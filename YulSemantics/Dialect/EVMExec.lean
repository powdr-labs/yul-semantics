import YulSemantics.Dialect
import YulSemantics.Dialect.EVMOp

/-!
# YulSemantics.Dialect.EVM

A gas-free reference instance of the EVM dialect, with `Value := BitVec 256` (see `DESIGN.md` §4).

Built-ins are a finite enum `Op`, covering the **full user-facing Yul EVM dialect**
(through the Fusaka fork, incl. `clz` (EIP-7939), `mcopy`, `blobhash`, `blobbasefee`).
`stepOp`/`effects` dispatch structurally on the constructor — fast to reduce and clean to prove
about. The string↔`Op` correspondence (`opName`, `parse`) is confined to the frontend.

## Modeling status

* **Fully modeled** (deterministic, local): arithmetic/comparison/bitwise/shifts/`clz`, `pop`,
  `keccak256` (via `ExecEnv.keccakOf`, whose default is the deterministic but unspecified
  `keccakBytes`), memory (`mload`/`mstore`/`mstore8`/`mcopy`/`msize`, including the
  active-memory high-water mark), storage and transient storage, calldata/code/returndata reads and
  copies, the execution-environment readers
  (`address` … `blobbasefee`, `selfbalance`), world-state reads via abstract environment maps
  (`balance`, `extcodesize`/`extcodecopy`/`extcodehash`, `blockhash`, `blobhash`), `log0`–`log4`,
  the object-data ops (`dataoffset`/`datasize`/`datacopy`, layout-abstracted — see below and
  `YulSemantics.Object`), and the halting ops (`stop`/`return`/`revert`/`invalid`).
* **Open-world modeled**: `call`/`callcode`/`delegatecall`/`staticcall` and `create`/`create2` are
  interpreted by `evmWithExternal calls creates gasOracle`. The supplied relations describe completed
  external executions and may include arbitrary nested calls, creations, and re-entrant callbacks.
  The call-only `evmWithCalls` API remains available. The original executable `evm` keeps these
  operations stuck because an open-world relation has no canonical evaluator.
* **Fully modeled (terminal world update)**: `selfdestruct` transfers the executing account's
  balance, records the destruction scheduled for transaction finalization, and halts. The
  environment's `createdThisTx` bit selects the post-Cancun self-beneficiary behavior.
* **Open-world modeled (environment oracle)**: `gas` is **deliberately** not a function of our
  state (`DESIGN.md`). In `evmWithExternal calls creates gasOracle` it returns a word permitted by
  the supplied `ExternalGas` oracle and leaves the state unchanged. `ExternalGas.any` is the
  historical unconstrained read (and what `evmWithCalls` installs); a narrower oracle lets a client
  couple `gas()` to a concrete machine's remaining gas, which is what makes a compiler forward
  simulation to the target `GAS` instruction possible at all. It must not be given a deterministic
  `stepOp` (that would license CSE), so it remains stuck in the executable reference dialect `evm`
  (`stepOp .gas = none`), which has no oracle to consult.
* **Deliberately absent from `Op`**:
  - stack/control opcodes (`DUP*`, `SWAP*`, incl. EIP-663 `DUPN`/`SWAPN`, `PUSH*`, `POP`-as-stack-op,
    `JUMP*`, `PC`) — Yul has no stack; these are bytecode-level and belong to the EVM repo and the
    compiler backend;
  - `pc()` (disallowed in modern Yul) and `difficulty()` (pre-Paris alias of `prevrandao`);
  - solc extensions (`verbatim*`, `memoryguard`, `linkersymbol`, `setimmutable`/`loadimmutable`).

## Object data (`dataoffset`/`datasize`/`datacopy`)

`datacopy(t, f, l)` copies `l` bytes from the code region to memory — semantically `codecopy`
(deployed bytecode carries data segments appended to the code). `dataoffset(name)`/`datasize(name)`
return the byte offset/size of a named data segment or sub-object in that bytecode. These are
**layout-dependent** — a sub-object's size is the length of *its compiled bytecode*, and offsets
are chosen at assembly time — so they are read from the `ExecEnv.dataOffset`/`dataSize` maps, which
the compiler supplies consistently with the object (`YulSemantics.Object`). Modeling caveat: a name
is keyed by its string-literal encoding `litValue (.string name)`; this is injective for the short
identifiers Yul object/data names actually are (≤ 31 bytes, distinct), and aliases otherwise.

Spec abstractions (documented): `blockhash`'s 256-block window and `blobhash`'s index bound are
abstracted into the environment maps. Gas is not modeled anywhere (`DESIGN.md` §1).
-/

namespace YulSemantics.EVM

open YulSemantics

/-- Keccak-256 as a deterministic but *unspecified* function (Lean `opaque`). It is the default
for `ExecEnv.keccakOf`; executable clients can supply a concrete implementation instead. -/
opaque keccakBytes : List UInt8 → U256

-- `U256`, `Op`, and `HaltKind` are the Mathlib-free frontend; they now live in
-- `YulSemantics.Dialect.EVMOp` and are re-used here via the import above.

/-- One emitted log record, including the emitting account. Keeping the
address explicit is necessary for logs produced by arbitrary callees or init
code, whose address need not be the current frame's address. -/
structure LogEntry where
  /-- The low-160-bit account address that emitted the record, represented as a word. -/
  address : U256
  /-- The indexed topics (`0`–`4` words, from `log0`…`log4`). -/
  topics : List U256
  /-- The logged memory slice. -/
  data   : List UInt8
  deriving Repr, DecidableEq, Inhabited

-- The `prec` argument of the auto-derived pretty-printer is genuinely unused for this plain record.
attribute [nolint unusedArguments] instReprLogEntry.repr

/-- The (immutable) execution environment: transaction/block context, input data, and abstract
read-only views of the world state. Addresses are represented as words. -/
structure ExecEnv where
  /-- The executing account's address (`address`). -/
  address       : U256 := 0
  /-- The transaction sender (`origin`). -/
  origin        : U256 := 0
  /-- The immediate caller (`caller`). -/
  caller        : U256 := 0
  /-- The wei sent with this call (`callvalue`). -/
  callvalue     : U256 := 0
  /-- The gas price of the transaction (`gasprice`). -/
  gasprice      : U256 := 0
  /-- The executing account's own balance (`selfbalance`). -/
  selfBalance   : U256 := 0
  /-- Whether the executing account was created in the current transaction. Post-Cancun this
  controls whether `selfdestruct(address())` burns its balance and whether transaction finalization
  deletes it. The frame-level semantics records the scheduled destruction but leaves deletion to
  a transaction semantics. -/
  createdThisTx : Bool := false
  /-- Whether this frame executes under a `STATICCALL` context. When set, every state-modifying
  built-in (`sstore`/`tstore`/`log0`–`log4`/`selfdestruct`, `create`/`create2`, and `call` with
  nonzero value) halts exceptionally instead of taking effect, matching the EVM's static-call
  write protection. `callcode` is *not* restricted (its value transfer is a self no-op), nor are
  `delegatecall`/`staticcall`; memory operations remain permitted. -/
  static        : Bool := false
  /-- The current block's beneficiary address (`coinbase`). -/
  coinbase      : U256 := 0
  /-- The current block's timestamp (`timestamp`). -/
  timestamp     : U256 := 0
  /-- The current block number (`number`). -/
  number        : U256 := 0
  /-- The current block's randomness beacon (`prevrandao`). -/
  prevrandao    : U256 := 0
  /-- The current block's gas limit (`gaslimit`). -/
  gaslimit      : U256 := 0
  /-- The chain identifier (`chainid`). -/
  chainid       : U256 := 0
  /-- The current block's base fee (`basefee`). -/
  basefee       : U256 := 0
  /-- The current block's blob base fee (`blobbasefee`). -/
  blobbasefee   : U256 := 0
  /-- The call's input data (`calldata*`). -/
  calldata      : List UInt8 := []
  /-- The executing account's own code (`codesize`/`codecopy`). -/
  code          : List UInt8 := []
  /-- Hash oracle used by `keccak256`. The default is abstract; executable clients can install a
  concrete Keccak-256 implementation, while proofs can relate this oracle to another semantics. -/
  keccakOf      : List UInt8 → U256 := keccakBytes
  /-- Balance lookup for any address (`balance`). -/
  balanceOf     : U256 → U256 := fun _ => 0
  /-- Code lookup for any address (`extcodesize`/`extcodecopy`). -/
  extCodeOf     : U256 → List UInt8 := fun _ => []
  /-- Code-hash lookup for any address (`extcodehash`). -/
  extCodeHashOf : U256 → U256 := fun _ => 0
  /-- Account nonce lookup for every address. Required to make CREATE address derivation and
  collision behavior stable across matching concrete worlds. -/
  nonceOf       : U256 → U256 := fun _ => 0
  /-- Persistent storage lookup for every account and key. -/
  storageOf     : U256 → U256 → U256 := fun _ _ => 0
  /-- Transient storage lookup for every account and key. -/
  transientOf   : U256 → U256 → U256 := fun _ _ => 0
  /-- Block-hash lookup by block number (`blockhash`). -/
  blockHashOf   : U256 → U256 := fun _ => 0
  /-- Blob-hash lookup by index (`blobhash`). -/
  blobHashOf    : U256 → U256 := fun _ => 0
  /-- Object-layout offset map for `dataoffset`, keyed by the *name's* string-literal encoding
  (`litValue (.string name)`); supplied by the compiler's layout (`YulSemantics.Object`). -/
  dataOffset    : U256 → U256 := fun _ => 0
  /-- Object-layout size map for `datasize`, keyed like `dataOffset`. -/
  dataSize      : U256 → U256 := fun _ => 0
  deriving Inhabited

/-- The (gas-free) EVM machine state.

* `memory` — byte-addressable, unbounded, default `0`.
* `activeWords` — the number of 32-byte words made active by memory-touching operations; this is
  separate from memory contents because even a zero read or write expands memory for `msize`.
* `storage` / `transient` — word-addressable maps, default `0`.
* `env` — frame context plus global world projections; local writes keep the current-account
  projections synchronized.
* `returndata` — the return-data buffer (written by open-world calls and creations).
* `logs` — emitted log records, in order.
* `selfdestructs` — accounts that executed `selfdestruct`, each paired with its `createdThisTx`
  bit, in order (see the field docstring).
* `halted` — set once a halting built-in fires: its kind and the return/revert data. -/
structure EvmState where
  /-- Byte-addressable memory, unbounded, default `0`. -/
  memory     : Nat → UInt8
  /-- Number of active 32-byte memory words, as observed by `msize`. -/
  activeWords : U256
  /-- Word-addressable persistent storage, default `0`. -/
  storage    : U256 → U256
  /-- Word-addressable transient storage (`tload`/`tstore`), default `0`. -/
  transient  : U256 → U256
  /-- Frame context and global world projections. -/
  env        : ExecEnv
  /-- The return-data buffer (written by external calls). -/
  returndata : List UInt8
  /-- Emitted log records, in order. -/
  logs       : List LogEntry
  /-- Accounts that have executed `selfdestruct`, in execution order. Each entry pairs the account
  address with its `createdThisTx` bit at destruction time: post-EIP-6780 (Cancun) the account is
  actually deleted at transaction finalization only when that bit is `true` (created in this
  transaction); when it is `false` the `selfdestruct` performed a balance transfer only and leaves
  the account in place. Recording the bit keeps the schedule lossless for a transaction semantics. -/
  selfdestructs : List (U256 × Bool)
  /-- Set once a halting built-in fires: its kind and the return/revert data. -/
  halted     : Option (HaltKind × List UInt8)

/-- The initial machine state: zeroed memory/storage, default environment, not halted. -/
def EvmState.init : EvmState :=
  { memory := fun _ => 0, activeWords := 0, storage := fun _ => 0, transient := fun _ => 0,
    env := default, returndata := [], logs := [], selfdestructs := [], halted := none }

/-! ### Frame-boundary commit vs. rollback

`stepOp` records only *which* halt fired (its `HaltKind` and exposed data) in `st.halted`; it does
**not** itself undo the storage/transient/log/balance/selfdestruct effects a frame accumulated
before halting. That is correct for a *sub-frame*, whose consequences are resolved by `finishCall`
on return, but the top-level frame's effects are only resolved at the **observation** boundary,
here.

Real EVM keeps a frame's committed world changes only when it halts *normally* — `stop`/`return` (or
runs off the end) — or via `selfdestruct`. A `revert`, an `invalid` (exceptional halt), or the
out-of-bounds `returndatacopy` (`invalidMemoryAccess`) discards **all** of the frame's changes;
only the exposed return/revert data survives. `HaltKind.commits`/`committedState` below apply this
rollback at the boundary, keeping the `Step` judgment (which is shared with sub-frames) untouched. -/

/-- Whether a halt *commits* the frame's accumulated world changes (`stop`/`return`/`selfdestruct`),
as opposed to discarding them (`revert`/`invalid`/`invalidMemoryAccess`). -/
def HaltKind.commits : HaltKind → Bool
  | .stop | .ret | .selfdestruct => true
  | .revert | .invalid | .invalidMemoryAccess | .staticViolation => false

/-- The frame's *observable* state at its boundary, given its initial state `st0` and its final
`Step` state `st'`.

* Not halted, or halted with a committing kind (`stop`/`return`/`selfdestruct`): the frame commits,
  so the observation is `st'` unchanged.
* Halted with a non-committing kind (`revert`/`invalid`/`invalidMemoryAccess`): every accumulated
  effect is rolled back to `st0`, carrying over only the outcome marker (`halted`) and the exposed
  return data (`returndata`) — exactly what real EVM leaves visible to the caller/transaction. -/
def committedState (st0 st' : EvmState) : EvmState :=
  match st'.halted with
  | none => st'
  | some (k, _) =>
      if k.commits then st'
      else { st0 with halted := st'.halted, returndata := st'.returndata }

/-! ### Helpers -/

-- `b2w` moved to `YulSemantics.Dialect.EVMOp`.

/-- Point-update of a word-addressable map. -/
@[inline] def upd (f : U256 → U256) (k v : U256) : U256 → U256 :=
  fun x => if x = k then v else f x

/-- The 160-bit EVM account key represented by a Yul word. -/
@[inline] def accountKey (address : U256) : Nat := address.toNat % (2 ^ 160)

/-- Point-update of an account-indexed word map. Account equality uses the EVM's low-160-bit
address truncation, so all 256-bit aliases remain coherent with a concrete account map. -/
@[inline] def updAccount (f : U256 → U256 → U256) (address key value : U256) :
    U256 → U256 → U256 :=
  fun a k => if accountKey a = accountKey address then
    if k = key then value else f a k
  else f a k

/-- Point-update of an account-indexed scalar map, respecting low-160-bit address aliases. -/
@[inline] def updAccountValue (f : U256 → U256) (address value : U256) : U256 → U256 :=
  fun a => if accountKey a = accountKey address then value else f a

/-- Runtime `EXTCODEHASH` for an account projection. EIP-161-empty accounts return zero; every
other account returns the configured Keccak hash of its code, including the empty-code hash for a
funded EOA. This helper keeps `extCodeHashOf` coherent when a balance transfer crosses emptiness. -/
def projectedCodeHash (env : ExecEnv) (balanceOf : U256 → U256) (address : U256) : U256 :=
  if (env.nonceOf address).toNat = 0 ∧ (balanceOf address).toNat = 0 ∧
      (env.extCodeOf address).length = 0 then 0
  else env.keccakOf (env.extCodeOf address)

/-- Intended world-consistency invariants for an execution environment. These are *not* enforced by
the state type (the fields are independent maps), but a concrete world always satisfies them, so
`WF` is provided as an optional hypothesis for downstream proofs.

* `extCodeHashOf` agrees with the derived `projectedCodeHash` rule (empty account ⇒ `0`; otherwise
  the Keccak hash of the account's code). This is the invariant the `extcodehash` opcode now reads
  through directly, so it rules out worlds the EVM never has (a code-hash decoupled from the code,
  nonce, and balance).
* `selfBalance` is the balance the global map assigns to the executing account. -/
def ExecEnv.WF (env : ExecEnv) : Prop :=
  (∀ a, env.extCodeHashOf a = projectedCodeHash env env.balanceOf a) ∧
    env.selfBalance = env.balanceOf env.address

/-- The `k`-th least-significant byte of a word. -/
@[inline] def byteAt (v : U256) (k : Nat) : UInt8 := UInt8.ofNat (v >>> (8 * k)).toNat

/-- The `i`-th byte of a byte list, zero-padded past the end. -/
@[inline] def byteFrom (data : List UInt8) (i : Nat) : UInt8 := data.getD i 0

/-- Load a big-endian 32-byte word from `memory` starting at byte address `p`. -/
def loadWord (mem : Nat → UInt8) (p : Nat) : U256 :=
  (List.range 32).foldl (fun acc i => (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 (mem (p + i)).toNat) 0

/-- Load a big-endian 32-byte word from a byte list starting at `p`, zero-padded (`calldataload`). -/
def wordFrom (data : List UInt8) (p : Nat) : U256 :=
  (List.range 32).foldl
    (fun acc i => (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 (byteFrom data (p + i)).toNat) 0

/-- Store `v` big-endian across the 32 bytes `p .. p+31` of `memory`. -/
def storeWord (mem : Nat → UInt8) (p : Nat) (v : U256) : Nat → UInt8 :=
  fun a => if p ≤ a ∧ a < p + 32 then byteAt v (31 - (a - p)) else mem a

/-- Store the least-significant byte of `v` at byte address `p` (`mstore8`). -/
def storeByte (mem : Nat → UInt8) (p : Nat) (v : U256) : Nat → UInt8 :=
  fun a => if a = p then byteAt v 0 else mem a

/-- Read `n` bytes of `memory` starting at byte address `p`. -/
def readBytes (mem : Nat → UInt8) (p n : Nat) : List UInt8 :=
  (List.range n).map (fun i => mem (p + i))

/-- Write `data[src .. src+n)` (zero-padded) into memory at `dst` (`calldatacopy` family). -/
def copyInto (mem : Nat → UInt8) (dst src n : Nat) (data : List UInt8) : Nat → UInt8 :=
  fun a => if dst ≤ a ∧ a < dst + n then byteFrom data (src + (a - dst)) else mem a

/-- Memory-to-memory copy, as if via an intermediate buffer (`MCOPY`, EIP-5656). -/
def copyWithin (mem : Nat → UInt8) (dst src n : Nat) : Nat → UInt8 :=
  fun a => if dst ≤ a ∧ a < dst + n then mem (src + (a - dst)) else mem a

/-- Active-word count after touching the byte range `[offset, offset + size)`. A zero-length range
does not expand memory, irrespective of its offset. -/
def activeWordsAfter (curr offset size : Nat) : Nat :=
  if size = 0 then curr else Nat.max curr ((offset + size - 1) / 32 + 1)

/-- Update the active-memory high-water mark after touching one byte range. -/
def touchMemory (st : EvmState) (offset size : Nat) : EvmState :=
  { st with activeWords := BitVec.ofNat 256 (activeWordsAfter st.activeWords.toNat offset size) }

/-- Update the active-memory high-water mark after touching two ranges (`mcopy` reads its source
as well as writing its destination). -/
def touchMemory2 (st : EvmState) (offset₁ size₁ offset₂ size₂ : Nat) : EvmState :=
  touchMemory (touchMemory st offset₁ size₁) offset₂ size₂

/-- The byte size of active memory, rounded to a multiple of 32 as required by `msize`. -/
def memorySize (st : EvmState) : U256 := BitVec.ofNat 256 (32 * st.activeWords.toNat)

/-- EIP-7939 `CLZ`: the number of leading zero bits (`256` for the zero word). -/
def clzVal (a : U256) : U256 :=
  if a = 0 then 256 else BitVec.ofNat 256 (255 - a.toNat.log2)

/-- Append a log record with the given topics and the memory slice `[p, p+n)`. -/
def appendLog (st : EvmState) (topics : List U256) (p n : U256) : EvmState :=
  { touchMemory st p.toNat n.toNat with
    logs := st.logs ++ [⟨st.env.address, topics, readBytes st.memory p.toNat n.toNat⟩] }

/-- Apply the immediate frame-level effects of post-Cancun `SELFDESTRUCT`.

The executing account is always recorded for transaction-finalization processing and the frame
halts successfully. Sending to another account transfers the full balance and zeroes the sender.
Sending to self preserves a pre-existing account's balance, but burns the balance of an account
created in this transaction; final deletion of the latter remains a transaction-level operation.
All account comparisons use the EVM's low 160 address bits. -/
def finishSelfdestruct (st : EvmState) (beneficiary : U256) : EvmState :=
  let self := st.env.address
  let sameAccount := accountKey beneficiary = accountKey self
  let balances :=
    if sameAccount then
      if st.env.createdThisTx then updAccountValue st.env.balanceOf self 0
      else st.env.balanceOf
    else
      updAccountValue
        (updAccountValue st.env.balanceOf self 0)
        beneficiary (st.env.balanceOf beneficiary + st.env.selfBalance)
  let selfBalance :=
    if sameAccount then
      if st.env.createdThisTx then 0 else st.env.selfBalance
    else 0
  let codeHashes := projectedCodeHash st.env balances
  { st with
    env := { st.env with
      balanceOf := balances
      extCodeHashOf := codeHashes
      selfBalance }
    selfdestructs := st.selfdestructs ++ [(self, st.env.createdThisTx)]
    halted := some (.selfdestruct, []) }

/-! ### Open-world external calls -/

/-- The four EVM call-family operations. -/
inductive CallKind
  | call | callcode | delegatecall | staticcall
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Everything the callee can observe at a call boundary. Caller memory is represented by the
already-copied `input`; output-memory placement remains a caller-local operation. The pre-call
`EvmState` is supplied separately to `ExternalCalls.Call`, giving the environment access to the
calling context and current world view. -/
structure CallRequest where
  /-- Which call-family instruction was used. -/
  kind   : CallKind
  /-- The caller's requested gas allowance. Gas accounting is delegated to the external model. -/
  gas    : U256
  /-- The address whose code is invoked. -/
  target : U256
  /-- The call value, or inherited/zero value for `delegatecall`/`staticcall`. -/
  value  : U256
  /-- A copy of the selected caller-memory input slice. -/
  input  : List UInt8

/-- The mutable, caller-observable world projection an external execution may change. It contains
global nonce and storage views so arbitrary callees and init code are fully pinned by a matching
concrete world. The separate current-account storage fields keep local built-ins simple.
`logs` and `selfdestructs` contain only newly emitted/scheduled records and are appended to the
caller's existing transaction-substate sequences. -/
structure CallWorld where
  /-- Balance of the executing account after the external execution. -/
  selfBalance   : U256
  /-- Post-execution balance view for every address. -/
  balanceOf     : U256 → U256
  /-- Post-execution code view for every address. -/
  extCodeOf     : U256 → List UInt8
  /-- Post-execution code-hash view for every address. -/
  extCodeHashOf : U256 → U256
  /-- Post-execution nonce view for every address. -/
  nonceOf       : U256 → U256
  /-- Post-execution persistent storage view for every address and key. -/
  storageOf     : U256 → U256 → U256
  /-- Post-execution transient storage view for every address and key. -/
  transientOf   : U256 → U256 → U256
  /-- Post-execution storage of the executing account, including re-entrant changes. -/
  storage       : U256 → U256
  /-- Post-execution transient storage of the executing account. -/
  transient     : U256 → U256
  /-- Log records emitted by the external execution, in order. -/
  logs          : List LogEntry
  /-- Destructions scheduled by the external execution, in order. Each pairs the destroyed account
  with its `createdThisTx` bit (see `EvmState.selfdestructs`). -/
  selfdestructs : List (U256 × Bool)

/-- The caller-visible result of a completed external execution. A false `success` represents
revert, exceptional failure, depth failure, or another EVM call failure. `returndata` is preserved
even on failure (and is empty for failures that expose no data). -/
structure CallResponse where
  /-- Whether the call completed successfully. -/
  success    : Bool
  /-- The complete return-data buffer exposed to the caller. -/
  returndata : List UInt8
  /-- The tentative post-world, committed only by successful non-static calls. -/
  world      : CallWorld

/-- Open-world interpretation of external calls. The relation may depend on the entire pre-call
state and may admit multiple responses. In particular, a response's post-world may include effects
of arbitrary nested calls and re-entrant executions of the caller. -/
structure ExternalCalls where
  /-- Relates a request and pre-call state to any permitted completed response. -/
  Call : CallRequest → EvmState → CallResponse → Prop

namespace ExternalCalls

/-- No external execution is available. This recovers the current local EVM reference dialect,
where call-family built-ins are stuck. -/
def none : ExternalCalls where Call := fun _ _ _ => False

/-- The maximally open environment: every response is possible. Useful for may-semantics; compiler
forward simulation uses a narrower relation coupled to the target EVM execution. -/
def any : ExternalCalls where Call := fun _ _ _ => True

end ExternalCalls

/-! ### Open-world contract creation -/

/-- The two EVM contract-creation operations. -/
inductive CreateKind
  | create | create2
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Everything init code can observe at a creation boundary. The pre-create `EvmState` is supplied
separately to `ExternalCreates.Create`; `initCode` is the already-copied caller-memory slice. -/
structure CreateRequest where
  /-- Whether the opcode derives its address from the creator nonce or a salt. -/
  kind     : CreateKind
  /-- Wei transferred to the account under construction. -/
  value    : U256
  /-- The exact init-code bytes copied from caller memory. -/
  initCode : List UInt8
  /-- `none` for CREATE and `some salt` for CREATE2. -/
  salt     : Option U256

/-- The caller-visible result of a completed creation attempt. `some address` means deployment
succeeded (including the mathematically possible address word `0`); `none` means the opcode pushes
zero. `world` describes the successful post-world in full; on failure (`created = none`) only the
creator nonce bump survives (`world.nonceOf`), while all other components of `world` are discarded
by `finishCreate`, which rolls back to the pre-state. This mirrors real EVM: a failed create
(collision, init-code revert, or deployment failure) reverts every state change except the
creator's nonce (and gas). -/
structure CreateResponse where
  /-- The deployed address on success, or `none` when the opcode returns zero. -/
  created    : Option U256
  /-- Revert data on failure. Successful creation exposes an empty return-data buffer. -/
  returndata : List UInt8
  /-- The successful post-world in full; on failure only its `nonceOf` (the creator nonce bump) is
  committed by `finishCreate`. -/
  world      : CallWorld

/-- Open-world interpretation of contract creation. The relation may summarize arbitrary init-code
execution, including nested calls/creates and re-entrant execution of the creator. -/
structure ExternalCreates where
  /-- Relates a creation request and pre-state to any permitted completed response. -/
  Create : CreateRequest → EvmState → CreateResponse → Prop

namespace ExternalCreates

/-- No contract creation is available. -/
def none : ExternalCreates where Create := fun _ _ _ => False

/-- Every completed creation response is permitted. -/
def any : ExternalCreates where Create := fun _ _ _ => True

end ExternalCreates

/-- Open-world interpretation of the `gas()` oracle: which remaining-gas words the surrounding
execution environment may report in a given state.

Remaining gas is not a function of the state this semantics tracks — the source language
deliberately has no gas accounting (`DESIGN.md` §1) — so, exactly like `ExternalCalls` and
`ExternalCreates`, the environment supplies the permitted answers. Keeping it a *parameter* rather
than hard-coding "any word" is what lets a client couple the oracle to a concrete machine: a
compiler forward-simulation proof, for instance, can only realize `gas()` with a target `GAS`
instruction when the source oracle is the one that reports exactly that machine's remaining gas.
`ExternalGas.any` recovers the historical unconstrained read. -/
structure ExternalGas where
  /-- Relates a pre-state to any remaining-gas word `gas()` may report there. -/
  Gas : EvmState → U256 → Prop

namespace ExternalGas

/-- The maximally open oracle: `gas()` may report any word. This is the historical behavior and the
right choice for may-semantics; it admits no forward-simulation realization. -/
def any : ExternalGas where Gas := fun _ _ => True

/-- No remaining-gas answer is available, so `gas()` is stuck. The counterpart of
`ExternalCalls.none`/`ExternalCreates.none` for a fully closed world. -/
def none : ExternalGas where Gas := fun _ _ => False

/-- The deterministic oracle that reports exactly `f st`. -/
def ofFun (f : EvmState → U256) : ExternalGas where Gas := fun st g => g = f st

end ExternalGas

/-- Install the mutable world projection produced by a successful external call. Immutable frame
context (address/caller/calldata/block fields), caller memory, returndata, and halt status are
preserved here and handled separately by `finishCall`. -/
def CallWorld.install (world : CallWorld) (st : EvmState) : EvmState :=
  { st with
    storage := world.storage
    transient := world.transient
    logs := st.logs ++ world.logs
    selfdestructs := st.selfdestructs ++ world.selfdestructs
    env := { st.env with
      selfBalance := world.selfBalance
      balanceOf := world.balanceOf
      extCodeOf := world.extCodeOf
      extCodeHashOf := world.extCodeHashOf
      nonceOf := world.nonceOf
      storageOf := world.storageOf
      transientOf := world.transientOf } }

/-- The current mutable world projection, useful when an external execution leaves it unchanged. -/
def CallWorld.ofState (st : EvmState) : CallWorld :=
  { selfBalance := st.env.selfBalance
    balanceOf := st.env.balanceOf
    extCodeOf := st.env.extCodeOf
    extCodeHashOf := st.env.extCodeHashOf
    nonceOf := st.env.nonceOf
    storageOf := st.env.storageOf
    transientOf := st.env.transientOf
    storage := st.storage
    transient := st.transient
    logs := []
    selfdestructs := [] }

/-- Copy the available prefix of return data into the caller's output area, leaving the remainder
of that area and all other caller memory unchanged. -/
def copyReturn (memory : Nat → UInt8) (dst size : Nat) (data : List UInt8) : Nat → UInt8 :=
  fun address =>
    if dst ≤ address ∧ address < dst + min size data.length then
      byteFrom data (address - dst)
    else memory address

/-- Complete a call after the external relation supplies its response. Memory expansion and return
copying are always caller-local. Failed calls roll back the world projection; `staticcall` preserves
it even on success. Successful non-static calls install the response world, which may contain
arbitrary re-entrant changes. -/
def finishCall (kind : CallKind) (st : EvmState) (response : CallResponse)
    (inputOffset inputSize outputOffset outputSize : Nat) : EvmState :=
  let touched := touchMemory2 st inputOffset inputSize outputOffset outputSize
  let postWorld :=
    if response.success = true ∧ kind ≠ .staticcall then response.world.install touched else touched
  { postWorld with
    memory := copyReturn st.memory outputOffset outputSize response.returndata
    returndata := response.returndata }

/-- EVM word returned by the call-family built-ins. -/
def CallResponse.flag (response : CallResponse) : U256 := if response.success then 1 else 0

/-- The word pushed by CREATE/CREATE2. -/
def CreateResponse.result (response : CreateResponse) : U256 := response.created.getD 0

/-- CREATE exposes revert bytes on failure and clears returndata on success. -/
def CreateResponse.visibleReturnData (response : CreateResponse) : List UInt8 :=
  if response.created.isSome then [] else response.returndata

/-- Complete a creation attempt after the external relation supplies its response. Reading init
code expands caller memory. On success (`created.isSome`) the full response world is installed. On
failure (`created = none`) the creation is rolled back structurally: the pre-state's storage,
transient storage, balances, logs, and every other component are preserved, and only the creator
nonce bump (`response.world.nonceOf`) is committed. This makes the failed-create rollback provable
(`finishCreate_failure_storage`) rather than relying on the external relation to reconstruct the
pre-state in `response.world`. -/
def finishCreate (st : EvmState) (response : CreateResponse) (offset size : Nat) : EvmState :=
  let touched := touchMemory st offset size
  let committed :=
    if response.created.isSome then response.world.install touched
    else { touched with env := { touched.env with nonceOf := response.world.nonceOf } }
  { committed with returndata := response.visibleReturnData }

-- `litValue` and `litWF` moved to `YulSemantics.Dialect.EVMOp`.

/-! ### Built-in semantics (structural dispatch on `Op`)

Dispatch is `op`-first (a structural `Op` case), then a small per-arity argument match via the
helpers below. This keeps every arm tiny, so reducing `stepOp op args st` on a concrete `op` is
cheap — `simp [stepOp, un, bin, ter, …]` closes goals without recursion-depth/heartbeat
gymnastics. -/

/-- Lift a unary value function to a built-in result (returns `none` on arity mismatch). -/
@[inline] def un (f : U256 → U256) : List U256 → EvmState → Option (BuiltinResult U256 EvmState)
  | [a], st => some (.ok [f a] st)
  | _,   _  => none

/-- Lift a binary value function to a built-in result. -/
@[inline] def bin (f : U256 → U256 → U256) : List U256 → EvmState → Option (BuiltinResult U256 EvmState)
  | [a, b], st => some (.ok [f a b] st)
  | _,      _  => none

/-- Lift a ternary value function to a built-in result. -/
@[inline] def ter (f : U256 → U256 → U256 → U256) : List U256 → EvmState → Option (BuiltinResult U256 EvmState)
  | [a, b, c], st => some (.ok [f a b c] st)
  | _,         _  => none

/-- A nullary state read. -/
@[inline] def rd0 (v : U256) : List U256 → EvmState → Option (BuiltinResult U256 EvmState)
  | [], st => some (.ok [v] st)
  | _,  _  => none

/-- A unary state read. -/
@[inline] def rd1 (f : U256 → U256) : List U256 → EvmState → Option (BuiltinResult U256 EvmState)
  | [a], st => some (.ok [f a] st)
  | _,   _  => none

/-- Two's-complement sign-extension of `x` from byte `i` (EVM `signextend`). -/
def signExtend (i x : U256) : U256 :=
  let k := i.toNat
  if 31 ≤ k then x
  else
    let bits := 8 * (k + 1)
    let low : U256 := (1 <<< bits) - 1
    if x.getLsbD (bits - 1) then x ||| (~~~low) else x &&& low

/-- Guard a state-modifying local built-in by the static-call context. In a static frame
(`st.env.static = true`) the operation halts exceptionally with `.staticViolation`, matching the
EVM's write protection (`StaticModeViolation`); otherwise it produces `act`. Used for
`sstore`/`tstore`/`log0`–`log4`/`selfdestruct`. -/
@[inline] def guardStatic (st : EvmState) (act : BuiltinResult U256 EvmState) :
    Option (BuiltinResult U256 EvmState) :=
  some (if st.env.static then .halt { st with halted := some (.staticViolation, []) } else act)

/-- The executable built-in step function. Returns `none` on an arity mismatch or an unmodeled
built-in. Call- and create-family operations are deliberately absent from this function; use the
relational `builtinWithExternal`/`evmWithExternal` interpretation for them. -/
def stepOp (op : Op) (args : List U256) (st : EvmState) : Option (BuiltinResult U256 EvmState) :=
  match op with
  -- arithmetic
  | .add        => bin (· + ·) args st
  | .sub        => bin (· - ·) args st
  | .mul        => bin (· * ·) args st
  | .div        => bin (fun a b => if b = 0 then 0 else a / b) args st
  | .sdiv       => bin (fun a b => if b = 0 then 0 else BitVec.sdiv a b) args st
  | .mod        => bin (fun a b => if b = 0 then 0 else a % b) args st
  | .smod       => bin (fun a b => if b = 0 then 0 else BitVec.srem a b) args st
  | .addmod     => ter (fun a b n => if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)) args st
  | .mulmod     => ter (fun a b n => if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)) args st
  | .exp        => bin (fun a b => BitVec.ofNat 256 (a.toNat ^ b.toNat)) args st
  | .signextend => bin signExtend args st
  | .clz        => un clzVal args st
  -- comparison
  | .lt         => bin (fun a b => b2w (a.ult b)) args st
  | .gt         => bin (fun a b => b2w (b.ult a)) args st
  | .slt        => bin (fun a b => b2w (a.slt b)) args st
  | .sgt        => bin (fun a b => b2w (b.slt a)) args st
  | .eq         => bin (fun a b => b2w (a = b)) args st
  | .iszero     => un  (fun a => b2w (a = 0)) args st
  -- bitwise / shifts
  | .and        => bin (· &&& ·) args st
  | .or         => bin (· ||| ·) args st
  | .xor        => bin (· ^^^ ·) args st
  | .not        => un  (~~~·) args st
  | .byte       => bin (fun i x => if 32 ≤ i.toNat then 0 else (x >>> (248 - 8 * i.toNat)) &&& 0xff) args st
  | .shl        => bin (fun shift val => val <<< shift.toNat) args st
  | .shr        => bin (fun shift val => val >>> shift.toNat) args st
  | .sar        => bin (fun shift val => BitVec.sshiftRight val shift.toNat) args st
  -- hashing / value discard
  | .keccak256  => match args with
      | [p, n] => some (.ok [st.env.keccakOf (readBytes st.memory p.toNat n.toNat)]
          (touchMemory st p.toNat n.toNat))
      | _ => none
  | .pop        => match args with | [_] => some (.ok [] st) | _ => none
  -- memory
  | .mload      => match args with
      | [p] => some (.ok [loadWord st.memory p.toNat] (touchMemory st p.toNat 32))
      | _ => none
  | .mstore     => match args with
      | [p, v] => some (.ok []
          { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v })
      | _ => none
  | .mstore8    => match args with
      | [p, v] => some (.ok []
          { touchMemory st p.toNat 1 with memory := storeByte st.memory p.toNat v })
      | _ => none
  | .mcopy      => match args with
      | [dst, src, n] =>
          some (.ok [] { touchMemory2 st dst.toNat n.toNat src.toNat n.toNat with
            memory := copyWithin st.memory dst.toNat src.toNat n.toNat })
      | _ => none
  | .msize      => rd0 (memorySize st) args st
  -- storage
  | .sload      => match args with | [k]    => some (.ok [st.storage k] st) | _ => none
  | .sstore     => match args with
      | [k, v] => guardStatic st (.ok [] { st with
          storage := upd st.storage k v
          env := { st.env with storageOf := updAccount st.env.storageOf st.env.address k v } })
      | _ => none
  | .tload      => match args with | [k]    => some (.ok [st.transient k] st) | _ => none
  | .tstore     => match args with
      | [k, v] => guardStatic st (.ok [] { st with
          transient := upd st.transient k v
          env := { st.env with transientOf := updAccount st.env.transientOf st.env.address k v } })
      | _ => none
  -- calldata / code / returndata
  | .calldataload   => rd1 (fun p => wordFrom st.env.calldata p.toNat) args st
  | .calldatasize   => rd0 (BitVec.ofNat 256 st.env.calldata.length) args st
  | .calldatacopy   => match args with
      | [dst, src, n] =>
          some (.ok [] { touchMemory st dst.toNat n.toNat with
            memory := copyInto st.memory dst.toNat src.toNat n.toNat st.env.calldata })
      | _ => none
  | .codesize       => rd0 (BitVec.ofNat 256 st.env.code.length) args st
  | .codecopy       => match args with
      | [dst, src, n] =>
          some (.ok [] { touchMemory st dst.toNat n.toNat with
            memory := copyInto st.memory dst.toNat src.toNat n.toNat st.env.code })
      | _ => none
  | .returndatasize => rd0 (BitVec.ofNat 256 st.returndata.length) args st
  | .returndatacopy => match args with
      | [dst, src, n] =>
          if src.toNat + n.toNat ≤ st.returndata.length then
            some (.ok [] { touchMemory st dst.toNat n.toNat with
              memory := copyInto st.memory dst.toNat src.toNat n.toNat st.returndata })
          else some (.halt { st with halted := some (.invalidMemoryAccess, []) })
      | _ => none
  -- object data: `dataoffset`/`datasize` read the layout maps (keyed by the name's string-literal
  -- encoding); `datacopy` copies from the code region, exactly like `codecopy`.
  | .datasize   => rd1 (fun k => st.env.dataSize k) args st
  | .dataoffset => rd1 (fun k => st.env.dataOffset k) args st
  | .datacopy   => match args with
      | [dst, off, n] =>
          some (.ok [] { touchMemory st dst.toNat n.toNat with
            memory := copyInto st.memory dst.toNat off.toNat n.toNat st.env.code })
      | _ => none
  -- execution environment
  | .address     => rd0 st.env.address args st
  | .origin      => rd0 st.env.origin args st
  | .caller      => rd0 st.env.caller args st
  | .callvalue   => rd0 st.env.callvalue args st
  | .gasprice    => rd0 st.env.gasprice args st
  | .selfbalance => rd0 st.env.selfBalance args st
  | .coinbase    => rd0 st.env.coinbase args st
  | .timestamp   => rd0 st.env.timestamp args st
  | .number      => rd0 st.env.number args st
  | .prevrandao  => rd0 st.env.prevrandao args st
  | .gaslimit    => rd0 st.env.gaslimit args st
  | .chainid     => rd0 st.env.chainid args st
  | .basefee     => rd0 st.env.basefee args st
  | .blobbasefee => rd0 st.env.blobbasefee args st
  -- world-state reads
  | .balance     => rd1 st.env.balanceOf args st
  | .extcodesize => rd1 (fun a => BitVec.ofNat 256 (st.env.extCodeOf a).length) args st
  | .extcodecopy => match args with
      | [a, dst, src, n] =>
          some (.ok [] { touchMemory st dst.toNat n.toNat with
            memory := copyInto st.memory dst.toNat src.toNat n.toNat (st.env.extCodeOf a) })
      | _ => none
  | .extcodehash => rd1 (fun a => projectedCodeHash st.env st.env.balanceOf a) args st
  | .blockhash   => rd1 st.env.blockHashOf args st
  | .blobhash    => rd1 st.env.blobHashOf args st
  -- logging
  | .log0 => match args with | [p, n]                 => guardStatic st (.ok [] (appendLog st [] p n)) | _ => none
  | .log1 => match args with | [p, n, t1]             => guardStatic st (.ok [] (appendLog st [t1] p n)) | _ => none
  | .log2 => match args with | [p, n, t1, t2]         => guardStatic st (.ok [] (appendLog st [t1, t2] p n)) | _ => none
  | .log3 => match args with | [p, n, t1, t2, t3]     => guardStatic st (.ok [] (appendLog st [t1, t2, t3] p n)) | _ => none
  | .log4 => match args with | [p, n, t1, t2, t3, t4] => guardStatic st (.ok [] (appendLog st [t1, t2, t3, t4] p n)) | _ => none
  -- external interaction: calls/creates are absent from the executable local evaluator
  | .gas | .call | .callcode | .delegatecall | .staticcall
  | .create | .create2 => none
  -- terminal world update
  | .selfdestruct => match args with
      | [beneficiary] => guardStatic st (.halt (finishSelfdestruct st beneficiary))
      | _ => none
  -- halting
  | .stop       => match args with | []     => some (.halt { st with halted := some (.stop, []) }) | _ => none
  | .ret        => match args with
      | [p, s] => some (.halt { touchMemory st p.toNat s.toNat with
          halted := some (.ret, readBytes st.memory p.toNat s.toNat) })
      | _ => none
  | .revert     => match args with
      | [p, s] => some (.halt { touchMemory st p.toNat s.toNat with
          halted := some (.revert, readBytes st.memory p.toNat s.toNat) })
      | _ => none
  | .invalid    => match args with | []     => some (.halt { st with halted := some (.invalid, []) }) | _ => none

/-- Relational execution of one external call after its arguments have been checked. The external
environment chooses a response; `finishCall` fixes all caller-local consequences. -/
def externalCall (external : ExternalCalls) (kind : CallKind) (gas target value : U256)
    (inputOffset inputSize outputOffset outputSize : U256) (st : EvmState)
    (result : BuiltinResult U256 EvmState) : Prop :=
  ∃ response,
    external.Call
      { kind, gas, target, value,
        input := readBytes st.memory inputOffset.toNat inputSize.toNat }
      st response ∧
    result = .ok [response.flag]
      (finishCall kind st response inputOffset.toNat inputSize.toNat
        outputOffset.toNat outputSize.toNat)

/-- Relational execution of CREATE/CREATE2 after arity checking. The external relation executes the
copied init code; `finishCreate` fixes memory expansion, the returned word, returndata, and the
committed caller-observable world. -/
def externalCreate (external : ExternalCreates) (kind : CreateKind) (value offset size : U256)
    (salt : Option U256) (st : EvmState) (result : BuiltinResult U256 EvmState) : Prop :=
  ∃ response,
    external.Create
      { kind, value, initCode := readBytes st.memory offset.toNat size.toNat, salt }
      st response ∧
    result = .ok [response.result] (finishCreate st response offset.toNat size.toNat)

/-- Combined open-world built-in relation. Local operations retain the executable `stepOp` graph;
CALL-family and CREATE-family operations are interpreted by their respective relations, and `gas()`
by the environment's remaining-gas oracle. -/
def builtinWithExternal (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas)
    (op : Op) (args : List U256) (st : EvmState)
    (result : BuiltinResult U256 EvmState) : Prop :=
  match op with
  | .call => match args with
      | [gas, target, value, inputOffset, inputSize, outputOffset, outputSize] =>
          -- A value-bearing `call` is a state modification, forbidden in a static frame.
          if st.env.static ∧ value ≠ 0 then
            result = .halt { st with halted := some (.staticViolation, []) }
          else
            externalCall calls .call gas target value inputOffset inputSize outputOffset
              outputSize st result
      | _ => False
  | .callcode => match args with
      | [gas, target, value, inputOffset, inputSize, outputOffset, outputSize] =>
          -- Unlike `call`, a value-bearing `callcode` is NOT rejected in a static frame: the value
          -- is transferred from the executing account to itself (`callcode` runs the target's code
          -- in the current account's context), a no-op on world state. Matches EIP-214 / the EVM,
          -- which has no static-mode `callcode` gate.
          externalCall calls .callcode gas target value inputOffset inputSize outputOffset
            outputSize st result
      | _ => False
  | .delegatecall => match args with
      | [gas, target, inputOffset, inputSize, outputOffset, outputSize] =>
          externalCall calls .delegatecall gas target st.env.callvalue inputOffset inputSize
            outputOffset outputSize st result
      | _ => False
  | .staticcall => match args with
      | [gas, target, inputOffset, inputSize, outputOffset, outputSize] =>
          externalCall calls .staticcall gas target 0 inputOffset inputSize outputOffset
            outputSize st result
      | _ => False
  | .create => match args with
      | [value, offset, size] =>
          -- Contract creation is forbidden in a static frame.
          if st.env.static then result = .halt { st with halted := some (.staticViolation, []) }
          else externalCreate creates .create value offset size none st result
      | _ => False
  | .create2 => match args with
      | [value, offset, size, salt] =>
          if st.env.static then result = .halt { st with halted := some (.staticViolation, []) }
          else externalCreate creates .create2 value offset size (some salt) st result
      | _ => False
  -- `gas()` is an oracle read: it returns a remaining-gas word the environment permits and leaves
  -- the state unchanged. It is deliberately absent from the deterministic `stepOp` (which has no
  -- oracle), so it lives only in this open-world relation. With `ExternalGas.any` this is the
  -- historical unconstrained `∃ g`. See `DESIGN.md` §1.
  | .gas => match args with
      | []   => ∃ g : U256, gasOracle.Gas st g ∧ result = .ok [g] st
      | _    => False
  | _ => stepOp op args st = some result

/-- Backwards-compatible call-only built-in relation, with the unconstrained gas oracle. -/
def builtin (external : ExternalCalls) :
    Op → List U256 → EvmState → BuiltinResult U256 EvmState → Prop :=
  builtinWithExternal external ExternalCreates.none ExternalGas.any

-- `effects`, `opName`, `parse`, and `mkCall` moved to `YulSemantics.Dialect.EVMOp`.

/-- The gas-free EVM reference dialect.

Marked `@[reducible]` so that instance search (e.g. `DecidableEq evm.Value`) and defeq can see through
to the concrete `Value := BitVec 256` / `State := EvmState`. -/
@[reducible] def evm : Dialect where
  Op       := Op
  Value    := U256
  State    := EvmState
  litValue := litValue
  litWF    := litWF
  Builtin  := fun op args st r => stepOp op args st = some r
  effects  := effects

/-- The gas-free EVM reference dialect with open-world call and creation behavior. Unlike `evm`,
this dialect may be nondeterministic and therefore has no canonical executable interpreter. -/
@[reducible] def evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : Dialect where
  Op       := Op
  Value    := U256
  State    := EvmState
  litValue := litValue
  litWF    := litWF
  Builtin  := builtinWithExternal calls creates gasOracle
  effects  := effects

/-- Backwards-compatible call-only open-world dialect, with the unconstrained gas oracle. -/
@[reducible] def evmWithCalls (external : ExternalCalls) : Dialect :=
  evmWithExternal external ExternalCreates.none ExternalGas.any

/-- The EVM dialect as an `ExecDialect`: `Builtin` is defined from `stepOp`, so the executable
`builtinFn := stepOp` agrees with it by construction. `@[reducible]` for the same reason as `evm`. -/
@[reducible] def exec : ExecDialect := { toDialect := evm, builtinFn := stepOp }

/-! ### Smoke tests — structural dispatch reduces cleanly (no `maxRecDepth` gymnastics). -/

/-! Effect-classification guards for the distinctions most relevant to memory expansion and
control flow. The general semantic guarantee is `effects_sound` above. -/

/-! `SELFDESTRUCT` guards. These cover an ordinary transfer and both sides of the post-Cancun
self-beneficiary rule. -/

-- `selfdestructTestState` (a test-only helper) moved to `YulSemantics.Dialect.EVM`
-- alongside the examples that use it.

/-! Open-world call guards. The post-storage value stands for a callback into the caller: the
call-boundary semantics commits it exactly on successful, non-static execution. -/

/-! Open-world `gas()` oracle guards. In the open-world dialect `gas()` may return any word while
leaving the state unchanged; it remains stuck in the executable reference dialect. -/

/-! Open-world creation guards. -/

/-! Static-call write-protection guards. In a static frame the state-modifying built-ins halt
exceptionally with `.staticViolation`; the same ops write normally in an ordinary frame. -/

end YulSemantics.EVM
