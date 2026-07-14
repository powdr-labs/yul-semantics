import Mathlib
import YulSemantics.Dialect

/-!
# YulSemantics.Dialect.EVM

A gas-free reference instance of the EVM dialect, with `Value := BitVec 256` (see `DESIGN.md` §4).

Built-ins are a finite enum `Op` (Option D), covering the **full user-facing Yul EVM dialect**
(through the Fusaka fork, incl. `clz` (EIP-7939), `mcopy`, `blobhash`, `blobbasefee`).
`stepOp`/`effects` dispatch structurally on the constructor — fast to reduce and clean to prove
about. The string↔`Op` correspondence (`opName`, `parse`) is confined to the frontend.

## Modeling status

* **Fully modeled** (deterministic, local): arithmetic/comparison/bitwise/shifts/`clz`, `pop`,
  `keccak256` (via the *opaque* `keccakBytes` — a deterministic but unspecified function, which is
  all the meta-theory needs), memory (`mload`/`mstore`/`mstore8`/`mcopy`/`msize`, including the
  active-memory high-water mark), storage and transient storage, calldata/code/returndata reads and
  copies, the execution-environment readers
  (`address` … `blobbasefee`, `selfbalance`), world-state reads via abstract environment maps
  (`balance`, `extcodesize`/`extcodecopy`/`extcodehash`, `blockhash`, `blobhash`), `log0`–`log4`,
  the object-data ops (`dataoffset`/`datasize`/`datacopy`, layout-abstracted — see below and
  `YulSemantics.Object`), and the halting ops (`stop`/`return`/`revert`/`invalid`).
* **Enumerated but unmodeled** (`stepOp` returns `none`; the real semantics arrives by
  instantiating the `Dialect` with the external EVM):
  - `gas` — **deliberately** not a function of our state: it is nondeterministic by design
    (`DESIGN.md`), so it must not be given a deterministic `stepOp` (that would license CSE).
  - `call`/`callcode`/`delegatecall`/`staticcall`/`create`/`create2`/`selfdestruct` — external
    world interaction.
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

Spec deviations (documented): `returndatacopy` out-of-bounds is *stuck* rather than an exceptional
halt; `blockhash`'s 256-block window and `blobhash`'s index bound are abstracted into the
environment maps. Gas is not modeled anywhere (`DESIGN.md` §1).
-/

namespace YulSemantics.EVM

open YulSemantics

/-- The EVM word: a 256-bit machine value. -/
abbrev U256 := BitVec 256

/-- Keccak-256 as a deterministic but *unspecified* function (Lean `opaque`): the meta-theory only
needs determinism, never the concrete hash. Programs using `keccak256` cannot be run by
`native_decide`/`#eval`. -/
opaque keccakBytes : List UInt8 → U256

/-- The Yul EVM-dialect built-in operations (see the module docstring for coverage and deliberate
omissions). `ret` is `return` (a Lean keyword). -/
inductive Op
  -- arithmetic
  | add | sub | mul | div | sdiv | mod | smod | addmod | mulmod | exp | signextend | clz
  -- comparison
  | lt | gt | slt | sgt | eq | iszero
  -- bitwise / shifts
  | and | or | xor | not | byte | shl | shr | sar
  -- hashing / value discard
  | keccak256 | pop
  -- memory / storage / transient storage
  | mload | mstore | mstore8 | mcopy | msize | sload | sstore | tload | tstore
  -- calldata / code / returndata
  | calldataload | calldatasize | calldatacopy | codesize | codecopy
  | returndatasize | returndatacopy
  -- object data (layout-abstracted; see `YulSemantics.Object`)
  | datasize | dataoffset | datacopy
  -- execution environment
  | address | origin | caller | callvalue | gasprice | selfbalance
  | coinbase | timestamp | number | prevrandao | gaslimit | chainid | basefee | blobbasefee
  -- world-state reads
  | balance | extcodesize | extcodecopy | extcodehash | blockhash | blobhash
  -- logging
  | log0 | log1 | log2 | log3 | log4
  -- external interaction (enumerated, unmodeled here)
  | gas | call | callcode | delegatecall | staticcall | create | create2 | selfdestruct
  -- halting
  | stop | ret | revert | invalid
  deriving Repr, DecidableEq, Inhabited

/-- How a halting built-in terminated, stored in the machine state. -/
inductive HaltKind
  | stop | ret | revert | invalid
  deriving Repr, DecidableEq, Inhabited

/-- One emitted log record: topics plus a copy of the logged memory slice. -/
structure LogEntry where
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
  /-- Balance lookup for any address (`balance`). -/
  balanceOf     : U256 → U256 := fun _ => 0
  /-- Code lookup for any address (`extcodesize`/`extcodecopy`). -/
  extCodeOf     : U256 → List UInt8 := fun _ => []
  /-- Code-hash lookup for any address (`extcodehash`). -/
  extCodeHashOf : U256 → U256 := fun _ => 0
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
* `env` — the immutable execution environment.
* `returndata` — the return-data buffer (written by external calls, which are unmodeled here).
* `logs` — emitted log records, in order.
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
  /-- The immutable execution environment. -/
  env        : ExecEnv
  /-- The return-data buffer (written by external calls, which are unmodeled here). -/
  returndata : List UInt8
  /-- Emitted log records, in order. -/
  logs       : List LogEntry
  /-- Set once a halting built-in fires: its kind and the return/revert data. -/
  halted     : Option (HaltKind × List UInt8)

/-- The initial machine state: zeroed memory/storage, default environment, not halted. -/
def EvmState.init : EvmState :=
  { memory := fun _ => 0, activeWords := 0, storage := fun _ => 0, transient := fun _ => 0,
    env := default, returndata := [], logs := [], halted := none }

/-! ### Helpers -/

/-- `b2w c` is the EVM boolean encoding: `1` for `true`, `0` for `false`. -/
@[inline] def b2w (c : Bool) : U256 := if c then 1 else 0

/-- Point-update of a word-addressable map. -/
@[inline] def upd (f : U256 → U256) (k v : U256) : U256 → U256 :=
  fun x => if x = k then v else f x

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
    logs := st.logs ++ [⟨topics, readBytes st.memory p.toNat n.toNat⟩] }

/-! ### Literals -/

/-- Interpret a literal as a 256-bit word: numbers wrap mod `2^256` (well-formed numbers are
`< 2^256`); `true`/`false` → `1`/`0`; string literals → their UTF-8 bytes, left-aligned. -/
def litValue : Literal → U256
  | .number n => BitVec.ofNat 256 n
  | .bool b   => b2w b
  | .string s =>
      let bytes := s.toUTF8.toList.take 32
      let n := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
      BitVec.ofNat 256 (n <<< (8 * (32 - bytes.length)))

/-- Well-formed literals: numbers fit in 256 bits and string literals are at most 32 bytes. -/
def litWF : Literal → Prop
  | .number n => n < 2 ^ 256
  | .bool _   => True
  | .string s => s.toUTF8.size ≤ 32

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

/-- The built-in step function. Returns `none` on an arity mismatch or an unmodeled built-in (a
stuck call — see the module docstring for which ops are unmodeled and why). -/
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
      | [p, n] => some (.ok [keccakBytes (readBytes st.memory p.toNat n.toNat)]
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
  | .sstore     => match args with | [k, v] => some (.ok [] { st with storage := upd st.storage k v }) | _ => none
  | .tload      => match args with | [k]    => some (.ok [st.transient k] st) | _ => none
  | .tstore     => match args with | [k, v] => some (.ok [] { st with transient := upd st.transient k v }) | _ => none
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
          -- out-of-bounds returndata access is an exceptional halt in the EVM; modeled as stuck
          if src.toNat + n.toNat ≤ st.returndata.length then
            some (.ok [] { touchMemory st dst.toNat n.toNat with
              memory := copyInto st.memory dst.toNat src.toNat n.toNat st.returndata })
          else none
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
  | .extcodehash => rd1 st.env.extCodeHashOf args st
  | .blockhash   => rd1 st.env.blockHashOf args st
  | .blobhash    => rd1 st.env.blobHashOf args st
  -- logging
  | .log0 => match args with | [p, n]                 => some (.ok [] (appendLog st [] p n)) | _ => none
  | .log1 => match args with | [p, n, t1]             => some (.ok [] (appendLog st [t1] p n)) | _ => none
  | .log2 => match args with | [p, n, t1, t2]         => some (.ok [] (appendLog st [t1, t2] p n)) | _ => none
  | .log3 => match args with | [p, n, t1, t2, t3]     => some (.ok [] (appendLog st [t1, t2, t3] p n)) | _ => none
  | .log4 => match args with | [p, n, t1, t2, t3, t4] => some (.ok [] (appendLog st [t1, t2, t3, t4] p n)) | _ => none
  -- external interaction: unmodeled (supplied by instantiating with the full EVM semantics)
  | .gas | .call | .callcode | .delegatecall | .staticcall
  | .create | .create2 | .selfdestruct => none
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

/-- Effect classification of each built-in (total on the finite `Op` enum). The flags
over-approximate (see `Effects`); unmodeled external ops get the conservative `top`. -/
def effects : Op → Effects
  -- pure computation
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .addmod | .mulmod | .exp
  | .signextend | .clz | .lt | .gt | .slt | .sgt | .eq | .iszero
  | .and | .or | .xor | .not | .byte | .shl | .shr | .sar | .pop =>
      { deterministic := true, reads := false, writes := false, halts := false }
  -- deterministic state reads
  | .msize | .sload | .tload
  | .calldataload | .calldatasize | .codesize | .returndatasize
  | .address | .origin | .caller | .callvalue | .gasprice | .selfbalance
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .basefee | .blobbasefee
  | .balance | .extcodesize | .extcodehash | .blockhash | .blobhash
  | .datasize | .dataoffset =>
      { deterministic := true, reads := true, writes := false, halts := false }
  -- deterministic writes (no state read)
  | .mstore | .mstore8 | .sstore | .tstore =>
      { deterministic := true, reads := false, writes := true, halts := false }
  -- deterministic read+write (memory reads can expand memory, observable through `msize`)
  | .keccak256 | .mload | .mcopy | .calldatacopy | .codecopy | .returndatacopy
  | .extcodecopy | .datacopy
  | .log0 | .log1 | .log2 | .log3 | .log4 =>
      { deterministic := true, reads := true, writes := true, halts := false }
  -- external interaction: conservative
  | .gas | .call | .callcode | .delegatecall | .staticcall
  | .create | .create2 | .selfdestruct => Effects.top
  -- halting
  | .stop | .invalid =>
      { deterministic := true, reads := false, writes := true, halts := true }
  | .ret | .revert =>
      { deterministic := true, reads := true, writes := true, halts := true }

/-! ### Frontend name mapping (used by the DSL in `YulSemantics.Syntax`; not by the semantics) -/

/-- The Yul source name of a built-in. -/
def opName : Op → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .sdiv => "sdiv"
  | .mod => "mod" | .smod => "smod" | .addmod => "addmod" | .mulmod => "mulmod" | .exp => "exp"
  | .signextend => "signextend" | .clz => "clz"
  | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"
  | .eq => "eq" | .iszero => "iszero" | .and => "and" | .or => "or" | .xor => "xor" | .not => "not"
  | .byte => "byte" | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .keccak256 => "keccak256" | .pop => "pop"
  | .mload => "mload" | .mstore => "mstore" | .mstore8 => "mstore8" | .mcopy => "mcopy"
  | .msize => "msize"
  | .sload => "sload" | .sstore => "sstore" | .tload => "tload" | .tstore => "tstore"
  | .calldataload => "calldataload" | .calldatasize => "calldatasize"
  | .calldatacopy => "calldatacopy" | .codesize => "codesize" | .codecopy => "codecopy"
  | .returndatasize => "returndatasize" | .returndatacopy => "returndatacopy"
  | .datasize => "datasize" | .dataoffset => "dataoffset" | .datacopy => "datacopy"
  | .address => "address" | .origin => "origin" | .caller => "caller"
  | .callvalue => "callvalue" | .gasprice => "gasprice" | .selfbalance => "selfbalance"
  | .coinbase => "coinbase" | .timestamp => "timestamp" | .number => "number"
  | .prevrandao => "prevrandao" | .gaslimit => "gaslimit" | .chainid => "chainid"
  | .basefee => "basefee" | .blobbasefee => "blobbasefee"
  | .balance => "balance" | .extcodesize => "extcodesize" | .extcodecopy => "extcodecopy"
  | .extcodehash => "extcodehash" | .blockhash => "blockhash" | .blobhash => "blobhash"
  | .log0 => "log0" | .log1 => "log1" | .log2 => "log2" | .log3 => "log3" | .log4 => "log4"
  | .gas => "gas" | .call => "call" | .callcode => "callcode"
  | .delegatecall => "delegatecall" | .staticcall => "staticcall"
  | .create => "create" | .create2 => "create2" | .selfdestruct => "selfdestruct"
  | .stop => "stop" | .ret => "return" | .revert => "revert" | .invalid => "invalid"

/-- Resolve a Yul source name to a built-in, or `none` if it is not a built-in (in which case a
call to it is a user-defined function call). -/
def parse : Ident → Option Op
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "sdiv" => some .sdiv | "mod" => some .mod | "smod" => some .smod | "addmod" => some .addmod
  | "mulmod" => some .mulmod | "exp" => some .exp | "signextend" => some .signextend
  | "clz" => some .clz
  | "lt" => some .lt | "gt" => some .gt | "slt" => some .slt | "sgt" => some .sgt
  | "eq" => some .eq | "iszero" => some .iszero | "and" => some .and | "or" => some .or
  | "xor" => some .xor | "not" => some .not | "byte" => some .byte
  | "shl" => some .shl | "shr" => some .shr | "sar" => some .sar
  | "keccak256" => some .keccak256 | "pop" => some .pop
  | "mload" => some .mload | "mstore" => some .mstore | "mstore8" => some .mstore8
  | "mcopy" => some .mcopy | "msize" => some .msize
  | "sload" => some .sload | "sstore" => some .sstore | "tload" => some .tload
  | "tstore" => some .tstore
  | "calldataload" => some .calldataload | "calldatasize" => some .calldatasize
  | "calldatacopy" => some .calldatacopy | "codesize" => some .codesize
  | "codecopy" => some .codecopy | "returndatasize" => some .returndatasize
  | "returndatacopy" => some .returndatacopy
  | "datasize" => some .datasize | "dataoffset" => some .dataoffset | "datacopy" => some .datacopy
  | "address" => some .address | "origin" => some .origin | "caller" => some .caller
  | "callvalue" => some .callvalue | "gasprice" => some .gasprice
  | "selfbalance" => some .selfbalance | "coinbase" => some .coinbase
  | "timestamp" => some .timestamp | "number" => some .number
  | "prevrandao" => some .prevrandao | "gaslimit" => some .gaslimit
  | "chainid" => some .chainid | "basefee" => some .basefee
  | "blobbasefee" => some .blobbasefee
  | "balance" => some .balance | "extcodesize" => some .extcodesize
  | "extcodecopy" => some .extcodecopy | "extcodehash" => some .extcodehash
  | "blockhash" => some .blockhash | "blobhash" => some .blobhash
  | "log0" => some .log0 | "log1" => some .log1 | "log2" => some .log2
  | "log3" => some .log3 | "log4" => some .log4
  | "gas" => some .gas | "call" => some .call | "callcode" => some .callcode
  | "delegatecall" => some .delegatecall | "staticcall" => some .staticcall
  | "create" => some .create | "create2" => some .create2
  | "selfdestruct" => some .selfdestruct
  | "stop" => some .stop | "return" => some .ret | "revert" => some .revert
  | "invalid" => some .invalid
  | _ => none

/-- Smart constructor for a call in source: resolve the name to a built-in if it is one, otherwise
treat it as a user-defined function call. Used by the DSL (`YulSemantics.Syntax`). For a literal
built-in name this reduces to `Expr.builtin op args` definitionally. -/
def mkCall (name : Ident) (args : List (Expr Op)) : Expr Op :=
  match parse name with
  | some op => .builtin op args
  | none    => .call name args

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

/-- The EVM dialect as an `ExecDialect`: `Builtin` is defined from `stepOp`, so the executable
`builtinFn := stepOp` agrees with it by construction. `@[reducible]` for the same reason as `evm`. -/
@[reducible] def exec : ExecDialect := { toDialect := evm, builtinFn := stepOp }

/-- The EVM executable dialect is lawful: `Builtin` and `builtinFn` agree definitionally (both are
`stepOp`). -/
theorem exec_lawful : exec.Lawful := fun _ _ _ _ => Iff.rfl

set_option linter.unusedSimpArgs false in
/-- The EVM dialect's effect flags soundly over-approximate its built-in semantics. In particular,
operations marked non-writing return the input state unchanged, and operations marked non-halting
can only produce a normal result. -/
theorem effects_sound : evm.EffectsSound := by
  refine ⟨?_, ?_, ?_⟩
  · intro op _
    exact exec_lawful.deterministic op
  · intro op hw
    cases op <;> simp [effects] at hw
    all_goals
      intro args st r hb
      change stepOp _ args st = some r at hb
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, args⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1] <;> subst r <;> rfl
  · intro op hh
    cases op <;> simp [effects] at hh
    all_goals
      intro args st r hb
      change stepOp _ args st = some r at hb
      rcases args with
        _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, args⟩⟩⟩⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1] <;>
        first
        | (rcases hb with ⟨_, hb⟩; subst r; rfl)
        | (subst r; rfl)

/-! ### Smoke tests — structural dispatch reduces cleanly (no `maxRecDepth` gymnastics). -/

example (x : U256) (st : EvmState) : stepOp .add [x, 0] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .mul [x, 1] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .and [x, x] st = some (.ok [x] st) := by simp [stepOp, bin]
example (st : EvmState) : stepOp .caller [] st = some (.ok [st.env.caller] st) := by simp [stepOp, rd0]
example (st : EvmState) : stepOp .clz [0] st = some (.ok [256] st) := by simp [stepOp, un, clzVal]

/-! Effect-classification guards for the distinctions most relevant to memory expansion and
control flow. The general semantic guarantee is `effects_sound` above. -/

example : (effects .msize).writes = false := rfl
example : (effects .mload).writes = true := rfl
example : (effects .stop).writes = true := rfl
example : effects .gas = Effects.top := rfl

end YulSemantics.EVM
