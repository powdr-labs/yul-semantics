import Mathlib
import YulSemantics.Dialect

/-!
# YulSemantics.Dialect.EVM

A gas-free reference instance of the EVM dialect, with `Value := BitVec 256` (see `DESIGN.md` §4).

Built-ins are a finite enum `Op` (Option D), so `stepOp`/`effects` dispatch structurally on the
constructor — fast to reduce and clean to prove about (contrast the earlier string-keyed `match`).
The string↔`Op` correspondence (`opName`, `parse`) is confined to the frontend (`parse` is used by
the DSL in Phase 4; the semantics never touches strings).

## What is modeled

* the computational core: arithmetic, comparison, and bitwise/shift built-ins (all pure);
* byte-addressable `memory` (`mload`/`mstore`/`mstore8`);
* word-addressable `storage`/transient storage (`sload`/`sstore`/`tload`/`tstore`);
* halting built-ins (`stop`/`return`/`revert`/`invalid`).

## What is deferred

`msize`, `keccak256`, the environment/context family, external calls, logs, and `gas()` are simply
absent from `Op`; `parse` returns `none` for them (a frontend error). They will largely arrive by
instantiating the `Dialect` with the external EVM semantics. Gas is not modeled (`DESIGN.md` §1).
-/

namespace YulSemantics.EVM

open YulSemantics

/-- The EVM word: a 256-bit machine value. -/
abbrev U256 := BitVec 256

/-- The modeled EVM built-in operations. `ret` is `return` (a Lean keyword). -/
inductive Op
  | add | sub | mul | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero
  | and | or | xor | not | byte | shl | shr | sar
  | mload | mstore | mstore8 | sload | sstore | tload | tstore
  | stop | ret | revert | invalid
  deriving Repr, DecidableEq, Inhabited

/-- How a halting built-in terminated, stored in the machine state. -/
inductive HaltKind
  | stop | ret | revert | invalid
  deriving Repr, DecidableEq, Inhabited

/-- The (gas-free) EVM machine state.

* `memory` — byte-addressable, unbounded, default `0`.
* `storage` / `transient` — word-addressable maps, default `0`.
* `halted` — set once a halting built-in fires: its kind and the return/revert data. -/
structure EvmState where
  memory    : Nat → UInt8
  storage   : U256 → U256
  transient : U256 → U256
  halted    : Option (HaltKind × List UInt8)

/-- The initial machine state: zeroed memory/storage, not halted. -/
def EvmState.init : EvmState :=
  { memory := fun _ => 0, storage := fun _ => 0, transient := fun _ => 0, halted := none }

/-! ### Helpers -/

/-- `b2w c` is the EVM boolean encoding: `1` for `true`, `0` for `false`. -/
@[inline] def b2w (c : Bool) : U256 := if c then 1 else 0

/-- Point-update of a word-addressable map. -/
@[inline] def upd (f : U256 → U256) (k v : U256) : U256 → U256 :=
  fun x => if x = k then v else f x

/-- The `k`-th least-significant byte of a word. -/
@[inline] def byteAt (v : U256) (k : Nat) : UInt8 := UInt8.ofNat (v >>> (8 * k)).toNat

/-- Load a big-endian 32-byte word from `memory` starting at byte address `p`. -/
def loadWord (mem : Nat → UInt8) (p : Nat) : U256 :=
  (List.range 32).foldl (fun acc i => (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 (mem (p + i)).toNat) 0

/-- Store `v` big-endian across the 32 bytes `p .. p+31` of `memory`. -/
def storeWord (mem : Nat → UInt8) (p : Nat) (v : U256) : Nat → UInt8 :=
  fun a => if p ≤ a ∧ a < p + 32 then byteAt v (31 - (a - p)) else mem a

/-- Store the least-significant byte of `v` at byte address `p` (`mstore8`). -/
def storeByte (mem : Nat → UInt8) (p : Nat) (v : U256) : Nat → UInt8 :=
  fun a => if a = p then byteAt v 0 else mem a

/-- Read `n` bytes of `memory` starting at byte address `p`. -/
def readBytes (mem : Nat → UInt8) (p n : Nat) : List UInt8 :=
  (List.range n).map (fun i => mem (p + i))

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
`un`/`bin`/`ter` helpers. This keeps every arm tiny, so reducing `stepOp op args st` on a concrete
`op` is cheap — `simp [stepOp, un, bin, ter]` closes goals without any recursion-depth/heartbeat
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

/-- Two's-complement sign-extension of `x` from byte `i` (EVM `signextend`). -/
def signExtend (i x : U256) : U256 :=
  let k := i.toNat
  if 31 ≤ k then x
  else
    let bits := 8 * (k + 1)
    let low : U256 := (1 <<< bits) - 1
    if x.getLsbD (bits - 1) then x ||| (~~~low) else x &&& low

/-- The built-in step function. Returns `none` on an arity mismatch (a stuck call). -/
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
  -- memory
  | .mload      => match args with | [p]    => some (.ok [loadWord st.memory p.toNat] st) | _ => none
  | .mstore     => match args with | [p, v] => some (.ok [] { st with memory := storeWord st.memory p.toNat v }) | _ => none
  | .mstore8    => match args with | [p, v] => some (.ok [] { st with memory := storeByte st.memory p.toNat v }) | _ => none
  -- storage
  | .sload      => match args with | [k]    => some (.ok [st.storage k] st) | _ => none
  | .sstore     => match args with | [k, v] => some (.ok [] { st with storage := upd st.storage k v }) | _ => none
  | .tload      => match args with | [k]    => some (.ok [st.transient k] st) | _ => none
  | .tstore     => match args with | [k, v] => some (.ok [] { st with transient := upd st.transient k v }) | _ => none
  -- halting
  | .stop       => match args with | []     => some (.halt { st with halted := some (.stop, []) }) | _ => none
  | .ret        => match args with | [p, s] => some (.halt { st with halted := some (.ret, readBytes st.memory p.toNat s.toNat) }) | _ => none
  | .revert     => match args with | [p, s] => some (.halt { st with halted := some (.revert, readBytes st.memory p.toNat s.toNat) }) | _ => none
  | .invalid    => match args with | []     => some (.halt { st with halted := some (.invalid, []) }) | _ => none

/-- Effect classification of each built-in (total on the finite `Op` enum). -/
def effects : Op → Effects
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .addmod | .mulmod | .exp
  | .signextend | .lt | .gt | .slt | .sgt | .eq | .iszero
  | .and | .or | .xor | .not | .byte | .shl | .shr | .sar =>
      { deterministic := true, reads := false, writes := false, halts := false }
  | .mload | .sload | .tload =>
      { deterministic := true, reads := true, writes := false, halts := false }
  | .mstore | .mstore8 | .sstore | .tstore =>
      { deterministic := true, reads := false, writes := true, halts := false }
  | .stop | .invalid =>
      { deterministic := true, reads := false, writes := false, halts := true }
  | .ret | .revert =>
      { deterministic := true, reads := true, writes := false, halts := true }

/-! ### Frontend name mapping (used by the DSL in Phase 4; not by the semantics) -/

/-- The Yul source name of a built-in. -/
def opName : Op → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .sdiv => "sdiv"
  | .mod => "mod" | .smod => "smod" | .addmod => "addmod" | .mulmod => "mulmod" | .exp => "exp"
  | .signextend => "signextend" | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"
  | .eq => "eq" | .iszero => "iszero" | .and => "and" | .or => "or" | .xor => "xor" | .not => "not"
  | .byte => "byte" | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .mload => "mload" | .mstore => "mstore" | .mstore8 => "mstore8"
  | .sload => "sload" | .sstore => "sstore" | .tload => "tload" | .tstore => "tstore"
  | .stop => "stop" | .ret => "return" | .revert => "revert" | .invalid => "invalid"

/-- Resolve a Yul source name to a built-in, or `none` if it is not a modeled built-in (in which
case a call to it is a user-defined function call). -/
def parse : Ident → Option Op
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "sdiv" => some .sdiv | "mod" => some .mod | "smod" => some .smod | "addmod" => some .addmod
  | "mulmod" => some .mulmod | "exp" => some .exp | "signextend" => some .signextend
  | "lt" => some .lt | "gt" => some .gt | "slt" => some .slt | "sgt" => some .sgt
  | "eq" => some .eq | "iszero" => some .iszero | "and" => some .and | "or" => some .or
  | "xor" => some .xor | "not" => some .not | "byte" => some .byte
  | "shl" => some .shl | "shr" => some .shr | "sar" => some .sar
  | "mload" => some .mload | "mstore" => some .mstore | "mstore8" => some .mstore8
  | "sload" => some .sload | "sstore" => some .sstore | "tload" => some .tload | "tstore" => some .tstore
  | "stop" => some .stop | "return" => some .ret | "revert" => some .revert | "invalid" => some .invalid
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

/-! ### Smoke tests — structural dispatch reduces cleanly (no `maxRecDepth` gymnastics). -/

example (x : U256) (st : EvmState) : stepOp .add [x, 0] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .mul [x, 1] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .and [x, x] st = some (.ok [x] st) := by simp [stepOp, bin]

end YulSemantics.EVM
