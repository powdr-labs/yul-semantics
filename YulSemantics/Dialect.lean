import YulSemantics.Ast
import Batteries.Tactic.Lint  -- for the `nolint` attribute and the `unusedArguments` linter

/-!
# YulSemantics.Dialect

The abstract **dialect** interface. Yul's core (control flow, scoping, functions) is independent of
its built-in functions; a `Dialect` packages everything dialect-specific:

* the value type and machine state,
* how literals are interpreted (`litValue`) and which literals are well-formed (`litWF`),
* a (possibly non-deterministic) interpretation of built-ins (`Builtin`), and
* an effect classification of built-ins (`effects`) used to justify optimizations.

The big-step semantics (Phase 3) is parameterized over a `Dialect`; the EVM instance lives in
`YulSemantics.Dialect.EVM`. See `DESIGN.md` §3.

This module is dependency-light (no Mathlib): it only needs the AST.
-/

namespace YulSemantics

/-- The result of invoking a built-in function on some arguments and state.

* `ok rets st'` — the built-in returned normally with values `rets`, leaving state `st'`.
* `halt st'` — a halting built-in (`return`/`revert`/`stop`/`invalid`) fired; execution unwinds to
  the top. The halt payload (kind + return/revert data) lives in `st'`, not here, so this type — and
  the `Outcome.halt` it maps to — stay dialect-agnostic. -/
inductive BuiltinResult (Value State : Type)
  | ok   (rets : List Value) (st : State)
  | halt (st : State)

namespace BuiltinResult
variable {Value State : Type}

/-- The state component of a built-in result. -/
def state : BuiltinResult Value State → State
  | .ok _ st => st
  | .halt st => st

/-- Whether the result is a halt (rather than a normal return). -/
def isHalt : BuiltinResult Value State → Bool
  | .halt _ => true
  | .ok ..  => false

end BuiltinResult

/-- Effect classification of a built-in, used to justify optimization passes (see `DESIGN.md`).

The flags are an *over-approximation*: a `true` means the built-in *may* have that effect. A sound
classification for a dialect must satisfy the predicates in `Dialect` below (e.g. `writes = false`
implies the built-in never changes the state).

* `deterministic` — same arguments and state always yield the same result (so the call may be
  duplicated / commonly-subexpression-eliminated). `gas()` and external call outcomes are *not*
  deterministic.
* `reads`  — the built-in *observes* the prior machine state (see the field doc below for the precise
  meaning and why it is currently the one flag without a machine-checked soundness proof).
* `writes` — the built-in may change the machine state.
* `halts`  — the built-in may halt execution instead of returning. -/
structure Effects where
  /-- Same arguments and state always yield the same result. -/
  deterministic : Bool
  /-- The built-in **observes** the prior machine state.

  Precise intended meaning: `reads = false` promises that the built-in does *not consult* the current
  state contents in deciding its behavior — both its return values and the *delta* it applies to the
  state are a function of its arguments alone. Crucially this is orthogonal to `writes`: a blind
  overwrite such as `mstore(p, v)`/`sstore(k, v)` is non-reading (`reads = false`) even though it is
  writing (`writes = true`), because the bytes it stores and where it stores them are determined by
  the arguments, not by what the state previously held. Conversely `mload`, `keccak256`, `sload`, and
  the `*copy` family are reading: their result or the data they move depends on the current state.
  `reads = true` is the conservative over-approximation ("may observe state").

  This is what optimizations need in order to move a non-reading write across an unrelated read, or
  to rule out a read-after-write dependency between two calls.

  **Why this flag is currently unproven** (unlike `deterministic`/`writes`/`halts`, which
  `Dialect.EffectsSound` turns into machine-checked guarantees): stating `reads = false` formally
  requires a *notion of state observation* — a way to say two states "agree on the part this built-in
  could look at" (a read footprint / framing relation) and then that the built-in's result and delta
  are invariant under changing the rest. This repo does not yet have that framing apparatus, so a
  `NonReading` predicate and a corresponding `EffectsSound` field are left as future work rather than
  asserted. The `reads` assignments in a concrete dialect are therefore *documented, audited-for-
  consistency* over-approximations, not yet formally discharged. -/
  reads  : Bool
  /-- The built-in may change the machine state. -/
  writes : Bool
  /-- The built-in may halt execution instead of returning. -/
  halts  : Bool
  deriving Repr, DecidableEq, Inhabited

-- The `prec` argument of the auto-derived pretty-printer is genuinely unused for this plain record.
attribute [nolint unusedArguments] instReprEffects.repr

namespace Effects

/-- A *pure* built-in: a deterministic function of its arguments alone, with no state interaction and
no halting. Pure calls may be freely duplicated, reordered, and eliminated. -/
def pure (e : Effects) : Bool := e.deterministic && !e.reads && !e.writes && !e.halts

/-- The most conservative classification: assume every effect. Used as the default for built-ins a
dialect does not model. -/
def top : Effects := { deterministic := false, reads := true, writes := true, halts := true }

end Effects

/-- A Yul **dialect**: the complete dialect-specific interpretation the core semantics is
parameterized over. -/
structure Dialect where
  /-- The dialect's built-in operation type (a finite enum for the EVM dialect). The AST is
  parameterized over this type (see `YulSemantics.Expr`). -/
  Op : Type
  /-- The value type (for the EVM dialect: `BitVec 256`). -/
  Value : Type
  /-- The machine / world state (memory, storage, …). -/
  State : Type
  /-- Interpret a literal as a value. Total; on ill-formed literals (see `litWF`) its behavior is
  unspecified-but-defined (e.g. the EVM dialect wraps mod `2^256`), and such literals never occur in
  well-formed programs. -/
  litValue : Literal → Value
  /-- Which literals are well-formed for this dialect (e.g. EVM: numbers `< 2^256`, string literals
  `≤ 32` bytes). The semantics and compiler are stated over well-formed programs. -/
  litWF : Literal → Prop
  /-- Interpretation of a built-in call: `Builtin op args st r` holds when invoking `op` on `args`
  in state `st` may produce result `r`. A relation (not a function) so that non-deterministic
  built-ins (`gas()`, external calls) can be modeled. -/
  Builtin : Op → List Value → State → BuiltinResult Value State → Prop
  /-- Effect classification of each built-in. -/
  effects : Op → Effects

namespace Dialect

variable (D : Dialect)

/-- The built-in `op` is deterministic: at most one result per arguments and state. -/
def Deterministic (op : D.Op) : Prop :=
  ∀ args st r₁ r₂, D.Builtin op args st r₁ → D.Builtin op args st r₂ → r₁ = r₂

/-- The built-in `op` never changes the state. -/
def NonWriting (op : D.Op) : Prop :=
  ∀ args st r, D.Builtin op args st r → r.state = st

/-- The built-in `op` never halts execution. -/
def NonHalting (op : D.Op) : Prop :=
  ∀ args st r, D.Builtin op args st r → r.isHalt = false

/-- Soundness of the effect classification: each `false` flag is an actual guarantee about
`Builtin`. Concrete dialects are expected to prove this; generic optimization lemmas take it as a
hypothesis. Because `Op` is a finite enum for concrete dialects, this is provable by case analysis.
The EVM instance proves it as `EVM.effects_sound`.

There is deliberately **no `read` field here**: a `reads = false` guarantee (the built-in does not
observe the prior state; see `Effects.reads`) needs a notion of state observation — a read-footprint /
framing relation stating that the result and the state delta are invariant under changes to the part
of the state the built-in cannot see. That apparatus does not exist in this development yet, so
`reads` remains a documented, audited over-approximation rather than a machine-checked guarantee, and
adding a `Dialect.NonReading` predicate plus a `read` field to this structure is tracked as future
work. The other three flags are discharged below. -/
structure EffectsSound : Prop where
  det   : ∀ op, (D.effects op).deterministic = true → D.Deterministic op
  write : ∀ op, (D.effects op).writes = false → D.NonWriting op
  halt  : ∀ op, (D.effects op).halts = false → D.NonHalting op

end Dialect

/-- A dialect equipped with an *executable* built-in evaluator, for the fuel-indexed interpreter
(`YulSemantics.Interp`). The interpreter needs a function; the ground-truth `Dialect.Builtin` is a
relation (to allow future non-determinism). For deterministic dialects the two agree — that
agreement is proved as part of interpreter adequacy (TODO), not required here. -/
structure ExecDialect extends Dialect where
  /-- Executable built-in evaluation; `none` on an arity mismatch (a stuck call). -/
  builtinFn : Op → List Value → State → Option (BuiltinResult Value State)

/-- The executable evaluator agrees *exactly* with the relational interpretation. This is the
hypothesis under which the interpreter is adequate for the big-step semantics
(`YulSemantics.Adequacy`). For the EVM dialect it holds definitionally (`Builtin` is defined from
`stepOp`). -/
def ExecDialect.Lawful (E : ExecDialect) : Prop :=
  ∀ op args st r, E.Builtin op args st r ↔ E.builtinFn op args st = some r

/-- A lawful executable dialect has deterministic built-ins (its `Builtin` is the graph of a
function). -/
theorem ExecDialect.Lawful.deterministic {E : ExecDialect} (hE : E.Lawful)
    (op : E.toDialect.Op) : E.toDialect.Deterministic op := by
  intro args st r₁ r₂ h₁ h₂
  rw [hE] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

end YulSemantics
