import Std.Tactic.BVDecide

/-!
# YulSemantics.Basic

Confirms the toolchain is wired up and that the EVM word type `BitVec 256`
(see `DESIGN.md` §4) is available with its bitvector automation.

This module deliberately does **not** `import Mathlib`. Every Lean module's `initialize_*`
calls the initializer of each module it imports, so a bare `import Mathlib` anywhere in a
downstream executable's import closure is a genuine symbol reference that keeps all ~8200
Mathlib object files alive at link time. `bv_decide` comes from `Std`, so nothing here needs
Mathlib; the modules that really do use Mathlib import the specific files they need.

Module map:
* `YulSemantics.Ast`     — AST + control-flow `Outcome`
* `YulSemantics.Dialect` — abstract `Dialect` + EVM dialect instance
* `YulSemantics.BigStep` — big-step relational semantics, the ground truth
* `YulSemantics.Syntax`  — concrete-syntax Yul DSL
* `YulSemantics.Equiv`   — behavior, contextual equivalence, congruence
-/

namespace YulSemantics

/-- The EVM-dialect value type: a 256-bit machine word (see `DESIGN.md` §4). -/
abbrev Word := BitVec 256

/-- Sanity check that `bv_decide`-style automation is available on `Word`. -/
example (x : Word) : x + 0 = x := by bv_decide

end YulSemantics
