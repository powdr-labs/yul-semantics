import Mathlib

/-!
# YulSemantics.Basic

Confirms the toolchain and Mathlib are wired up, and that the EVM word type `BitVec 256`
(see `DESIGN.md` §4) is available with its bitvector automation.

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
