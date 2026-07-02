import Mathlib

/-!
# YulSemantics.Basic

Phase 0 placeholder: confirms the toolchain and Mathlib are wired up, and that the EVM word
type `BitVec 256` (see `DESIGN.md` §4) is available with its bitvector automation.

Subsequent phases add:
* `YulSemantics.Ast`     — AST + control-flow `Outcome` (Phase 1)
* `YulSemantics.Dialect` — abstract `Dialect` + EVM dialect instance (Phase 2)
* `YulSemantics.BigStep` — big-step relational semantics, the ground truth (Phase 3)
* `YulSemantics.Syntax`  — concrete-syntax Yul DSL (Phase 4)
* `YulSemantics.Equiv`   — behavior, contextual equivalence, congruence (Phase 5)
-/

namespace YulSemantics

/-- The EVM-dialect value type: a 256-bit machine word (see `DESIGN.md` §4). -/
abbrev Word := BitVec 256

/-- Sanity check that `bv_decide`-style automation is available on `Word`. -/
example (x : Word) : x + 0 = x := by bv_decide

end YulSemantics
