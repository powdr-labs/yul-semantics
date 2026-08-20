/-!
# YulSemantics.Basic

Defines the EVM word type `BitVec 256` (see `DESIGN.md` §4).

This project does **not** depend on Mathlib — and, deliberately, no library module imports a
*tactic* module (`Std.Tactic.*`, `Batteries.Tactic.*`) either. Every Lean module's `initialize_*`
calls the initializer of each module it imports, so importing a tactic framework anywhere in an
executable's import closure is a genuine symbol reference that links the whole elaborator
(`libLean`) into the binary. Proof automation runs at proof-checking time; it does not need to be
in the import graph. The only external dependency is Batteries, kept solely as the `lake lint`
driver — nothing imports it.

Module map:
* `YulSemantics.Ast`     — AST + control-flow `Outcome`
* `YulSemantics.Dialect` — abstract `Dialect` + EVM dialect instance
* `YulSemantics.BigStep` — big-step relational semantics, the ground truth
* `YulSemantics.Contract` — compositional, proof-facing relational contracts
* `YulSemantics.Syntax`  — concrete-syntax Yul DSL
* `YulSemantics.Equiv`   — behavior, contextual equivalence, congruence
-/

namespace YulSemantics

/-- The EVM-dialect value type: a 256-bit machine word (see `DESIGN.md` §4). -/
abbrev Word := BitVec 256

end YulSemantics
