import YulSemantics.BigStep
import YulSemantics.Dialect.EVM

/-!
# YulSemantics.Examples

Smoke tests: hand-built derivations in the big-step semantics for the EVM dialect, confirming the
relation is usable (not vacuous) across the normal, halt, and value-producing paths. Ergonomic
example programs come with the DSL (Phase 4).
-/

namespace YulSemantics.Examples

open YulSemantics EVM

/-- The empty program runs to a normal outcome, leaving the state and (empty) environment. -/
example : Run evm [] EvmState.init [] EvmState.init .normal :=
  ExecStmt.block ExecStmts.nil

/-- `{ stop() }` halts. (Exercises the halt-propagation path through `exprStmt`/built-in.) -/
example : ∃ V' st' o, Run evm [Stmt.exprStmt (Expr.builtin .stop [])] EvmState.init V' st' o :=
  ⟨_, _, _,
    ExecStmt.block
      (ExecStmts.consStop (ExecStmt.exprStmtHalt (EvalExpr.builtinHalt EvalArgs.nil rfl)) (by decide))⟩

/-- `{ let x := add(2, 3) }` runs normally. (Exercises `letVal`, `builtinOk`, and right-to-left
argument evaluation.) -/
example :
    ∃ V' st' o,
      Run evm
        [Stmt.letDecl ["x"] (some (Expr.builtin .add [Expr.lit (.number 2), Expr.lit (.number 3)]))]
        EvmState.init V' st' o :=
  ⟨_, _, _,
    ExecStmt.block (ExecStmts.consNormal
      (ExecStmt.letVal (D := evm) (vals := [litValue (.number 2) + litValue (.number 3)])
        (EvalExpr.builtinOk
          (EvalArgs.cons (EvalArgs.cons EvalArgs.nil EvalExpr.lit) EvalExpr.lit) rfl)
        rfl)
      ExecStmts.nil)⟩

end YulSemantics.Examples
