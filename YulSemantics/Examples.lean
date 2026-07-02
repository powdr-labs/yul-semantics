import YulSemantics.BigStep
import YulSemantics.Dialect.EVM
import YulSemantics.Syntax

/-!
# YulSemantics.Examples

Smoke tests: hand-built derivations in the big-step semantics for the EVM dialect, confirming the
relation is usable (not vacuous) across the normal, halt, and value-producing paths, plus DSL
round-trip / elaboration tests for `YulSemantics.Syntax`.
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

/-! ### DSL (`YulSemantics.Syntax`) -/

/-- The concrete syntax `add(2, 3)` resolves to the built-in `Op.add` and produces the expected
AST (the smart constructor `mkCall` reduces definitionally). -/
example :
    (yul% { let x := add(2, 3) }) =
      [Stmt.letDecl ["x"] (some (Expr.builtin .add [Expr.lit (.number 2), Expr.lit (.number 3)]))] :=
  rfl

/-- A call to a name that is not a built-in resolves to a user-function call. -/
example :
    (yul% { let y := myFn(1) }) =
      [Stmt.letDecl ["y"] (some (Expr.call "myFn" [Expr.lit (.number 1)]))] :=
  rfl

/-- Multi-variable `let`/assignment, `if`, and a call statement all elaborate. -/
example :
    (yul% {
      let a, b := myPair()
      a := add(a, b)
      if lt(a, 10) { sstore(0, a) }
    }) =
      [ Stmt.letDecl ["a", "b"] (some (Expr.call "myPair" [])),
        Stmt.assign ["a"] (Expr.builtin .add [Expr.var "a", Expr.var "b"]),
        Stmt.cond (Expr.builtin .lt [Expr.var "a", Expr.lit (.number 10)])
          [Stmt.exprStmt (Expr.builtin .sstore [Expr.lit (.number 0), Expr.var "a"])] ] :=
  rfl

/-- A multi-target assignment (`a, b := swap(a, b)`) elaborates to a `Stmt.assign` with several
LHS variables (exercising the raw-syntax `assignS` dispatch). -/
example :
    (yul% {
      let a, b := myPair()
      a, b := swap(a, b)
    }) =
      [ Stmt.letDecl ["a", "b"] (some (Expr.call "myPair" [])),
        Stmt.assign ["a", "b"] (Expr.call "swap" [Expr.var "a", Expr.var "b"]) ] :=
  rfl

/-- A larger program exercising `function` (with a return), `for`, nested `let`/assignment, and
halting built-ins elaborates to a `Block EVM.Op`. -/
def sumProgram : Block EVM.Op := yul% {
  function sum(n) -> s {
    s := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      s := add(s, i)
    }
  }
  let total := sum(10)
  mstore(0, total)
  return(0, 32)
}

/-- `switch`/`case`/`default` elaborates. -/
def switchProgram : Block EVM.Op := yul% {
  let x := 3
  switch x
  case 1 { x := 10 }
  case 2 { x := 20 }
  default { x := 0 }
}

end YulSemantics.Examples
