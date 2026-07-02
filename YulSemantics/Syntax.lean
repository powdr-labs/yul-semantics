import YulSemantics.Ast
import YulSemantics.Dialect.EVM

/-!
# YulSemantics.Syntax

A concrete-syntax DSL for writing Yul in the EVM dialect (see `DESIGN.md` §5). `yul% { … }`
elaborates to a `Block EVM.Op`, and `yulE% …` to an `Expr EVM.Op`. Call names are resolved to
built-ins via `EVM.mkCall`/`EVM.parse`; unknown names become user-function calls.

Supported: number/hex/string/`true`/`false` literals, variables, calls; `let`(multi-var,
optional init), assignment, `if`, `switch`/`case`/`default`, `for`, `break`/`continue`/`leave`,
`function` definitions, nested blocks, and call expression-statements.

Not yet supported (documented deferrals): type annotations (`: u256`), object/`code`/`data` syntax,
and hex *string* literals (`hex"…"`).
-/

open Lean

namespace YulSemantics.Yul

open YulSemantics

/-! ### Syntax categories -/

declare_syntax_cat yulexpr
declare_syntax_cat yulstmt
declare_syntax_cat yulcase

-- expressions (`true`/`false` are handled as identifiers, to avoid clashing with Lean keywords)
syntax num : yulexpr
syntax str : yulexpr
syntax:max ident "(" yulexpr,* ")" : yulexpr   -- call (built-in or user function)
syntax:max ident : yulexpr                      -- variable / `true` / `false`

-- statements
syntax "let " ident,+ (" := " yulexpr)? : yulstmt
syntax (name := assignS) ident,+ " := " yulexpr : yulstmt
syntax "if " yulexpr "{" yulstmt* "}" : yulstmt
syntax "case " yulexpr "{" yulstmt* "}" : yulcase
syntax "switch " yulexpr yulcase* (" default " "{" yulstmt* "}")? : yulstmt
syntax "for " "{" yulstmt* "}" yulexpr "{" yulstmt* "}" "{" yulstmt* "}" : yulstmt
syntax "break" : yulstmt
syntax "continue" : yulstmt
syntax "leave" : yulstmt
syntax "function " ident "(" ident,* ")" (" -> " ident,+)? "{" yulstmt* "}" : yulstmt
syntax "{" yulstmt* "}" : yulstmt               -- nested block
syntax:max ident "(" yulexpr,* ")" : yulstmt    -- call expression-statement
syntax "return" "(" yulexpr,* ")" : yulstmt     -- `return(…)` (`return` is a Lean keyword)

/-! ### Elaboration to AST terms -/

private def idStr (id : TSyntax `ident) : String := id.getId.toString

mutual

/-- Elaborate a Yul expression to an `Expr EVM.Op` term. -/
partial def elabExpr : TSyntax `yulexpr → MacroM (TSyntax `term)
  | `(yulexpr| $n:num) => `(YulSemantics.Expr.lit (YulSemantics.Literal.number $n))
  | `(yulexpr| $s:str) => `(YulSemantics.Expr.lit (YulSemantics.Literal.string $s))
  | `(yulexpr| $f:ident ($args,*)) => do
      let a ← args.getElems.mapM elabExpr
      `(YulSemantics.EVM.mkCall $(quote (idStr f)) [$a,*])
  | `(yulexpr| $x:ident) =>
      match idStr x with
      | "true"  => `(YulSemantics.Expr.lit (YulSemantics.Literal.bool true))
      | "false" => `(YulSemantics.Expr.lit (YulSemantics.Literal.bool false))
      | s       => `(YulSemantics.Expr.var $(quote s))
  | _ => Macro.throwUnsupported

/-- Elaborate a Yul literal (a switch-case label) to a `Literal` term. -/
partial def elabLit : TSyntax `yulexpr → MacroM (TSyntax `term)
  | `(yulexpr| $n:num) => `(YulSemantics.Literal.number $n)
  | `(yulexpr| $s:str) => `(YulSemantics.Literal.string $s)
  | `(yulexpr| $x:ident) =>
      match idStr x with
      | "true"  => `(YulSemantics.Literal.bool true)
      | "false" => `(YulSemantics.Literal.bool false)
      | _       => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

/-- Elaborate a Yul statement to a `Stmt EVM.Op` term. -/
partial def elabStmt : TSyntax `yulstmt → MacroM (TSyntax `term)
  | `(yulstmt| let $xs,* $[:= $e]?) => do
      let vs : Array (TSyntax `term) := xs.getElems.map (fun i => quote (idStr i))
      match e with
      | some e => do
          let et ← elabExpr e
          `(YulSemantics.Stmt.letDecl [$vs,*] (some $et))
      | none => `(YulSemantics.Stmt.letDecl [$vs,*] none)
  | `(yulstmt| if $c { $body* }) => do
      let ct ← elabExpr c
      let bt ← elabStmts body
      `(YulSemantics.Stmt.cond $ct $bt)
  | `(yulstmt| switch $c $cs:yulcase* $[default { $d* }]?) => do
      let ct ← elabExpr c
      let cases ← cs.mapM elabCase
      let dflt ← match d with
        | some d => do let db ← elabStmts d; `(some $db)
        | none   => `(none)
      `(YulSemantics.Stmt.switch $ct [$cases,*] $dflt)
  | `(yulstmt| for { $init* } $c { $post* } { $body* }) => do
      let it ← elabStmts init
      let ct ← elabExpr c
      let pt ← elabStmts post
      let bt ← elabStmts body
      `(YulSemantics.Stmt.forLoop $it $ct $pt $bt)
  | `(yulstmt| break)    => `(YulSemantics.Stmt.«break»)
  | `(yulstmt| continue) => `(YulSemantics.Stmt.«continue»)
  | `(yulstmt| leave)    => `(YulSemantics.Stmt.leave)
  | `(yulstmt| function $f ($ps,*) $[-> $rs,*]? { $body* }) => do
      let rsIds : Array (TSyntax `ident) := match rs with
        | some rs => rs.getElems
        | none    => #[]
      let psT : Array (TSyntax `term) := ps.getElems.map (fun i => quote (idStr i))
      let rsT : Array (TSyntax `term) := rsIds.map (fun i => quote (idStr i))
      let bt ← elabStmts body
      `(YulSemantics.Stmt.funDef $(quote (idStr f)) [$psT,*] [$rsT,*] $bt)
  | `(yulstmt| { $body* }) => do
      let bt ← elabStmts body
      `(YulSemantics.Stmt.block $bt)
  | `(yulstmt| $f:ident ($args,*)) => do
      let a ← args.getElems.mapM elabExpr
      `(YulSemantics.Stmt.exprStmt (YulSemantics.EVM.mkCall $(quote (idStr f)) [$a,*]))
  | `(yulstmt| return ($args,*)) => do
      let a ← args.getElems.mapM elabExpr
      `(YulSemantics.Stmt.exprStmt (YulSemantics.EVM.mkCall "return" [$a,*]))
  | stx => do
      -- assignment (`ident,+ := expr`) can't be matched by a quotation pattern (it starts with a
      -- bare comma-separated antiquotation), so dispatch it from the raw syntax here.
      if stx.raw.getKind == ``assignS then
        let ids := stx.raw.getArg 0 |>.getSepArgs
        let vs : Array (TSyntax `term) := ids.map (fun i => quote i.getId.toString)
        let et ← elabExpr ⟨stx.raw.getArg 2⟩
        `(YulSemantics.Stmt.assign [$vs,*] $et)
      else
        Macro.throwUnsupported

/-- Elaborate a switch case to a `(Literal × Block EVM.Op)` term. -/
partial def elabCase : TSyntax `yulcase → MacroM (TSyntax `term)
  | `(yulcase| case $l { $b* }) => do
      let lt ← elabLit l
      let bt ← elabStmts b
      `(($lt, $bt))
  | _ => Macro.throwUnsupported

/-- Elaborate a statement sequence to a `Block EVM.Op` term (a `List (Stmt EVM.Op)`). -/
partial def elabStmts (stmts : Array (TSyntax `yulstmt)) : MacroM (TSyntax `term) := do
  let ss ← stmts.mapM elabStmt
  `([$ss,*])

end

/-! ### Entry points -/

/-- `yul% { … }` : a Yul program/block as a `Block EVM.Op`. -/
syntax (name := yulBlockTerm) "yul% " "{" yulstmt* "}" : term
/-- `yulE% …` : a Yul expression as an `Expr EVM.Op`. -/
syntax (name := yulExprTerm) "yulE% " yulexpr : term

macro_rules
  | `(yul% { $stmts* }) => do
      let b ← elabStmts stmts
      `(($b : YulSemantics.Block YulSemantics.EVM.Op))
  | `(yulE% $e) => do
      let et ← elabExpr e
      `(($et : YulSemantics.Expr YulSemantics.EVM.Op))

end YulSemantics.Yul
