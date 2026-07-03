import YulSemantics.Ast
import YulSemantics.Dialect.EVM
import YulSemantics.Object

/-!
# YulSemantics.Syntax

A concrete-syntax DSL for writing Yul in the EVM dialect (see `DESIGN.md` §5). `yul% { … }`
elaborates to a `Block EVM.Op`, `yulE% …` to an `Expr EVM.Op`, and `yulObject% object "…" { … }`
to an `Object EVM.Op`. Call names are resolved to built-ins via `EVM.mkCall`/`EVM.parse`; unknown
names become user-function calls.

Supported: number/hex/string/`true`/`false` literals, variables, calls; `let`(multi-var,
optional init), assignment, `if`, `switch`/`case`/`default`, `for`, `break`/`continue`/`leave`,
`function` definitions, nested blocks, and call expression-statements; and objects —
`object "name" { code { … } <sub-objects and data> }` with `data "name" "…"` (string) and
`data "name" hex"…"` (hex) segments.

The leading object keywords `object`/`data` are reserved (a syntax category cannot lead with a
non-reserved symbol); the non-leading `code`/`hex` are non-reserved and stay usable as identifiers.
Objects are elaborated by raw-syntax dispatch (quotation patterns handle these productions poorly).

Not yet supported (documented deferrals): type annotations (`: u256`) and hex *string* literals
(`hex"…"`) as expressions.
-/

open Lean

namespace YulSemantics.Yul

open YulSemantics

/-! ### Syntax categories -/

/-- Syntax category for Yul expressions. -/
declare_syntax_cat yulexpr
/-- Syntax category for Yul statements. -/
declare_syntax_cat yulstmt
/-- Syntax category for a single `switch` case. -/
declare_syntax_cat yulcase
/-- Syntax category for a Yul `object`. -/
declare_syntax_cat yulobject
/-- Syntax category for an item inside an object (a sub-object or a data segment). -/
declare_syntax_cat yulobjitem

-- expressions (`true`/`false` are handled as identifiers, to avoid clashing with Lean keywords)
/-- A number literal. -/
syntax num : yulexpr
/-- A string literal. -/
syntax str : yulexpr
/-- A call to a built-in or user function. -/
syntax:max ident "(" yulexpr,* ")" : yulexpr
/-- A variable reference (or the `true` / `false` literals). -/
syntax:max ident : yulexpr

-- statements
/-- A `let` declaration of one or more variables, with an optional initializer. -/
syntax "let " ident,+ (" := " yulexpr)? : yulstmt
/-- An assignment to one or more already-declared variables. -/
syntax (name := assignS) ident,+ " := " yulexpr : yulstmt
/-- An `if` statement (Yul has no `else`). -/
syntax "if " yulexpr "{" yulstmt* "}" : yulstmt
/-- A single `case` of a `switch`. -/
syntax "case " yulexpr "{" yulstmt* "}" : yulcase
/-- A `switch` with zero or more cases and an optional `default`. -/
syntax "switch " yulexpr yulcase* (" default " "{" yulstmt* "}")? : yulstmt
/-- A `for` loop: `for { init } cond { post } { body }`. -/
syntax "for " "{" yulstmt* "}" yulexpr "{" yulstmt* "}" "{" yulstmt* "}" : yulstmt
/-- `break` — exit the enclosing loop. -/
syntax "break" : yulstmt
/-- `continue` — skip to the enclosing loop's `post` block. -/
syntax "continue" : yulstmt
/-- `leave` — return from the enclosing function. -/
syntax "leave" : yulstmt
/-- A function definition, with optional `-> ret` outputs. -/
syntax "function " ident "(" ident,* ")" (" -> " ident,+)? "{" yulstmt* "}" : yulstmt
/-- A nested block, introducing a new scope. -/
syntax "{" yulstmt* "}" : yulstmt
/-- A call evaluated as a statement (for its effects). -/
syntax:max ident "(" yulexpr,* ")" : yulstmt
/-- `return(…)` — spelled out because `return` is a Lean keyword. -/
syntax "return" "(" yulexpr,* ")" : yulstmt

-- objects. The *leading* symbols `object`/`data` must be reserved (a category production cannot
-- lead with a non-reserved symbol); neither collides with any identifier. The non-leading `code`
-- and `hex` stay non-reserved, so `ExecEnv.code` and `Data.hex` remain usable.
/-- A Yul `object`: a named `code` block followed by sub-objects and data segments. -/
syntax (name := objectS)
  "object" str "{" &"code" "{" yulstmt* "}" yulobjitem* "}" : yulobject
/-- A nested sub-object. -/
syntax (name := subObjS) yulobject : yulobjitem
/-- A string data segment: `data "name" "contents"`. -/
syntax (name := dataStrS) "data" str str : yulobjitem
/-- A hex data segment: `data "name" hex"…"`. -/
syntax (name := dataHexS) "data" str &"hex" str : yulobjitem

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

-- Objects are elaborated by *raw-syntax dispatch* rather than quotation patterns: the productions
-- lead with non-reserved symbols (`object`/`code`/`data`), which quotation patterns handle poorly.
-- Argument positions follow the `syntax` declarations above (atoms occupy slots).
mutual

/-- Elaborate an object to an `Object EVM.Op` term. -/
partial def elabObject (stx : TSyntax `yulobject) : MacroM (TSyntax `term) := do
  let raw := stx.raw
  let name : TSyntax `str := ⟨raw.getArg 1⟩
  let stmts := (raw.getArg 5).getArgs                    -- yulstmt* (the `code` block body)
  let items := (raw.getArg 7).getArgs                    -- yulobjitem*
  let codeT ← elabStmts (stmts.map (⟨·⟩))
  let results ← items.mapM (fun i => elabObjItem ⟨i⟩)
  let subs  : Array (TSyntax `term) := results.filterMap (·.1)
  let datas : Array (TSyntax `term) := results.filterMap (·.2)
  `(YulSemantics.Object.mk $name $codeT [$subs,*] [$datas,*])

/-- Elaborate an object item to either a sub-object term (`.1`) or a `(name, Data)` term (`.2`). -/
partial def elabObjItem (stx : TSyntax `yulobjitem) :
    MacroM (Option (TSyntax `term) × Option (TSyntax `term)) := do
  let raw := stx.raw
  let k := raw.getKind
  if k == ``dataStrS then
    let name : TSyntax `str := ⟨raw.getArg 1⟩
    let s    : TSyntax `str := ⟨raw.getArg 2⟩
    return (none, some (← `(($name, YulSemantics.Data.string $s))))
  else if k == ``dataHexS then
    let name  : TSyntax `str := ⟨raw.getArg 1⟩
    let bytes : TSyntax `str := ⟨raw.getArg 3⟩
    return (none, some (← `(($name, YulSemantics.Data.hex (YulSemantics.Data.ofHex $bytes)))))
  else
    -- a sub-object (kind `subObjS` wrapping the object, or the object node directly)
    let objRaw := if k == ``objectS then raw else raw.getArg 0
    return (some (← elabObject ⟨objRaw⟩), none)

end

/-! ### Entry points -/

/-- `yul% { … }` : a Yul program/block as a `Block EVM.Op`. -/
syntax (name := yulBlockTerm) "yul% " "{" yulstmt* "}" : term
/-- `yulE% …` : a Yul expression as an `Expr EVM.Op`. -/
syntax (name := yulExprTerm) "yulE% " yulexpr : term
/-- `yulObject% object "…" { … }` : a Yul object as an `Object EVM.Op`. -/
syntax (name := yulObjectTerm) "yulObject% " yulobject : term

macro_rules
  | `(yul% { $stmts* }) => do
      let b ← elabStmts stmts
      `(($b : YulSemantics.Block YulSemantics.EVM.Op))
  | `(yulE% $e) => do
      let et ← elabExpr e
      `(($et : YulSemantics.Expr YulSemantics.EVM.Op))
  | `(yulObject% $o) => do
      let ot ← elabObject o
      `(($ot : YulSemantics.Object YulSemantics.EVM.Op))

end YulSemantics.Yul
