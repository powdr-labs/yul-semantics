import YulSemantics.Ast
import YulSemantics.Dialect

/-!
# YulSemantics.BigStep

The **big-step relational semantics** of Yul — the ground truth (see `DESIGN.md` §2). It is an
inductive evaluation judgment over an arbitrary `Dialect D`, gas-free.

## Encoding: one judgment, five syntactic classes

Conceptually the semantics is five mutually inductive relations: expression evaluation, argument
lists, statements, statement sequences, and loop iteration. They are encoded as a **single indexed
inductive judgment** `Step` over a sum `Code` of the five syntactic classes and a sum `Res` of the
two result shapes; the five conceptual relations are recovered as abbreviations (`EvalExpr`,
`EvalArgs`, `ExecStmt`, `ExecStmts`, `ExecLoop`) with their natural signatures, so downstream
statements read exactly as with a mutual family.

Why not a literal `mutual` family: Lean's `induction` tactic does not support mutually inductive
predicates (their recursors have one motive per relation), and the equation compiler cannot compile
mutual structural recursion over them (the premises have constructor-shaped result indices, which
defeat below-style elimination). With a single inductive, every derivation induction — determinism,
interpreter adequacy, and eventually the compiler-correctness simulation — is a standard
`induction … with` proof.

## Environments

* Variables (`VEnv`) are a scoped stack `List (Ident × Value)`: `let` prepends, `assign` updates in
  place, and a block drops the variables it introduced on exit (`restore`).
* Functions (`FunEnv`) are a stack of *scopes* (`FScope`), innermost first. All function definitions
  of a block are hoisted into one scope (so they may be forward-referenced and mutually recursive).
  A call resolves the function and the tail of scopes visible at its definition site, so a callee
  sees its own scope and enclosing ones — but **not** inner scopes, and **not** caller variables
  (Yul functions cannot access variables from outer scopes).

## Outcomes and halting

Statement execution yields an `Outcome` (`normal`/`break`/`continue`/`leave`/`halt`). Because a
nested call can halt (`return`/`revert`/`stop`), expression evaluation yields `EResult` — either a
list of values with a new state, or a halt with a new state (payload in the state, per `DESIGN.md`).

## Conventions / points to revisit

* **Argument evaluation is right-to-left** (Yul's specified order); values are collected in source
  order. TODO: confirm against the Yul spec / the EVM repo.
* **Truthiness**: a condition is true iff its value `≠ D.zero` (`D.zero := litValue 0`), matching the
  EVM convention `0 = false`.
* Ill-formed situations (unbound variable, arity mismatch, `break` outside a loop, …) simply have no
  applicable rule — the program is *stuck* (no derivation). The semantics is intended for well-formed
  programs.
-/

namespace YulSemantics

/-! ### Environments and helpers -/

/-- A variable environment: a scoped stack of bindings, innermost (most recent) first. -/
abbrev VEnv (D : Dialect) := List (Ident × D.Value)

/-- A user-defined function declaration (its signature and body). -/
structure FDecl (D : Dialect) where
  /-- The function's formal parameter names. -/
  params : List Ident
  /-- The function's output ("return") variable names. -/
  rets   : List Ident
  /-- The function body. -/
  body   : Block D.Op

/-- One lexical scope's worth of (mutually-recursive) function declarations. -/
abbrev FScope (D : Dialect) := List (Ident × FDecl D)

/-- The function environment: a stack of scopes, innermost first. -/
abbrev FunEnv (D : Dialect) := List (FScope D)

/-- The result of evaluating an expression: values with a new state, or a halt with a new state. -/
inductive EResult (D : Dialect)
  | vals (vs : List D.Value) (st : D.State)
  | halt (st : D.State)

/-- The dialect's zero value, used to initialize variables and to test truthiness. -/
def Dialect.zero (D : Dialect) : D.Value := D.litValue (.number 0)

/-- Look up a variable's value (innermost binding). -/
def VEnv.get {D : Dialect} (V : VEnv D) (x : Ident) : Option D.Value :=
  (V.find? (fun p => p.1 = x)).map (·.2)

/-- Update the innermost binding of `x` to `v` (no-op if unbound; well-formed programs never hit
that case). Length- and order-preserving, so outer bindings survive a later `restore`. -/
def VEnv.set {D : Dialect} (V : VEnv D) (x : Ident) (v : D.Value) : VEnv D :=
  match V with
  | [] => []
  | (y, w) :: rest => if y = x then (x, v) :: rest else (y, w) :: VEnv.set rest x v

/-- Update several variables in order (for multi-assignment). -/
def VEnv.setMany {D : Dialect} (V : VEnv D) (xs : List Ident) (vs : List D.Value) : VEnv D :=
  (xs.zip vs).foldl (fun acc p => VEnv.set acc p.1 p.2) V

/-- Bind each name to the dialect's zero value. -/
def bindZeros (D : Dialect) (xs : List Ident) : VEnv D := xs.map (fun x => (x, D.zero))

/-- Drop the bindings introduced since `outer` (block/scope exit), keeping outer bindings (with any
in-place updates). Relies on the invariant that execution only prepends and updates in place. -/
def restore {D : Dialect} (outer inner : VEnv D) : VEnv D :=
  inner.drop (inner.length - outer.length)

/-- Collect a block's function definitions into a single hoisted scope. -/
def hoist (D : Dialect) (body : Block D.Op) : FScope D :=
  body.filterMap (fun s => match s with
    | .funDef n ps rs b => some (n, { params := ps, rets := rs, body := b })
    | _ => none)

/-- Resolve a function name to its declaration and the function environment visible at its
definition site (its own scope plus enclosing scopes). -/
def lookupFun {D : Dialect} : FunEnv D → Ident → Option (FDecl D × FunEnv D)
  | [], _ => none
  | scope :: rest, f =>
    match scope.find? (fun p => p.1 = f) with
    | some p => some (p.2, scope :: rest)
    | none => lookupFun rest f

/-- The block a `switch` executes: the first case whose label evaluates equal to the scrutinee `cv`,
else the default (or the empty block when there is neither). Shared by the semantics and the
interpreter, so `switch` is deterministic by construction. -/
def selectSwitch (D : Dialect) [DecidableEq D.Value] (cv : D.Value)
    (cases : List (Literal × Block D.Op)) (dflt : Option (Block D.Op)) : Block D.Op :=
  match cases.find? (fun p => decide (cv = D.litValue p.1)) with
  | some p => p.2
  | none   => dflt.getD []

/-! ### The evaluation judgment -/

/-- The five syntactic classes the judgment ranges over. -/
inductive Code (Op : Type)
  /-- Evaluate a single expression. -/
  | expr  (e : Expr Op)
  /-- Evaluate an argument list (right-to-left). -/
  | args  (es : List (Expr Op))
  /-- Execute a single statement. -/
  | stmt  (s : Stmt Op)
  /-- Execute a statement sequence. -/
  | stmts (ss : List (Stmt Op))
  /-- Execute a `for`-loop's iteration (after its `init` block has run). -/
  | loop  (c : Expr Op) (post body : Block Op)

/-- The result of a `Step`: expression-class code produces an `EResult`; statement-class code
produces a variable environment, a state, and an `Outcome`. -/
inductive Res (D : Dialect)
  | eres (r : EResult D)
  | sres (V : VEnv D) (st : D.State) (o : Outcome)

/-- The big-step evaluation judgment: `Step D funs V st code res` holds when `code`, run with
function environment `funs`, variable environment `V`, and machine state `st`, may produce `res`.

Requires `[DecidableEq D.Value]` so that `switch` can dispatch through `selectSwitch` (a function),
making it deterministic without a well-formedness side condition. -/
inductive Step (D : Dialect) [DecidableEq D.Value] :
    FunEnv D → VEnv D → D.State → Code D.Op → Res D → Prop where

  /- ### Expressions -/

  | lit {funs V st l} :
      Step D funs V st (.expr (.lit l)) (.eres (.vals [D.litValue l] st))
  | var {funs V st x v} :
      VEnv.get V x = some v →
      Step D funs V st (.expr (.var x)) (.eres (.vals [v] st))
  | builtinOk {funs V st op args argvals st1 rets st2} :
      Step D funs V st (.args args) (.eres (.vals argvals st1)) →
      D.Builtin op argvals st1 (.ok rets st2) →
      Step D funs V st (.expr (.builtin op args)) (.eres (.vals rets st2))
  | builtinHalt {funs V st op args argvals st1 st2} :
      Step D funs V st (.args args) (.eres (.vals argvals st1)) →
      D.Builtin op argvals st1 (.halt st2) →
      Step D funs V st (.expr (.builtin op args)) (.eres (.halt st2))
  | builtinArgsHalt {funs V st op args st1} :
      Step D funs V st (.args args) (.eres (.halt st1)) →
      Step D funs V st (.expr (.builtin op args)) (.eres (.halt st1))
  | callOk {funs V st fn args argvals st1 decl cenv Vend st2 o} :
      Step D funs V st (.args args) (.eres (.vals argvals st1)) →
      lookupFun funs fn = some (decl, cenv) →
      argvals.length = decl.params.length →
      Step D cenv ((decl.params.zip argvals) ++ bindZeros D decl.rets) st1
        (.stmt (.block decl.body)) (.sres Vend st2 o) →
      (o = .normal ∨ o = .leave) →
      Step D funs V st (.expr (.call fn args))
        (.eres (.vals (decl.rets.map (fun r => (VEnv.get Vend r).getD D.zero)) st2))
  | callHalt {funs V st fn args argvals st1 decl cenv Vend st2} :
      Step D funs V st (.args args) (.eres (.vals argvals st1)) →
      lookupFun funs fn = some (decl, cenv) →
      argvals.length = decl.params.length →
      Step D cenv ((decl.params.zip argvals) ++ bindZeros D decl.rets) st1
        (.stmt (.block decl.body)) (.sres Vend st2 .halt) →
      Step D funs V st (.expr (.call fn args)) (.eres (.halt st2))
  | callArgsHalt {funs V st fn args st1} :
      Step D funs V st (.args args) (.eres (.halt st1)) →
      Step D funs V st (.expr (.call fn args)) (.eres (.halt st1))

  /- ### Argument lists (evaluated right-to-left; values collected in source order) -/

  | argsNil {funs V st} :
      Step D funs V st (.args []) (.eres (.vals [] st))
  | argsCons {funs V st e rest restvals st1 v st2} :
      Step D funs V st (.args rest) (.eres (.vals restvals st1)) →
      Step D funs V st1 (.expr e) (.eres (.vals [v] st2)) →
      Step D funs V st (.args (e :: rest)) (.eres (.vals (v :: restvals) st2))
  | argsRestHalt {funs V st e rest st1} :
      Step D funs V st (.args rest) (.eres (.halt st1)) →
      Step D funs V st (.args (e :: rest)) (.eres (.halt st1))
  | argsHeadHalt {funs V st e rest restvals st1 st2} :
      Step D funs V st (.args rest) (.eres (.vals restvals st1)) →
      Step D funs V st1 (.expr e) (.eres (.halt st2)) →
      Step D funs V st (.args (e :: rest)) (.eres (.halt st2))

  /- ### Statements -/

  | funDef {funs V st n ps rs b} :
      Step D funs V st (.stmt (.funDef n ps rs b)) (.sres V st .normal)
  | block {funs V st body Vb stb o} :
      Step D (hoist D body :: funs) V st (.stmts body) (.sres Vb stb o) →
      Step D funs V st (.stmt (.block body)) (.sres (restore V Vb) stb o)
  | letZero {funs V st vars} :
      Step D funs V st (.stmt (.letDecl vars none)) (.sres (bindZeros D vars ++ V) st .normal)
  | letVal {funs V st vars e vals st1} :
      Step D funs V st (.expr e) (.eres (.vals vals st1)) →
      vals.length = vars.length →
      Step D funs V st (.stmt (.letDecl vars (some e))) (.sres (vars.zip vals ++ V) st1 .normal)
  | letHalt {funs V st vars e st1} :
      Step D funs V st (.expr e) (.eres (.halt st1)) →
      Step D funs V st (.stmt (.letDecl vars (some e))) (.sres V st1 .halt)
  | assignVal {funs V st vars e vals st1} :
      Step D funs V st (.expr e) (.eres (.vals vals st1)) →
      vals.length = vars.length →
      Step D funs V st (.stmt (.assign vars e)) (.sres (VEnv.setMany V vars vals) st1 .normal)
  | assignHalt {funs V st vars e st1} :
      Step D funs V st (.expr e) (.eres (.halt st1)) →
      Step D funs V st (.stmt (.assign vars e)) (.sres V st1 .halt)
  | exprStmt {funs V st e st1} :
      Step D funs V st (.expr e) (.eres (.vals [] st1)) →
      Step D funs V st (.stmt (.exprStmt e)) (.sres V st1 .normal)
  | exprStmtHalt {funs V st e st1} :
      Step D funs V st (.expr e) (.eres (.halt st1)) →
      Step D funs V st (.stmt (.exprStmt e)) (.sres V st1 .halt)
  | ifTrue {funs V st c body cv st1 V' st2 o} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres V' st2 o) →
      Step D funs V st (.stmt (.cond c body)) (.sres V' st2 o)
  | ifFalse {funs V st c body cv st1} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv = D.zero →
      Step D funs V st (.stmt (.cond c body)) (.sres V st1 .normal)
  | ifHalt {funs V st c body st1} :
      Step D funs V st (.expr c) (.eres (.halt st1)) →
      Step D funs V st (.stmt (.cond c body)) (.sres V st1 .halt)
  | switchExec {funs V st c cases dflt cv st1 V' st2 o} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      Step D funs V st1 (.stmt (.block (selectSwitch D cv cases dflt))) (.sres V' st2 o) →
      Step D funs V st (.stmt (.switch c cases dflt)) (.sres V' st2 o)
  | switchHalt {funs V st c cases dflt st1} :
      Step D funs V st (.expr c) (.eres (.halt st1)) →
      Step D funs V st (.stmt (.switch c cases dflt)) (.sres V st1 .halt)
  | forLoop {funs V st init c post body Vinit stinit Vend stend o} :
      Step D (hoist D init :: funs) V st (.stmts init) (.sres Vinit stinit .normal) →
      Step D (hoist D init :: funs) Vinit stinit (.loop c post body) (.sres Vend stend o) →
      Step D funs V st (.stmt (.forLoop init c post body)) (.sres (restore V Vend) stend o)
  | forInitHalt {funs V st init c post body Vinit stinit} :
      Step D (hoist D init :: funs) V st (.stmts init) (.sres Vinit stinit .halt) →
      Step D funs V st (.stmt (.forLoop init c post body)) (.sres (restore V Vinit) stinit .halt)
  | «break» {funs V st} :
      Step D funs V st (.stmt .«break») (.sres V st .«break»)
  | «continue» {funs V st} :
      Step D funs V st (.stmt .«continue») (.sres V st .«continue»)
  | leave {funs V st} :
      Step D funs V st (.stmt .leave) (.sres V st .leave)

  /- ### Statement sequences (short-circuiting on a non-`normal` outcome) -/

  | seqNil {funs V st} :
      Step D funs V st (.stmts []) (.sres V st .normal)
  | seqCons {funs V st s rest V1 st1 V2 st2 o} :
      Step D funs V st (.stmt s) (.sres V1 st1 .normal) →
      Step D funs V1 st1 (.stmts rest) (.sres V2 st2 o) →
      Step D funs V st (.stmts (s :: rest)) (.sres V2 st2 o)
  | seqStop {funs V st s rest V1 st1 o} :
      Step D funs V st (.stmt s) (.sres V1 st1 o) →
      o ≠ .normal →
      Step D funs V st (.stmts (s :: rest)) (.sres V1 st1 o)

  /- ### Loop iteration (condition-check, body, post, repeat — after `init` has run).
     The outcome is `normal` (loop finished or `break`), `leave`, or `halt`. -/

  | loopDone {funs V st c post body cv st1} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv = D.zero →
      Step D funs V st (.loop c post body) (.sres V st1 .normal)
  | loopCondHalt {funs V st c post body st1} :
      Step D funs V st (.expr c) (.eres (.halt st1)) →
      Step D funs V st (.loop c post body) (.sres V st1 .halt)
  | loopStep {funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres Vb stb ob) →
      (ob = .normal ∨ ob = .«continue») →
      Step D funs Vb stb (.stmt (.block post)) (.sres Vp stp .normal) →
      Step D funs Vp stp (.loop c post body) (.sres Vend stend o) →
      Step D funs V st (.loop c post body) (.sres Vend stend o)
  | loopPostHalt {funs V st c post body cv st1 Vb stb ob Vp stp} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres Vb stb ob) →
      (ob = .normal ∨ ob = .«continue») →
      Step D funs Vb stb (.stmt (.block post)) (.sres Vp stp .halt) →
      Step D funs V st (.loop c post body) (.sres Vp stp .halt)
  | loopBreak {funs V st c post body cv st1 Vb stb} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres Vb stb .«break») →
      Step D funs V st (.loop c post body) (.sres Vb stb .normal)
  | loopLeave {funs V st c post body cv st1 Vb stb} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres Vb stb .leave) →
      Step D funs V st (.loop c post body) (.sres Vb stb .leave)
  | loopBodyHalt {funs V st c post body cv st1 Vb stb} :
      Step D funs V st (.expr c) (.eres (.vals [cv] st1)) →
      cv ≠ D.zero →
      Step D funs V st1 (.stmt (.block body)) (.sres Vb stb .halt) →
      Step D funs V st (.loop c post body) (.sres Vb stb .halt)

/-! ### The five conceptual relations, as abbreviations -/

/-- Expression evaluation (a `lit`/`var` yields one value; a call may yield several). -/
abbrev EvalExpr (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (e : Expr D.Op) (r : EResult D) : Prop :=
  Step D funs V st (.expr e) (.eres r)

/-- Argument-list evaluation (right-to-left; each argument must be single-valued). -/
abbrev EvalArgs (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (es : List (Expr D.Op)) (r : EResult D) : Prop :=
  Step D funs V st (.args es) (.eres r)

/-- Single-statement execution. -/
abbrev ExecStmt (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (s : Stmt D.Op) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.stmt s) (.sres V' st' o)

/-- Statement-sequence execution. -/
abbrev ExecStmts (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (ss : List (Stmt D.Op)) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.stmts ss) (.sres V' st' o)

/-- `for`-loop iteration (after `init`). -/
abbrev ExecLoop (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (c : Expr D.Op) (post body : Block D.Op)
    (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.loop c post body) (.sres V' st' o)

/-- Run a whole program (a top-level block) from an initial state with empty environments. -/
def Run (D : Dialect) [DecidableEq D.Value] (prog : Block D.Op) (st0 : D.State)
    (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  ExecStmt D [] [] st0 (.block prog) V' st' o

end YulSemantics
