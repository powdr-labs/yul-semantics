import YulSemantics.Ast
import YulSemantics.Dialect

/-!
# YulSemantics.BigStep

The **big-step relational semantics** of Yul — the ground truth (see `DESIGN.md` §2). It is an
inductive evaluation relation over an arbitrary `Dialect D`, gas-free.

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
  params : List Ident
  rets   : List Ident
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

/-! ### The evaluation / execution relations -/

mutual

/-- Evaluate a single expression to values (a `lit`/`var` yields one; a call may yield several) or a
halt, threading the machine state. -/
inductive EvalExpr (D : Dialect) :
    FunEnv D → VEnv D → D.State → Expr D.Op → EResult D → Prop where
  | lit {funs V st l} :
      EvalExpr D funs V st (.lit l) (.vals [D.litValue l] st)
  | var {funs V st x v} :
      VEnv.get V x = some v →
      EvalExpr D funs V st (.var x) (.vals [v] st)
  | builtinOk {funs V st op args argvals st1 rets st2} :
      EvalArgs D funs V st args (.vals argvals st1) →
      D.Builtin op argvals st1 (.ok rets st2) →
      EvalExpr D funs V st (.builtin op args) (.vals rets st2)
  | builtinHalt {funs V st op args argvals st1 st2} :
      EvalArgs D funs V st args (.vals argvals st1) →
      D.Builtin op argvals st1 (.halt st2) →
      EvalExpr D funs V st (.builtin op args) (.halt st2)
  | builtinArgsHalt {funs V st op args st1} :
      EvalArgs D funs V st args (.halt st1) →
      EvalExpr D funs V st (.builtin op args) (.halt st1)
  | callOk {funs V st fn args argvals st1 decl cenv Vend st2 o} :
      EvalArgs D funs V st args (.vals argvals st1) →
      lookupFun funs fn = some (decl, cenv) →
      argvals.length = decl.params.length →
      ExecStmt D cenv ((decl.params.zip argvals) ++ bindZeros D decl.rets) st1
        (.block decl.body) Vend st2 o →
      (o = .normal ∨ o = .leave) →
      EvalExpr D funs V st (.call fn args)
        (.vals (decl.rets.map (fun r => (VEnv.get Vend r).getD D.zero)) st2)
  | callHalt {funs V st fn args argvals st1 decl cenv Vend st2} :
      EvalArgs D funs V st args (.vals argvals st1) →
      lookupFun funs fn = some (decl, cenv) →
      argvals.length = decl.params.length →
      ExecStmt D cenv ((decl.params.zip argvals) ++ bindZeros D decl.rets) st1
        (.block decl.body) Vend st2 .halt →
      EvalExpr D funs V st (.call fn args) (.halt st2)
  | callArgsHalt {funs V st fn args st1} :
      EvalArgs D funs V st args (.halt st1) →
      EvalExpr D funs V st (.call fn args) (.halt st1)

/-- Evaluate an argument list right-to-left (each argument must be single-valued); collect the
values in source order. -/
inductive EvalArgs (D : Dialect) :
    FunEnv D → VEnv D → D.State → List (Expr D.Op) → EResult D → Prop where
  | nil {funs V st} :
      EvalArgs D funs V st [] (.vals [] st)
  | cons {funs V st e rest restvals st1 v st2} :
      EvalArgs D funs V st rest (.vals restvals st1) →
      EvalExpr D funs V st1 e (.vals [v] st2) →
      EvalArgs D funs V st (e :: rest) (.vals (v :: restvals) st2)
  | consRestHalt {funs V st e rest st1} :
      EvalArgs D funs V st rest (.halt st1) →
      EvalArgs D funs V st (e :: rest) (.halt st1)
  | consHeadHalt {funs V st e rest restvals st1 st2} :
      EvalArgs D funs V st rest (.vals restvals st1) →
      EvalExpr D funs V st1 e (.halt st2) →
      EvalArgs D funs V st (e :: rest) (.halt st2)

/-- Execute a single statement, threading the variable environment, state, and outcome. -/
inductive ExecStmt (D : Dialect) :
    FunEnv D → VEnv D → D.State → Stmt D.Op → VEnv D → D.State → Outcome → Prop where
  | funDef {funs V st n ps rs b} :
      ExecStmt D funs V st (.funDef n ps rs b) V st .normal
  | block {funs V st body Vb stb o} :
      ExecStmts D (hoist D body :: funs) V st body Vb stb o →
      ExecStmt D funs V st (.block body) (restore V Vb) stb o
  | letZero {funs V st vars} :
      ExecStmt D funs V st (.letDecl vars none) (bindZeros D vars ++ V) st .normal
  | letVal {funs V st vars e vals st1} :
      EvalExpr D funs V st e (.vals vals st1) →
      vals.length = vars.length →
      ExecStmt D funs V st (.letDecl vars (some e)) (vars.zip vals ++ V) st1 .normal
  | letHalt {funs V st vars e st1} :
      EvalExpr D funs V st e (.halt st1) →
      ExecStmt D funs V st (.letDecl vars (some e)) V st1 .halt
  | assignVal {funs V st vars e vals st1} :
      EvalExpr D funs V st e (.vals vals st1) →
      vals.length = vars.length →
      ExecStmt D funs V st (.assign vars e) (VEnv.setMany V vars vals) st1 .normal
  | assignHalt {funs V st vars e st1} :
      EvalExpr D funs V st e (.halt st1) →
      ExecStmt D funs V st (.assign vars e) V st1 .halt
  | exprStmt {funs V st e st1} :
      EvalExpr D funs V st e (.vals [] st1) →
      ExecStmt D funs V st (.exprStmt e) V st1 .normal
  | exprStmtHalt {funs V st e st1} :
      EvalExpr D funs V st e (.halt st1) →
      ExecStmt D funs V st (.exprStmt e) V st1 .halt
  | ifTrue {funs V st c body cv st1 V' st2 o} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) V' st2 o →
      ExecStmt D funs V st (.cond c body) V' st2 o
  | ifFalse {funs V st c body cv st1} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv = D.zero →
      ExecStmt D funs V st (.cond c body) V st1 .normal
  | ifHalt {funs V st c body st1} :
      EvalExpr D funs V st c (.halt st1) →
      ExecStmt D funs V st (.cond c body) V st1 .halt
  | switchCase {funs V st c cases dflt cv st1 l body V' st2 o} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      (l, body) ∈ cases →
      cv = D.litValue l →
      ExecStmt D funs V st1 (.block body) V' st2 o →
      ExecStmt D funs V st (.switch c cases dflt) V' st2 o
  | switchDefault {funs V st c cases dflt cv st1 V' st2 o} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      (∀ p ∈ cases, cv ≠ D.litValue p.1) →
      ExecStmt D funs V st1 (.block (dflt.getD [])) V' st2 o →
      ExecStmt D funs V st (.switch c cases dflt) V' st2 o
  | switchHalt {funs V st c cases dflt st1} :
      EvalExpr D funs V st c (.halt st1) →
      ExecStmt D funs V st (.switch c cases dflt) V st1 .halt
  | forLoop {funs V st init c post body Vinit stinit Vend stend o} :
      ExecStmts D (hoist D init :: funs) V st init Vinit stinit .normal →
      ExecLoop D (hoist D init :: funs) Vinit stinit c post body Vend stend o →
      ExecStmt D funs V st (.forLoop init c post body) (restore V Vend) stend o
  | forInitHalt {funs V st init c post body Vinit stinit} :
      ExecStmts D (hoist D init :: funs) V st init Vinit stinit .halt →
      ExecStmt D funs V st (.forLoop init c post body) (restore V Vinit) stinit .halt
  | «break» {funs V st} :
      ExecStmt D funs V st .«break» V st .«break»
  | «continue» {funs V st} :
      ExecStmt D funs V st .«continue» V st .«continue»
  | leave {funs V st} :
      ExecStmt D funs V st .leave V st .leave

/-- Execute a statement sequence, threading env/state and short-circuiting on a non-`normal`
outcome. -/
inductive ExecStmts (D : Dialect) :
    FunEnv D → VEnv D → D.State → List (Stmt D.Op) → VEnv D → D.State → Outcome → Prop where
  | nil {funs V st} :
      ExecStmts D funs V st [] V st .normal
  | consNormal {funs V st s rest V1 st1 V2 st2 o} :
      ExecStmt D funs V st s V1 st1 .normal →
      ExecStmts D funs V1 st1 rest V2 st2 o →
      ExecStmts D funs V st (s :: rest) V2 st2 o
  | consStop {funs V st s rest V1 st1 o} :
      ExecStmt D funs V st s V1 st1 o →
      o ≠ .normal →
      ExecStmts D funs V st (s :: rest) V1 st1 o

/-- Execute a `for`-loop's iteration (condition-check, body, post, repeat) after its `init` block
has run. `funs`/`V`/`st` carry the loop scope; the outcome is `normal` (loop finished or `break`),
`leave`, or `halt`. -/
inductive ExecLoop (D : Dialect) :
    FunEnv D → VEnv D → D.State → Expr D.Op → Block D.Op → Block D.Op →
    VEnv D → D.State → Outcome → Prop where
  | done {funs V st c post body cv st1} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv = D.zero →
      ExecLoop D funs V st c post body V st1 .normal
  | condHalt {funs V st c post body st1} :
      EvalExpr D funs V st c (.halt st1) →
      ExecLoop D funs V st c post body V st1 .halt
  | step {funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) Vb stb ob →
      (ob = .normal ∨ ob = .«continue») →
      ExecStmt D funs Vb stb (.block post) Vp stp .normal →
      ExecLoop D funs Vp stp c post body Vend stend o →
      ExecLoop D funs V st c post body Vend stend o
  | stepPostHalt {funs V st c post body cv st1 Vb stb ob Vp stp} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) Vb stb ob →
      (ob = .normal ∨ ob = .«continue») →
      ExecStmt D funs Vb stb (.block post) Vp stp .halt →
      ExecLoop D funs V st c post body Vp stp .halt
  | brk {funs V st c post body cv st1 Vb stb} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) Vb stb .«break» →
      ExecLoop D funs V st c post body Vb stb .normal
  | lv {funs V st c post body cv st1 Vb stb} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) Vb stb .leave →
      ExecLoop D funs V st c post body Vb stb .leave
  | bodyHalt {funs V st c post body cv st1 Vb stb} :
      EvalExpr D funs V st c (.vals [cv] st1) →
      cv ≠ D.zero →
      ExecStmt D funs V st1 (.block body) Vb stb .halt →
      ExecLoop D funs V st c post body Vb stb .halt

end

/-- Run a whole program (a top-level block) from an initial state with empty environments. -/
def Run (D : Dialect) (prog : Block D.Op) (st0 : D.State)
    (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  ExecStmt D [] [] st0 (.block prog) V' st' o

-- TODO(next): the determinism lemma. The relation is deterministic on well-formed programs given
-- `D.Deterministic` for every built-in and distinct switch-case values; the proof is by mutual
-- induction over the relations.

end YulSemantics
