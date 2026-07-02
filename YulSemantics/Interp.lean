import YulSemantics.BigStep

/-!
# YulSemantics.Interp

A total, fuel-indexed **executable interpreter** over an `ExecDialect`. It mirrors the big-step
judgment of `YulSemantics.BigStep`, which remains the ground truth (`DESIGN.md` §2); the interpreter
is a derived, runnable view, proven **adequate** (sound and complete) for the judgment in
`YulSemantics.Adequacy`, under the `ExecDialect.Lawful` hypothesis (definitional for the EVM
dialect). Determinism of the judgment is proven in `YulSemantics.Determinism`.

Fuel bounds *all* recursion (not just calls/loops), so a terminating program is interpreted for
some sufficiently large fuel — the natural "∃ fuel" adequacy statement. `Result` distinguishes a
genuine stuck configuration (ill-formed: unbound variable, arity mismatch, `break` outside a loop,
non-single-valued argument, …) from running `outOfFuel`.

Switch/condition branching needs decidable equality on values (`[DecidableEq D.Value]`), which the
relation avoids by using propositional equality.
-/

namespace YulSemantics

/-- The result of interpretation: a value, a genuinely stuck configuration, or fuel exhaustion. -/
inductive Result (α : Type)
  | ok (a : α)
  | stuck
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

namespace Result

/-- Monadic bind: `stuck`/`outOfFuel` short-circuit. -/
@[inline] def bind {α β : Type} : Result α → (α → Result β) → Result β
  | .ok a,      f => f a
  | .stuck,     _ => .stuck
  | .outOfFuel, _ => .outOfFuel

/-- Map over a successful result. -/
@[inline] def map {α β : Type} (f : α → β) : Result α → Result β
  | .ok a      => .ok (f a)
  | .stuck     => .stuck
  | .outOfFuel => .outOfFuel

instance : Monad Result where
  pure := .ok
  bind := Result.bind

@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Result β) :
    (Result.ok a >>= f) = f a := rfl
@[simp] theorem stuck_bind {α β : Type} (f : α → Result β) :
    ((Result.stuck : Result α) >>= f) = Result.stuck := rfl
@[simp] theorem outOfFuel_bind {α β : Type} (f : α → Result β) :
    ((Result.outOfFuel : Result α) >>= f) = Result.outOfFuel := rfl

end Result

namespace Interp

variable (E : ExecDialect) [DecidableEq E.toDialect.Value]

/-- The triple threaded by statement execution. -/
abbrev SResult := VEnv E.toDialect × E.toDialect.State × Outcome

mutual

/-- Evaluate an expression to values (or a halt), threading state; fuel-bounded. -/
def evalExpr (fuel : Nat) (funs : FunEnv E.toDialect) (V : VEnv E.toDialect)
    (st : E.toDialect.State) (e : Expr E.toDialect.Op) : Result (EResult E.toDialect) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 =>
    match e with
    | .lit l => .ok (.vals [E.litValue l] st)
    | .var x =>
        match VEnv.get V x with
        | some v => .ok (.vals [v] st)
        | none   => .stuck
    | .builtin op args => do
        match ← evalArgs n funs V st args with
        | .vals argvals st1 =>
            match E.builtinFn op argvals st1 with
            | some (.ok rets st2) => .ok (.vals rets st2)
            | some (.halt st2)    => .ok (.halt st2)
            | none                => .stuck
        | .halt st1 => .ok (.halt st1)
    | .call fn args => do
        match ← evalArgs n funs V st args with
        | .vals argvals st1 =>
            match lookupFun funs fn with
            | some (decl, cenv) =>
                if argvals.length = decl.params.length then do
                  let V0 := decl.params.zip argvals ++ bindZeros E.toDialect decl.rets
                  match ← execStmt n cenv V0 st1 (.block decl.body) with
                  | (Vend, st2, .normal) | (Vend, st2, .leave) =>
                      .ok (.vals (decl.rets.map (fun r => (VEnv.get Vend r).getD E.toDialect.zero)) st2)
                  | (_, st2, .halt) => .ok (.halt st2)
                  | (_, _, _)       => .stuck
                else .stuck
            | none => .stuck
        | .halt st1 => .ok (.halt st1)

/-- Evaluate an argument list right-to-left; each argument must be single-valued. -/
def evalArgs (fuel : Nat) (funs : FunEnv E.toDialect) (V : VEnv E.toDialect)
    (st : E.toDialect.State) (args : List (Expr E.toDialect.Op)) : Result (EResult E.toDialect) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 =>
    match args with
    | [] => .ok (.vals [] st)
    | e :: rest => do
        match ← evalArgs n funs V st rest with
        | .vals restvals st1 => do
            match ← evalExpr n funs V st1 e with
            | .vals [v] st2 => .ok (.vals (v :: restvals) st2)
            | .vals _ _     => .stuck
            | .halt st2     => .ok (.halt st2)
        | .halt st1 => .ok (.halt st1)

/-- Execute a single statement. -/
def execStmt (fuel : Nat) (funs : FunEnv E.toDialect) (V : VEnv E.toDialect)
    (st : E.toDialect.State) (s : Stmt E.toDialect.Op) : Result (SResult E) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 =>
    match s with
    | .funDef .. => .ok (V, st, .normal)
    | .block body => do
        let (Vb, stb, o) ← execStmts n (hoist E.toDialect body :: funs) V st body
        .ok (restore V Vb, stb, o)
    | .letDecl vars none => .ok (bindZeros E.toDialect vars ++ V, st, .normal)
    | .letDecl vars (some e) => do
        match ← evalExpr n funs V st e with
        | .vals vals st1 =>
            if vals.length = vars.length then .ok (vars.zip vals ++ V, st1, .normal) else .stuck
        | .halt st1 => .ok (V, st1, .halt)
    | .assign vars e => do
        match ← evalExpr n funs V st e with
        | .vals vals st1 =>
            if vals.length = vars.length then .ok (VEnv.setMany V vars vals, st1, .normal) else .stuck
        | .halt st1 => .ok (V, st1, .halt)
    | .exprStmt e => do
        match ← evalExpr n funs V st e with
        | .vals [] st1 => .ok (V, st1, .normal)
        | .vals _ _    => .stuck
        | .halt st1    => .ok (V, st1, .halt)
    | .cond c body => do
        match ← evalExpr n funs V st c with
        | .vals [cv] st1 =>
            if cv = E.toDialect.zero then .ok (V, st1, .normal)
            else execStmt n funs V st1 (.block body)
        | .vals _ _ => .stuck
        | .halt st1 => .ok (V, st1, .halt)
    | .switch c cases dflt => do
        match ← evalExpr n funs V st c with
        | .vals [cv] st1 => execStmt n funs V st1 (.block (selectSwitch E.toDialect cv cases dflt))
        | .vals _ _ => .stuck
        | .halt st1 => .ok (V, st1, .halt)
    | .forLoop init c post body => do
        let (Vinit, stinit, oinit) ← execStmts n (hoist E.toDialect init :: funs) V st init
        match oinit with
        | .normal => do
            let (Vend, stend, o) ←
              execLoop n (hoist E.toDialect init :: funs) Vinit stinit c post body
            .ok (restore V Vend, stend, o)
        | .halt => .ok (restore V Vinit, stinit, .halt)
        | _     => .stuck
    | .«break»    => .ok (V, st, .«break»)
    | .«continue» => .ok (V, st, .«continue»)
    | .leave      => .ok (V, st, .leave)

/-- Execute a statement sequence, short-circuiting on a non-`normal` outcome. -/
def execStmts (fuel : Nat) (funs : FunEnv E.toDialect) (V : VEnv E.toDialect)
    (st : E.toDialect.State) (stmts : List (Stmt E.toDialect.Op)) : Result (SResult E) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 =>
    match stmts with
    | [] => .ok (V, st, .normal)
    | s :: rest => do
        let (V1, st1, o1) ← execStmt n funs V st s
        match o1 with
        | .normal => execStmts n funs V1 st1 rest
        | _       => .ok (V1, st1, o1)

/-- Execute a `for`-loop's iteration (after `init`). -/
def execLoop (fuel : Nat) (funs : FunEnv E.toDialect) (V : VEnv E.toDialect) (st : E.toDialect.State)
    (c : Expr E.toDialect.Op) (post body : Block E.toDialect.Op) : Result (SResult E) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 => do
    match ← evalExpr n funs V st c with
    | .vals [cv] st1 =>
        if cv = E.toDialect.zero then .ok (V, st1, .normal)
        else do
          let (Vb, stb, ob) ← execStmt n funs V st1 (.block body)
          match ob with
          | .normal | .«continue» => do
              let (Vp, stp, op) ← execStmt n funs Vb stb (.block post)
              match op with
              | .normal => execLoop n funs Vp stp c post body
              | .halt   => .ok (Vp, stp, .halt)
              | _       => .stuck
          | .«break» => .ok (Vb, stb, .normal)
          | .leave   => .ok (Vb, stb, .leave)
          | .halt    => .ok (Vb, stb, .halt)
    | .vals _ _ => .stuck
    | .halt st1 => .ok (V, st1, .halt)

end

/-- Run a whole program (top-level block) from an initial state with empty environments. -/
def run (fuel : Nat) (prog : Block E.toDialect.Op) (st0 : E.toDialect.State) : Result (SResult E) :=
  execStmt E fuel [] [] st0 (.block prog)

end Interp

end YulSemantics
