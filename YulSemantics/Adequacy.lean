import YulSemantics.BigStep
import YulSemantics.Interp
import YulSemantics.Dialect.EVM

/-!
# YulSemantics.Adequacy

The fuel-indexed interpreter (`YulSemantics.Interp`) is **adequate** for the big-step relational
semantics (`YulSemantics.BigStep`), under the hypothesis that the executable dialect is `Lawful`
(its `builtinFn` agrees exactly with the relational `Builtin`; definitional for the EVM dialect):

* **Soundness** (`Interp.sound_all` and its projections): if the interpreter returns `.ok` at any
  fuel, the corresponding big-step derivation exists. By induction on fuel.
* **Completeness** (`Interp.complete`): if a big-step derivation exists, the interpreter returns
  the same result at every sufficiently large fuel. By rule induction on the derivation (fuel
  monotonicity is embedded in the "for all `n ≥ N`" statement, so no separate monotonicity lemma
  over the interpreter's structure is needed).
* **Adequacy** (`Interp.adequacy`, `Interp.run_adequacy`): the two combined, as an `iff`.

Together with determinism (`YulSemantics.Determinism`), this pins the interpreter down as *the*
computational content of the semantics: it returns `.ok r` for some fuel iff `r` is the unique
big-step result.
-/

namespace YulSemantics

namespace Interp

variable {E : ExecDialect} [DecidableEq E.toDialect.Value]

/-- Soundness of the interpreter, jointly for the five syntactic classes, by induction on fuel:
whenever the interpreter answers `.ok`, the big-step judgment holds. -/
theorem sound_all (hE : E.Lawful) : ∀ n : Nat,
    (∀ funs V st e r, evalExpr E n funs V st e = .ok r →
        EvalExpr E.toDialect funs V st e r) ∧
    (∀ funs V st es r, evalArgs E n funs V st es = .ok r →
        EvalArgs E.toDialect funs V st es r) ∧
    (∀ funs V st s V' st' o, execStmt E n funs V st s = .ok (V', st', o) →
        ExecStmt E.toDialect funs V st s V' st' o) ∧
    (∀ funs V st ss V' st' o, execStmts E n funs V st ss = .ok (V', st', o) →
        ExecStmts E.toDialect funs V st ss V' st' o) ∧
    (∀ funs V st c post body V' st' o, execLoop E n funs V st c post body = .ok (V', st', o) →
        ExecLoop E.toDialect funs V st c post body V' st' o) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro funs V st e r h; simp [evalExpr] at h
      · intro funs V st es r h; simp [evalArgs] at h
      · intro funs V st s V' st' o h; simp [execStmt] at h
      · intro funs V st ss V' st' o h; simp [execStmts] at h
      · intro funs V st c post body V' st' o h; simp [execLoop] at h
  | succ n ih =>
      obtain ⟨ihE, ihA, ihS, ihSS, ihL⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      /- ### Expressions -/
      · intro funs V st e r h
        cases e with
        | lit l =>
            simp only [evalExpr] at h
            injection h with h; subst h
            exact Step.lit
        | var x =>
            cases hv : VEnv.get V x with
            | none => simp [evalExpr, hv] at h
            | some v =>
                simp only [evalExpr, hv] at h
                injection h with h; subst h
                exact Step.var hv
        | builtin op args =>
            simp only [evalExpr] at h
            cases hA : evalArgs E n funs V st args with
            | stuck => simp [hA] at h
            | outOfFuel => simp [hA] at h
            | ok a =>
                cases a with
                | vals argvals st1 =>
                    cases hB : E.builtinFn op argvals st1 with
                    | none => simp [hA, hB] at h
                    | some br =>
                        cases br with
                        | ok rets st2 =>
                            simp [hA, hB] at h; subst h
                            exact Step.builtinOk (ihA _ _ _ _ _ hA) ((hE _ _ _ _).mpr hB)
                        | halt st2 =>
                            simp [hA, hB] at h; subst h
                            exact Step.builtinHalt (ihA _ _ _ _ _ hA) ((hE _ _ _ _).mpr hB)
                | halt st1 =>
                    simp [hA] at h; subst h
                    exact Step.builtinArgsHalt (ihA _ _ _ _ _ hA)
        | call fn args =>
            simp only [evalExpr] at h
            cases hA : evalArgs E n funs V st args with
            | stuck => simp [hA] at h
            | outOfFuel => simp [hA] at h
            | ok a =>
                cases a with
                | vals argvals st1 =>
                    cases hL : lookupFun funs fn with
                    | none => simp [hA, hL] at h
                    | some p =>
                        obtain ⟨decl, cenv⟩ := p
                        by_cases hlen : argvals.length = decl.params.length
                        · cases hS : execStmt E n cenv
                              (decl.params.zip argvals ++ bindZeros E.toDialect decl.rets) st1
                              (.block decl.body) with
                          | stuck => simp [hA, hL, hlen, hS] at h
                          | outOfFuel => simp [hA, hL, hlen, hS] at h
                          | ok x =>
                              obtain ⟨Vend, st2, o⟩ := x
                              cases o with
                              | normal =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callOk (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS) (Or.inl rfl)
                              | leave =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callOk (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS) (Or.inr rfl)
                              | halt =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callHalt (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS)
                              | «break» => simp [hA, hL, hlen, hS] at h
                              | «continue» => simp [hA, hL, hlen, hS] at h
                        · simp [hA, hL, hlen] at h
                | halt st1 =>
                    simp [hA] at h; subst h
                    exact Step.callArgsHalt (ihA _ _ _ _ _ hA)
      /- ### Argument lists -/
      · intro funs V st es r h
        cases es with
        | nil =>
            simp only [evalArgs] at h
            injection h with h; subst h
            exact Step.argsNil
        | cons e rest =>
            simp only [evalArgs] at h
            cases hR : evalArgs E n funs V st rest with
            | stuck => simp [hR] at h
            | outOfFuel => simp [hR] at h
            | ok a =>
                cases a with
                | vals restvals st1 =>
                    cases hH : evalExpr E n funs V st1 e with
                    | stuck => simp [hR, hH] at h
                    | outOfFuel => simp [hR, hH] at h
                    | ok b =>
                        cases b with
                        | vals vs st2 =>
                            cases vs with
                            | nil => simp [hR, hH] at h
                            | cons v vs' =>
                                cases vs' with
                                | nil =>
                                    simp [hR, hH] at h; subst h
                                    exact Step.argsCons (ihA _ _ _ _ _ hR) (ihE _ _ _ _ _ hH)
                                | cons _ _ => simp [hR, hH] at h
                        | halt st2 =>
                            simp [hR, hH] at h; subst h
                            exact Step.argsHeadHalt (ihA _ _ _ _ _ hR) (ihE _ _ _ _ _ hH)
                | halt st1 =>
                    simp [hR] at h; subst h
                    exact Step.argsRestHalt (ihA _ _ _ _ _ hR)
      /- ### Statements -/
      · intro funs V st s V' st' o h
        cases s with
        | funDef n' ps rs b =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.funDef
        | block body =>
            simp only [execStmt] at h
            cases hB : execStmts E n (hoist E.toDialect body :: funs) V st body with
            | stuck => simp [hB] at h
            | outOfFuel => simp [hB] at h
            | ok x =>
                obtain ⟨Vb, stb, ob⟩ := x
                simp [hB] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Step.block (ihSS _ _ _ _ _ _ _ hB)
        | letDecl vars val =>
            cases val with
            | none =>
                simp only [execStmt] at h
                injection h with h
                obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
                exact Step.letZero
            | some e =>
                simp only [execStmt] at h
                cases hEv : evalExpr E n funs V st e with
                | stuck => simp [hEv] at h
                | outOfFuel => simp [hEv] at h
                | ok a =>
                    cases a with
                    | vals vals st1 =>
                        by_cases hlen : vals.length = vars.length
                        · simp [hEv, hlen] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact Step.letVal (ihE _ _ _ _ _ hEv) hlen
                        · simp [hEv, hlen] at h
                    | halt st1 =>
                        simp [hEv] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.letHalt (ihE _ _ _ _ _ hEv)
        | assign vars e =>
            simp only [execStmt] at h
            cases hEv : evalExpr E n funs V st e with
            | stuck => simp [hEv] at h
            | outOfFuel => simp [hEv] at h
            | ok a =>
                cases a with
                | vals vals st1 =>
                    by_cases hlen : vals.length = vars.length
                    · simp [hEv, hlen] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      exact Step.assignVal (ihE _ _ _ _ _ hEv) hlen
                    · simp [hEv, hlen] at h
                | halt st1 =>
                    simp [hEv] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.assignHalt (ihE _ _ _ _ _ hEv)
        | exprStmt e =>
            simp only [execStmt] at h
            cases hEv : evalExpr E n funs V st e with
            | stuck => simp [hEv] at h
            | outOfFuel => simp [hEv] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil =>
                        simp [hEv] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.exprStmt (ihE _ _ _ _ _ hEv)
                    | cons _ _ => simp [hEv] at h
                | halt st1 =>
                    simp [hEv] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.exprStmtHalt (ihE _ _ _ _ _ hEv)
        | cond c body =>
            simp only [execStmt] at h
            cases hC : evalExpr E n funs V st c with
            | stuck => simp [hC] at h
            | outOfFuel => simp [hC] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil => simp [hC] at h
                    | cons cv vs' =>
                        cases vs' with
                        | cons _ _ => simp [hC] at h
                        | nil =>
                            by_cases hz : cv = E.toDialect.zero
                            · simp [hC, hz] at h
                              obtain ⟨rfl, rfl, rfl⟩ := h
                              exact Step.ifFalse (ihE _ _ _ _ _ hC) hz
                            · simp only [hC, Result.ok_bind] at h
                              rw [if_neg hz] at h
                              exact Step.ifTrue (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ h)
                | halt st1 =>
                    simp [hC] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.ifHalt (ihE _ _ _ _ _ hC)
        | switch c cases' dflt =>
            simp only [execStmt] at h
            cases hC : evalExpr E n funs V st c with
            | stuck => simp [hC] at h
            | outOfFuel => simp [hC] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil => simp [hC] at h
                    | cons cv vs' =>
                        cases vs' with
                        | cons _ _ => simp [hC] at h
                        | nil =>
                            simp only [hC, Result.ok_bind] at h
                            exact Step.switchExec (ihE _ _ _ _ _ hC) (ihS _ _ _ _ _ _ _ h)
                | halt st1 =>
                    simp [hC] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.switchHalt (ihE _ _ _ _ _ hC)
        | forLoop init c post body =>
            simp only [execStmt] at h
            cases hI : execStmts E n (hoist E.toDialect init :: funs) V st init with
            | stuck => simp [hI] at h
            | outOfFuel => simp [hI] at h
            | ok x =>
                obtain ⟨Vinit, stinit, oinit⟩ := x
                cases oinit with
                | normal =>
                    cases hLp : execLoop E n (hoist E.toDialect init :: funs) Vinit stinit
                        c post body with
                    | stuck => simp [hI, hLp] at h
                    | outOfFuel => simp [hI, hLp] at h
                    | ok y =>
                        obtain ⟨Vend, stend, o2⟩ := y
                        simp [hI, hLp] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.forLoop (ihSS _ _ _ _ _ _ _ hI) (ihL _ _ _ _ _ _ _ _ _ hLp)
                | halt =>
                    simp [hI] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.forInitHalt (ihSS _ _ _ _ _ _ _ hI)
                | «break» => simp [hI] at h
                | «continue» => simp [hI] at h
                | leave => simp [hI] at h
        | «break» =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.«break»
        | «continue» =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.«continue»
        | leave =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.leave
      /- ### Statement sequences -/
      · intro funs V st ss V' st' o h
        cases ss with
        | nil =>
            simp only [execStmts] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.seqNil
        | cons s rest =>
            simp only [execStmts] at h
            cases hS : execStmt E n funs V st s with
            | stuck => simp [hS] at h
            | outOfFuel => simp [hS] at h
            | ok x =>
                obtain ⟨V1, st1, o1⟩ := x
                cases o1 with
                | normal =>
                    simp only [hS, Result.ok_bind] at h
                    exact Step.seqCons (ihS _ _ _ _ _ _ _ hS) (ihSS _ _ _ _ _ _ _ h)
                | «break» =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | «continue» =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | leave =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | halt =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
      /- ### Loop iteration -/
      · intro funs V st c post body V' st' o h
        simp only [execLoop] at h
        cases hC : evalExpr E n funs V st c with
        | stuck => simp [hC] at h
        | outOfFuel => simp [hC] at h
        | ok a =>
            cases a with
            | vals vs st1 =>
                cases vs with
                | nil => simp [hC] at h
                | cons cv vs' =>
                    cases vs' with
                    | cons _ _ => simp [hC] at h
                    | nil =>
                        by_cases hz : cv = E.toDialect.zero
                        · simp [hC, hz] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact Step.loopDone (ihE _ _ _ _ _ hC) hz
                        · cases hB : execStmt E n funs V st1 (.block body) with
                          | stuck => simp [hC, hz, hB] at h
                          | outOfFuel => simp [hC, hz, hB] at h
                          | ok x =>
                              obtain ⟨Vb, stb, ob⟩ := x
                              cases ob with
                              | normal =>
                                  cases hP : execStmt E n funs Vb stb (.block post) with
                                  | stuck => simp [hC, hz, hB, hP] at h
                                  | outOfFuel => simp [hC, hz, hB, hP] at h
                                  | ok y =>
                                      obtain ⟨Vp, stp, op⟩ := y
                                      cases op with
                                      | normal =>
                                          simp only [hC, Result.ok_bind] at h
                                          rw [if_neg hz] at h
                                          simp only [hB, Result.ok_bind, hP] at h
                                          exact Step.loopStep (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inl rfl)
                                            (ihS _ _ _ _ _ _ _ hP) (ihL _ _ _ _ _ _ _ _ _ h)
                                      | halt =>
                                          simp [hC, hz, hB, hP] at h
                                          obtain ⟨rfl, rfl, rfl⟩ := h
                                          exact Step.loopPostHalt (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inl rfl)
                                            (ihS _ _ _ _ _ _ _ hP)
                                      | «break» => simp [hC, hz, hB, hP] at h
                                      | «continue» => simp [hC, hz, hB, hP] at h
                                      | leave => simp [hC, hz, hB, hP] at h
                              | «continue» =>
                                  cases hP : execStmt E n funs Vb stb (.block post) with
                                  | stuck => simp [hC, hz, hB, hP] at h
                                  | outOfFuel => simp [hC, hz, hB, hP] at h
                                  | ok y =>
                                      obtain ⟨Vp, stp, op⟩ := y
                                      cases op with
                                      | normal =>
                                          simp only [hC, Result.ok_bind] at h
                                          rw [if_neg hz] at h
                                          simp only [hB, Result.ok_bind, hP] at h
                                          exact Step.loopStep (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inr rfl)
                                            (ihS _ _ _ _ _ _ _ hP) (ihL _ _ _ _ _ _ _ _ _ h)
                                      | halt =>
                                          simp [hC, hz, hB, hP] at h
                                          obtain ⟨rfl, rfl, rfl⟩ := h
                                          exact Step.loopPostHalt (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inr rfl)
                                            (ihS _ _ _ _ _ _ _ hP)
                                      | «break» => simp [hC, hz, hB, hP] at h
                                      | «continue» => simp [hC, hz, hB, hP] at h
                                      | leave => simp [hC, hz, hB, hP] at h
                              | «break» =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopBreak (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ hB)
                              | leave =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopLeave (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ hB)
                              | halt =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopBodyHalt (ihE _ _ _ _ _ hC) hz
                                    (ihS _ _ _ _ _ _ _ hB)
            | halt st1 =>
                simp [hC] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Step.loopCondHalt (ihE _ _ _ _ _ hC)

/-- Soundness for whole-program runs: an interpreter `.ok` at any fuel yields a big-step run. -/
theorem run_sound (hE : E.Lawful) {n prog st0 V' st' o}
    (h : Interp.run E n prog st0 = .ok (V', st', o)) :
    Run E.toDialect prog st0 V' st' o :=
  (sound_all hE n).2.2.1 _ _ _ _ _ _ _ h

/-- "The interpreter, at fuel `n`, returns exactly `res` for `code`" — the interpreter-side
counterpart of `Step`, used to state completeness/adequacy uniformly over the five syntactic
classes. Mismatched code/result classes are `False`. -/
def InterpOk (E : ExecDialect) [DecidableEq E.toDialect.Value] (n : Nat)
    (funs : FunEnv E.toDialect) (V : VEnv E.toDialect) (st : E.toDialect.State) :
    Code E.toDialect.Op → Res E.toDialect → Prop
  | .expr e, .eres r => evalExpr E n funs V st e = .ok r
  | .args es, .eres r => evalArgs E n funs V st es = .ok r
  | .stmt s, .sres V' st' o => execStmt E n funs V st s = .ok (V', st', o)
  | .stmts ss, .sres V' st' o => execStmts E n funs V st ss = .ok (V', st', o)
  | .loop c post body, .sres V' st' o => execLoop E n funs V st c post body = .ok (V', st', o)
  | _, _ => False

/-- Completeness of the interpreter: a big-step derivation is reproduced by the interpreter at
every sufficiently large fuel. By rule induction on the derivation; the "for all `n ≥ N`" form
embeds fuel monotonicity, so no separate monotonicity lemma is needed. -/
theorem complete (hE : E.Lawful) {funs V st code res}
    (h : Step E.toDialect funs V st code res) :
    ∃ N, ∀ n, N ≤ n → InterpOk E n funs V st code res := by
  induction h with
  /- ### Expressions -/
  | lit =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr]
  | var hv =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, hv]
  | builtinOk ha hb iha =>
      obtain ⟨N₁, h₁⟩ := iha
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, h₁ k (by omega), (hE _ _ _ _).mp hb]
  | builtinHalt ha hb iha =>
      obtain ⟨N₁, h₁⟩ := iha
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, h₁ k (by omega), (hE _ _ _ _).mp hb]
  | builtinArgsHalt ha iha =>
      obtain ⟨N₁, h₁⟩ := iha
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, h₁ k (by omega)]
  | callOk ha hl hlen hbody ho iha ihbody =>
      obtain ⟨N₁, h₁⟩ := iha
      obtain ⟨N₂, h₂⟩ := ihbody
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [InterpOk]
      rcases ho with rfl | rfl <;>
        simp [evalExpr, h₁ k (by omega), h₂ k (by omega), hl, hlen]
  | callHalt ha hl hlen hbody iha ihbody =>
      obtain ⟨N₁, h₁⟩ := iha
      obtain ⟨N₂, h₂⟩ := ihbody
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, h₁ k (by omega), h₂ k (by omega), hl, hlen]
  | callArgsHalt ha iha =>
      obtain ⟨N₁, h₁⟩ := iha
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalExpr, h₁ k (by omega)]
  /- ### Argument lists -/
  | argsNil =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalArgs]
  | argsCons ha he iha ihe =>
      obtain ⟨N₁, h₁⟩ := iha
      obtain ⟨N₂, h₂⟩ := ihe
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalArgs, h₁ k (by omega), h₂ k (by omega)]
  | argsRestHalt ha iha =>
      obtain ⟨N₁, h₁⟩ := iha
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalArgs, h₁ k (by omega)]
  | argsHeadHalt ha he iha ihe =>
      obtain ⟨N₁, h₁⟩ := iha
      obtain ⟨N₂, h₂⟩ := ihe
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, evalArgs, h₁ k (by omega), h₂ k (by omega)]
  /- ### Statements -/
  | funDef =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt]
  | block hb ihb =>
      obtain ⟨N₁, h₁⟩ := ihb
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | letZero =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt]
  | letVal he hlen ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), hlen]
  | letHalt he ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | assignVal he hlen ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), hlen]
  | assignHalt he ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | exprStmt he ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | exprStmtHalt he ihe =>
      obtain ⟨N₁, h₁⟩ := ihe
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | ifTrue hc hnz hb ihc ihb =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), h₂ k (by omega), hnz]
  | ifFalse hc hz ihc =>
      obtain ⟨N₁, h₁⟩ := ihc
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), hz]
  | ifHalt hc ihc =>
      obtain ⟨N₁, h₁⟩ := ihc
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | switchExec hc hb ihc ihb =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), h₂ k (by omega)]
  | switchHalt hc ihc =>
      obtain ⟨N₁, h₁⟩ := ihc
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | forLoop hinit hloop ihinit ihloop =>
      obtain ⟨N₁, h₁⟩ := ihinit
      obtain ⟨N₂, h₂⟩ := ihloop
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega), h₂ k (by omega)]
  | forInitHalt hinit ihinit =>
      obtain ⟨N₁, h₁⟩ := ihinit
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt, h₁ k (by omega)]
  | «break» =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt]
  | «continue» =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt]
  | leave =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmt]
  /- ### Statement sequences -/
  | seqNil =>
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmts]
  | seqCons hs hrest ihs ihrest =>
      obtain ⟨N₁, h₁⟩ := ihs
      obtain ⟨N₂, h₂⟩ := ihrest
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execStmts, h₁ k (by omega), h₂ k (by omega)]
  | seqStop hs hne ihs =>
      rename_i o
      obtain ⟨N₁, h₁⟩ := ihs
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      cases o with
      | normal => exact absurd rfl hne
      | «break» => simp [InterpOk, execStmts, h₁ k (by omega)]
      | «continue» => simp [InterpOk, execStmts, h₁ k (by omega)]
      | leave => simp [InterpOk, execStmts, h₁ k (by omega)]
      | halt => simp [InterpOk, execStmts, h₁ k (by omega)]
  /- ### Loop iteration -/
  | loopDone hc hz ihc =>
      obtain ⟨N₁, h₁⟩ := ihc
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execLoop, h₁ k (by omega), hz]
  | loopCondHalt hc ihc =>
      obtain ⟨N₁, h₁⟩ := ihc
      simp only [InterpOk] at h₁
      refine ⟨N₁ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execLoop, h₁ k (by omega)]
  | loopStep hc hnz hb hob hp hr ihc ihb ihp ihr =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      obtain ⟨N₃, h₃⟩ := ihp
      obtain ⟨N₄, h₄⟩ := ihr
      simp only [InterpOk] at h₁ h₂ h₃ h₄
      refine ⟨N₁ + N₂ + N₃ + N₄ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [InterpOk]
      rcases hob with rfl | rfl <;>
        simp [execLoop, h₁ k (by omega), h₂ k (by omega), h₃ k (by omega), h₄ k (by omega), hnz]
  | loopPostHalt hc hnz hb hob hp ihc ihb ihp =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      obtain ⟨N₃, h₃⟩ := ihp
      simp only [InterpOk] at h₁ h₂ h₃
      refine ⟨N₁ + N₂ + N₃ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [InterpOk]
      rcases hob with rfl | rfl <;>
        simp [execLoop, h₁ k (by omega), h₂ k (by omega), h₃ k (by omega), hnz]
  | loopBreak hc hnz hb ihc ihb =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execLoop, h₁ k (by omega), h₂ k (by omega), hnz]
  | loopLeave hc hnz hb ihc ihb =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execLoop, h₁ k (by omega), h₂ k (by omega), hnz]
  | loopBodyHalt hc hnz hb ihc ihb =>
      obtain ⟨N₁, h₁⟩ := ihc
      obtain ⟨N₂, h₂⟩ := ihb
      simp only [InterpOk] at h₁ h₂
      refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [InterpOk, execLoop, h₁ k (by omega), h₂ k (by omega), hnz]

/-- **Adequacy**: the big-step judgment holds iff the interpreter succeeds at some fuel. -/
theorem adequacy (hE : E.Lawful) {funs V st code res} :
    Step E.toDialect funs V st code res ↔ ∃ n, InterpOk E n funs V st code res := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := complete hE h
    exact ⟨N, hN N le_rfl⟩
  · rintro ⟨n, h⟩
    have S := sound_all hE n
    cases code with
    | expr e =>
        cases res with
        | eres r => exact S.1 _ _ _ _ _ h
        | sres V' st' o => simp [InterpOk] at h
    | args es =>
        cases res with
        | eres r => exact S.2.1 _ _ _ _ _ h
        | sres V' st' o => simp [InterpOk] at h
    | stmt s =>
        cases res with
        | eres r => simp [InterpOk] at h
        | sres V' st' o => exact S.2.2.1 _ _ _ _ _ _ _ h
    | stmts ss =>
        cases res with
        | eres r => simp [InterpOk] at h
        | sres V' st' o => exact S.2.2.2.1 _ _ _ _ _ _ _ h
    | loop c post body =>
        cases res with
        | eres r => simp [InterpOk] at h
        | sres V' st' o => exact S.2.2.2.2 _ _ _ _ _ _ _ _ _ h

/-- **Adequacy for whole-program runs**: a big-step run exists iff the interpreter reproduces it at
some fuel. -/
theorem run_adequacy (hE : E.Lawful) {prog st0 V' st' o} :
    Run E.toDialect prog st0 V' st' o ↔
      ∃ n, Interp.run E n prog st0 = .ok (V', st', o) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := complete hE h
    have := hN N le_rfl
    exact ⟨N, by simpa [InterpOk, Interp.run] using this⟩
  · rintro ⟨n, h⟩
    exact run_sound hE h

end Interp

/-- Adequacy for the EVM dialect — hypothesis-free, since `EVM.exec` is lawful definitionally. -/
theorem EVM.run_adequacy {prog st0 V' st' o} :
    Run EVM.evm prog st0 V' st' o ↔
      ∃ n, Interp.run EVM.exec n prog st0 = .ok (V', st', o) :=
  Interp.run_adequacy EVM.exec_lawful

end YulSemantics
