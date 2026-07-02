import YulSemantics.BigStep
import YulSemantics.Dialect.EVM

/-!
# YulSemantics.Determinism

The big-step judgment is **deterministic**: a configuration evaluates to at most one result,
provided every built-in is deterministic (`∀ op, D.Deterministic op`). `switch` needs no side
condition — it is deterministic by construction (it dispatches through `selectSwitch`).

The proof is a single standard rule induction over `Step` (possible because the semantics is
encoded as one indexed judgment — see the encoding note in `YulSemantics.BigStep`), inverting the
second derivation in each case. Corollaries restate it for the five conceptual relations and for
whole-program runs, and the EVM dialect is shown to satisfy the built-in hypothesis.
-/

namespace YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- Determinism of the big-step judgment, given deterministic built-ins. -/
theorem Step.det (hdet : ∀ op, D.Deterministic op)
    {funs V st code r₁} (h₁ : Step D funs V st code r₁) :
    ∀ {r₂}, Step D funs V st code r₂ → r₁ = r₂ := by
  induction h₁ with
  /- ### Expressions -/
  | lit => intro r₂ h₂; cases h₂; rfl
  | var hv₁ =>
      intro r₂ h₂; cases h₂ with
      | var hv₂ => rw [hv₁] at hv₂; injection hv₂ with h; subst h; rfl
  | builtinOk ha₁ hb₁ iha =>
      intro r₂ h₂; cases h₂ with
      | builtinOk ha₂ hb₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          have hB := hdet _ _ _ _ _ hb₁ hb₂; injection hB with hr hs2; subst hr; subst hs2; rfl
      | builtinHalt ha₂ hb₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          have hB := hdet _ _ _ _ _ hb₁ hb₂; simp at hB
      | builtinArgsHalt ha₂ => have hA := iha ha₂; simp at hA
  | builtinHalt ha₁ hb₁ iha =>
      intro r₂ h₂; cases h₂ with
      | builtinOk ha₂ hb₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          have hB := hdet _ _ _ _ _ hb₁ hb₂; simp at hB
      | builtinHalt ha₂ hb₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          have hB := hdet _ _ _ _ _ hb₁ hb₂; injection hB with hs2; subst hs2; rfl
      | builtinArgsHalt ha₂ => have hA := iha ha₂; simp at hA
  | builtinArgsHalt ha₁ iha =>
      intro r₂ h₂; cases h₂ with
      | builtinOk ha₂ hb₂ => have hA := iha ha₂; simp at hA
      | builtinHalt ha₂ hb₂ => have hA := iha ha₂; simp at hA
      | builtinArgsHalt ha₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hs; subst hs; rfl
  | callOk ha₁ hl₁ hlen₁ hbody₁ ho₁ iha ihbody =>
      intro r₂ h₂; cases h₂ with
      | callOk ha₂ hl₂ hlen₂ hbody₂ ho₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          rw [hl₁] at hl₂; injection hl₂ with hl
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hl
          have hB := ihbody hbody₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho; rfl
      | callHalt ha₂ hl₂ hlen₂ hbody₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          rw [hl₁] at hl₂; injection hl₂ with hl
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hl
          have hB := ihbody hbody₂; injection hB with hV hs2 ho; subst ho; simp at ho₁
      | callArgsHalt ha₂ => have hA := iha ha₂; simp at hA
  | callHalt ha₁ hl₁ hlen₁ hbody₁ iha ihbody =>
      intro r₂ h₂; cases h₂ with
      | callOk ha₂ hl₂ hlen₂ hbody₂ ho₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          rw [hl₁] at hl₂; injection hl₂ with hl
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hl
          have hB := ihbody hbody₂; injection hB with hV hs2 ho
          rw [← ho] at ho₂; simp at ho₂
      | callHalt ha₂ hl₂ hlen₂ hbody₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hv hs; subst hv; subst hs
          rw [hl₁] at hl₂; injection hl₂ with hl
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hl
          have hB := ihbody hbody₂; injection hB with hV hs2 ho; subst hs2; rfl
      | callArgsHalt ha₂ => have hA := iha ha₂; simp at hA
  | callArgsHalt ha₁ iha =>
      intro r₂ h₂; cases h₂ with
      | callOk ha₂ hl₂ hlen₂ hbody₂ ho₂ => have hA := iha ha₂; simp at hA
      | callHalt ha₂ hl₂ hlen₂ hbody₂ => have hA := iha ha₂; simp at hA
      | callArgsHalt ha₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hs; subst hs; rfl
  /- ### Argument lists -/
  | argsNil => intro r₂ h₂; cases h₂; rfl
  | argsCons ha₁ he₁ iha ihe =>
      intro r₂ h₂; cases h₂ with
      | argsCons ha₂ he₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hrv hs; subst hrv; subst hs
          have hE := ihe he₂; injection hE with h2; injection h2 with hvl hs2
          injection hvl with hv _; subst hv; subst hs2; rfl
      | argsRestHalt ha₂ => have hA := iha ha₂; simp at hA
      | argsHeadHalt ha₂ he₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hrv hs; subst hs
          have hE := ihe he₂; simp at hE
  | argsRestHalt ha₁ iha =>
      intro r₂ h₂; cases h₂ with
      | argsCons ha₂ he₂ => have hA := iha ha₂; simp at hA
      | argsRestHalt ha₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hs; subst hs; rfl
      | argsHeadHalt ha₂ he₂ => have hA := iha ha₂; simp at hA
  | argsHeadHalt ha₁ he₁ iha ihe =>
      intro r₂ h₂; cases h₂ with
      | argsCons ha₂ he₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hrv hs; subst hs
          have hE := ihe he₂; simp at hE
      | argsRestHalt ha₂ => have hA := iha ha₂; simp at hA
      | argsHeadHalt ha₂ he₂ =>
          have hA := iha ha₂; injection hA with h; injection h with hrv hs; subst hs
          have hE := ihe he₂; injection hE with h2; injection h2 with hs2; subst hs2; rfl
  /- ### Statements -/
  | funDef => intro r₂ h₂; cases h₂; rfl
  | block hb₁ ihb =>
      intro r₂ h₂; cases h₂ with
      | block hb₂ =>
          have hB := ihb hb₂; injection hB with hV hs ho; subst hV; subst hs; subst ho; rfl
  | letZero => intro r₂ h₂; cases h₂; rfl
  | letVal he₁ hlen₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | letVal he₂ hlen₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hv hs; subst hv; subst hs; rfl
      | letHalt he₂ => have hE := ihe he₂; simp at hE
  | letHalt he₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | letVal he₂ hlen₂ => have hE := ihe he₂; simp at hE
      | letHalt he₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hs; subst hs; rfl
  | assignVal he₁ hlen₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | assignVal he₂ hlen₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hv hs; subst hv; subst hs; rfl
      | assignHalt he₂ => have hE := ihe he₂; simp at hE
  | assignHalt he₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | assignVal he₂ hlen₂ => have hE := ihe he₂; simp at hE
      | assignHalt he₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hs; subst hs; rfl
  | exprStmt he₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | exprStmt he₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hv hs; subst hs; rfl
      | exprStmtHalt he₂ => have hE := ihe he₂; simp at hE
  | exprStmtHalt he₁ ihe =>
      intro r₂ h₂; cases h₂ with
      | exprStmt he₂ => have hE := ihe he₂; simp at hE
      | exprStmtHalt he₂ =>
          have hE := ihe he₂; injection hE with h; injection h with hs; subst hs; rfl
  | ifTrue hc₁ hnz₁ hb₁ ihc ihb =>
      intro r₂ h₂; cases h₂ with
      | ifTrue hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho; rfl
      | ifFalse hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | ifHalt hc₂ => have hC := ihc hc₂; simp at hC
  | ifFalse hc₁ hz₁ ihc =>
      intro r₂ h₂; cases h₂ with
      | ifTrue hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
      | ifFalse hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs; subst hs; rfl
      | ifHalt hc₂ => have hC := ihc hc₂; simp at hC
  | ifHalt hc₁ ihc =>
      intro r₂ h₂; cases h₂ with
      | ifTrue hc₂ hnz₂ hb₂ => have hC := ihc hc₂; simp at hC
      | ifFalse hc₂ hz₂ => have hC := ihc hc₂; simp at hC
      | ifHalt hc₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hs; subst hs; rfl
  | switchExec hc₁ hb₁ ihc ihb =>
      intro r₂ h₂; cases h₂ with
      | switchExec hc₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho; rfl
      | switchHalt hc₂ => have hC := ihc hc₂; simp at hC
  | switchHalt hc₁ ihc =>
      intro r₂ h₂; cases h₂ with
      | switchExec hc₂ hb₂ => have hC := ihc hc₂; simp at hC
      | switchHalt hc₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hs; subst hs; rfl
  | forLoop hinit₁ hloop₁ ihinit ihloop =>
      intro r₂ h₂; cases h₂ with
      | forLoop hinit₂ hloop₂ =>
          have hI := ihinit hinit₂; injection hI with hV hs ho; subst hV; subst hs
          have hL := ihloop hloop₂; injection hL with hV2 hs2 ho2; subst hV2; subst hs2; subst ho2; rfl
      | forInitHalt hinit₂ =>
          have hI := ihinit hinit₂; injection hI with hV hs ho; simp at ho
  | forInitHalt hinit₁ ihinit =>
      intro r₂ h₂; cases h₂ with
      | forLoop hinit₂ hloop₂ =>
          have hI := ihinit hinit₂; injection hI with hV hs ho; simp at ho
      | forInitHalt hinit₂ =>
          have hI := ihinit hinit₂; injection hI with hV hs ho; subst hV; subst hs; rfl
  | «break» => intro r₂ h₂; cases h₂; rfl
  | «continue» => intro r₂ h₂; cases h₂; rfl
  | leave => intro r₂ h₂; cases h₂; rfl
  /- ### Statement sequences -/
  | seqNil => intro r₂ h₂; cases h₂; rfl
  | seqCons hs₁ hrest₁ ihs ihrest =>
      intro r₂ h₂; cases h₂ with
      | seqCons hs₂ hrest₂ =>
          have hS := ihs hs₂; injection hS with hV hst ho; subst hV; subst hst
          exact ihrest hrest₂
      | seqStop hs₂ hne₂ =>
          have hS := ihs hs₂; injection hS with hV hst ho; exact absurd ho.symm hne₂
  | seqStop hs₁ hne₁ ihs =>
      intro r₂ h₂; cases h₂ with
      | seqCons hs₂ hrest₂ =>
          have hS := ihs hs₂; injection hS with hV hst ho; exact absurd ho hne₁
      | seqStop hs₂ hne₂ =>
          have hS := ihs hs₂; injection hS with hV hst ho; subst hV; subst hst; subst ho; rfl
  /- ### Loop iteration -/
  | loopDone hc₁ hz₁ ihc =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs; subst hs; rfl
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₁ hnz₂
  | loopCondHalt hc₁ ihc =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ => have hC := ihc hc₂; simp at hC
      | loopCondHalt hc₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hs; subst hs; rfl
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ => have hC := ihc hc₂; simp at hC
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ => have hC := ihc hc₂; simp at hC
      | loopBreak hc₂ hnz₂ hb₂ => have hC := ihc hc₂; simp at hC
      | loopLeave hc₂ hnz₂ hb₂ => have hC := ihc hc₂; simp at hC
      | loopBodyHalt hc₂ hnz₂ hb₂ => have hC := ihc hc₂; simp at hC
  | loopStep hc₁ hnz₁ hb₁ hob₁ hp₁ hr₁ ihc ihb ihp ihr =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho
          have hP := ihp hp₂; injection hP with hV3 hs3 _; subst hV3; subst hs3
          exact ihr hr₂
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho
          have hP := ihp hp₂; injection hP with hV3 hs3 ho3; simp at ho3
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
  | loopPostHalt hc₁ hnz₁ hb₁ hob₁ hp₁ ihc ihb ihp =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho
          have hP := ihp hp₂; injection hP with hV3 hs3 ho3; simp at ho3
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; subst ho
          have hP := ihp hp₂; injection hP with hV3 hs3 _; subst hV3; subst hs3; rfl
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst ho; simp at hob₁
  | loopBreak hc₁ hnz₁ hb₁ ihc ihb =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; rfl
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
  | loopLeave hc₁ hnz₁ hb₁ ihc ihb =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; rfl
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
  | loopBodyHalt hc₁ hnz₁ hb₁ ihc ihb =>
      intro r₂ h₂; cases h₂ with
      | loopDone hc₂ hz₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; exact absurd hz₂ hnz₁
      | loopCondHalt hc₂ => have hC := ihc hc₂; simp at hC
      | loopStep hc₂ hnz₂ hb₂ hob₂ hp₂ hr₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopPostHalt hc₂ hnz₂ hb₂ hob₂ hp₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; rw [← ho] at hob₂; simp at hob₂
      | loopBreak hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
      | loopLeave hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; simp at ho
      | loopBodyHalt hc₂ hnz₂ hb₂ =>
          have hC := ihc hc₂; injection hC with h; injection h with hl hs
          injection hl with hcv _; subst hcv; subst hs
          have hB := ihb hb₂; injection hB with hV hs2 ho; subst hV; subst hs2; rfl

/-! ### Corollaries for the five conceptual relations -/

/-- Determinism of expression evaluation. -/
theorem EvalExpr.det (hdet : ∀ op, D.Deterministic op) {funs V st e r₁ r₂}
    (h₁ : EvalExpr D funs V st e r₁) (h₂ : EvalExpr D funs V st e r₂) : r₁ = r₂ := by
  have h := Step.det hdet h₁ h₂; injection h

/-- Determinism of argument-list evaluation. -/
theorem EvalArgs.det (hdet : ∀ op, D.Deterministic op) {funs V st es r₁ r₂}
    (h₁ : EvalArgs D funs V st es r₁) (h₂ : EvalArgs D funs V st es r₂) : r₁ = r₂ := by
  have h := Step.det hdet h₁ h₂; injection h

/-- Determinism of statement execution. -/
theorem ExecStmt.det (hdet : ∀ op, D.Deterministic op) {funs V st s V₁ st₁ o₁ V₂ st₂ o₂}
    (h₁ : ExecStmt D funs V st s V₁ st₁ o₁) (h₂ : ExecStmt D funs V st s V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ := by
  have h := Step.det hdet h₁ h₂; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩

/-- Determinism of statement-sequence execution. -/
theorem ExecStmts.det (hdet : ∀ op, D.Deterministic op) {funs V st ss V₁ st₁ o₁ V₂ st₂ o₂}
    (h₁ : ExecStmts D funs V st ss V₁ st₁ o₁) (h₂ : ExecStmts D funs V st ss V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ := by
  have h := Step.det hdet h₁ h₂; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩

/-- Determinism of whole-program execution. -/
theorem Run.det (hdet : ∀ op, D.Deterministic op) {prog st0 V₁ st₁ o₁ V₂ st₂ o₂}
    (h₁ : Run D prog st0 V₁ st₁ o₁) (h₂ : Run D prog st0 V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  ExecStmt.det hdet h₁ h₂

/-! ### The EVM dialect satisfies the hypothesis -/

/-- Every EVM built-in is deterministic: `Builtin` is defined by the function `stepOp`. -/
theorem EVM.evm_deterministic (op : EVM.Op) : EVM.evm.Deterministic op := by
  intro args st r₁ r₂ h₁ h₂
  have h₁' : EVM.stepOp op args st = some r₁ := h₁
  have h₂' : EVM.stepOp op args st = some r₂ := h₂
  rw [h₁'] at h₂'
  exact Option.some.inj h₂'

/-- Whole-program determinism for the EVM dialect. -/
theorem EVM.run_det {prog st0 V₁ st₁ o₁ V₂ st₂ o₂}
    (h₁ : Run EVM.evm prog st0 V₁ st₁ o₁) (h₂ : Run EVM.evm prog st0 V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  Run.det EVM.evm_deterministic h₁ h₂

end YulSemantics
