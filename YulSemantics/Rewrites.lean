import YulSemantics.Equiv
import YulSemantics.Syntax

/-!
# YulSemantics.Rewrites

Sample **local rewrites** for the EVM dialect, proven as semantic equivalences and lifted through
the congruence lemmas of `YulSemantics.Equiv` — validating that the Phase 5 framework can carry an
optimizer's proof obligations:

* constant folding: `add(2, 3) ≈ 5`;
* algebraic identity: `add(x, 0) ≈ x` (for a variable `x`);
* a lifted statement rewrite: `sstore(0, add(x, 0)) ≈ sstore(0, x)` via congruence.

Note the shape of the identity: it is stated for a *variable* argument, not an arbitrary
expression. `add(e, 0) ≈ e` is **false** for arbitrary `e` — if `e` is a call returning two
values, the left side is stuck while the right is not. The general version needs a "single-valued
expression" premise; rewrites on variables/literals (what an optimizer's value-numbering pass
produces) avoid it.
-/

namespace YulSemantics.Rewrites

open YulSemantics EVM

/-! ### Inversion helpers for two-element EVM argument lists -/

/-- Two literal arguments always evaluate to their values, unchanged state. -/
theorem two_lits_inv {funs V st l₁ l₂ r}
    (h : EvalArgs EVM.evm funs V st [.lit l₁, .lit l₂] r) :
    r = .vals [EVM.litValue l₁, EVM.litValue l₂] st := by
  cases h with
  | argsCons h₁ h₂ =>
      cases h₂ with
      | lit =>
          cases h₁ with
          | argsCons h₃ h₄ =>
              cases h₄ with
              | lit => cases h₃ with | argsNil => rfl
  | argsRestHalt h₁ =>
      cases h₁ with
      | argsRestHalt h₃ => cases h₃
      | argsHeadHalt h₃ h₄ => cases h₄
  | argsHeadHalt h₁ h₂ => cases h₂

/-- A variable and a literal always evaluate to the variable's value and the literal, unchanged
state. -/
theorem var_lit_inv {funs V st x l r}
    (h : EvalArgs EVM.evm funs V st [.var x, .lit l] r) :
    ∃ v, VEnv.get V x = some v ∧ r = .vals [v, EVM.litValue l] st := by
  cases h with
  | argsCons h₁ h₂ =>
      cases h₂ with
      | var hv =>
          cases h₁ with
          | argsCons h₃ h₄ =>
              cases h₄ with
              | lit => cases h₃ with | argsNil => exact ⟨_, hv, rfl⟩
  | argsRestHalt h₁ =>
      cases h₁ with
      | argsRestHalt h₃ => cases h₃
      | argsHeadHalt h₃ h₄ => cases h₄
  | argsHeadHalt h₁ h₂ => cases h₂

/-! ### Constant folding: `add(2, 3) ≈ 5` -/

theorem fold_add_2_3 :
    EquivExpr EVM.evm (.builtin .add [.lit (.number 2), .lit (.number 3)]) (.lit (.number 5)) := by
  have hval : EVM.litValue (.number 2) + EVM.litValue (.number 3) = EVM.litValue (.number 5) := by
    decide
  intro funs V st r
  constructor
  · intro h
    cases h with
    | builtinOk ha hb =>
        have hr := two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [hval]
        exact Step.lit
    | builtinHalt ha hb =>
        have hr := two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
    | builtinArgsHalt ha =>
        have hr := two_lits_inv ha
        simp at hr
  · intro h
    cases h with
    | lit =>
        refine Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) ?_
        simp [EVM.stepOp, EVM.bin, hval]

/-! ### Algebraic identity: `add(x, 0) ≈ x` -/

theorem add_zero (x : Ident) :
    EquivExpr EVM.evm (.builtin .add [.var x, .lit (.number 0)]) (.var x) := by
  have hz : ∀ v : EVM.U256, v + EVM.litValue (.number 0) = v := fun v => by
    have h0 : EVM.litValue (.number 0) = 0 := by decide
    rw [h0]; exact BitVec.add_zero v
  intro funs V st r
  constructor
  · intro h
    cases h with
    | builtinOk ha hb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [hz]
        exact Step.var hv
    | builtinHalt ha hb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
    | builtinArgsHalt ha =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        simp at hr
  · intro h
    cases h with
    | var hv =>
        refine Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hv)) ?_
        simp [EVM.stepOp, EVM.bin, hz]

/-! ### Lifting through congruence: a statement-level rewrite -/

/-- The identity lifted into a statement: `sstore(0, add(x, 0)) ≈ sstore(0, x)`. Assembled purely
from the congruence lemmas plus the local rewrite. -/
theorem sstore_add_zero (x : Ident) :
    EquivStmt EVM.evm
      (.exprStmt (.builtin .sstore [.lit (.number 0), .builtin .add [.var x, .lit (.number 0)]]))
      (.exprStmt (.builtin .sstore [.lit (.number 0), .var x])) :=
  EquivStmt.exprStmt_congr
    (EquivExpr.builtin_congr EVM.Op.sstore
      (EquivArgs.of_forall₂ (.cons (EquivExpr.refl _) (.cons (add_zero x) .nil))))

/-- The same rewrite at the whole-program level, written in concrete syntax (the `x` here is the
Yul identifier `"x"`). The `hoist` side condition is `rfl` — the rewrite touches no function
definitions. -/
example :
    EquivBlock EVM.evm (yul% { sstore(0, add(x, 0)) }) (yul% { sstore(0, x) }) :=
  EquivBlock.of_forall₂ (.cons (sstore_add_zero "x") .nil) rfl

end YulSemantics.Rewrites
