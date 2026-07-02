import YulSemantics.Optimizer
import YulSemantics.Rewrites

/-!
# YulSemantics.Passes

The first end-to-end **verified optimization pass**: constant folding (plus an algebraic identity)
for the EVM dialect, built with the `CorrectPass`/rewriter machinery of `YulSemantics.Optimizer`.

The entire proof surface of the pass is `foldRule_sound` — one `EquivExpr` lemma per rule arm; the
traversal, congruence lifting, and pipeline composition are inherited from the engine theorem.
-/

namespace YulSemantics.Passes

open YulSemantics EVM

/-! ### Value-level facts -/

/-- Constant folding of `add` at the word level, for arbitrary numeric literals. -/
theorem litValue_add (a b : Nat) :
    EVM.litValue (.number a) + EVM.litValue (.number b)
      = EVM.litValue (.number ((a + b) % 2 ^ 256)) := by
  simp only [EVM.litValue]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ### The rule -/

/-- The local rewrite rule: fold `add` of two numeric literals; simplify `add(x, 0)` for a
variable `x`. Declines everywhere else. -/
def foldRule : Expr EVM.Op → Option (Expr EVM.Op)
  | .builtin .add [.lit (.number a), .lit (.number b)] =>
      some (.lit (.number ((a + b) % 2 ^ 256)))
  | .builtin .add [.var x, .lit (.number 0)] => some (.var x)
  | _ => none

/-- General constant folding of `add`: the `Rewrites.fold_add_2_3` sample, for arbitrary numeric
literals. -/
theorem fold_add (a b : Nat) :
    EquivExpr EVM.evm (.builtin .add [.lit (.number a), .lit (.number b)])
      (.lit (.number ((a + b) % 2 ^ 256))) := by
  intro funs V st r
  constructor
  · intro h
    cases h with
    | builtinOk ha hb =>
        have hr := Rewrites.two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [litValue_add]
        exact Step.lit
    | builtinHalt ha hb =>
        have hr := Rewrites.two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
    | builtinArgsHalt ha =>
        have hr := Rewrites.two_lits_inv ha
        simp at hr
  · intro h
    cases h with
    | lit =>
        refine Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) ?_
        simp [EVM.stepOp, EVM.bin, litValue_add]

/-- Soundness of the rule: one small equivalence lemma per arm. -/
theorem foldRule_sound : RuleSound EVM.evm foldRule := by
  intro e e' h
  unfold foldRule at h
  split at h
  · injection h with h; subst h; exact fold_add _ _
  · injection h with h; subst h; exact Rewrites.add_zero _
  · exact absurd h (by simp)

/-! ### The pass -/

/-- The verified constant-folding pass. -/
def constantFolding : CorrectPass EVM.evm := CorrectPass.ofRule foldRule foldRule_sound

/-! ### The pass at work -/

/-- Folding computes: `add(2, 3)` becomes `5`. -/
example : constantFolding.run (yul% { sstore(0, add(2, 3)) }) = (yul% { sstore(0, 5) }) := rfl

/-- The identity fires: `add(x, 0)` becomes `x`. -/
example : constantFolding.run (yul% { sstore(0, add(x, 0)) }) = (yul% { sstore(0, x) }) := rfl

/-- Rewriting is bottom-up, so folding cascades in one traversal:
`add(add(1, 2), add(x, 0))` becomes `add(3, x)`. -/
example :
    constantFolding.run (yul% { sstore(0, add(add(1, 2), add(x, 0))) })
      = (yul% { sstore(0, add(3, x)) }) := rfl

/-- The engine rewrites under control flow (here: a loop condition and body). -/
example :
    constantFolding.run
        (yul% { for { let i := 0 } lt(i, add(5, 5)) { i := add(i, 1) } { sstore(i, add(2, 3)) } })
      = (yul% { for { let i := 0 } lt(i, 10) { i := add(i, 1) } { sstore(i, 5) } }) := rfl

/-- The behavioral guarantee, for free from the pass's correctness. -/
example {st0 V' st' o} :
    Run EVM.evm (yul% { sstore(0, add(2, 3)) }) st0 V' st' o ↔
      Run EVM.evm (yul% { sstore(0, 5) }) st0 V' st' o :=
  constantFolding.run_iff _

end YulSemantics.Passes
