import YulSemantics.Determinism

/-!
# YulSemantics.Observation

**Frame-boundary observation for the EVM dialect.**

The `Step` judgment (`YulSemantics.BigStep`) is shared between the top-level frame and every
sub-frame, so — by design — it does *not* itself roll back the storage/transient/log/balance/
selfdestruct effects that a frame accumulated before it halted. A callee's rollback is applied by
`finishCall` when control returns to the caller; the **top-level** frame has no such caller, so its
rollback is applied here, at the *observation* boundary.

`EVM.committedState st0 st'` (see `YulSemantics.Dialect.EVM`) is that boundary map: it commits `st'`
on a normal/`stop`/`return`/`selfdestruct` halt and rolls everything back to `st0` (keeping only the
outcome marker and exposed return data) on a `revert`/`invalid`/`invalidMemoryAccess`/
`staticViolation` halt. This file lifts it to whole-program runs (`RunCommitted`): the state a
caller/transaction actually observes.

## Why observe here

Raw `Run` compares the *entire* `Step` state exactly, so it distinguishes
`{ sstore(0,1); revert(0,0) }` from `{ revert(0,0) }`: the first leaves `storage[0] = 1` in the raw
halt state. That is faithful to `Step`, but it is *not* what an EVM caller observes — a reverted
frame discards its storage write. `RunCommitted` restores that observation. The payoff for
optimization — a dead store before a revert is observationally invisible — is proven downstream in
the compiler repository, whose optimizer owns the dead-effect reasoning.
-/

namespace YulSemantics

open EVM

/-- A top-level **observed** run of an EVM program: it runs the program (`Run`) and then applies the
frame-boundary commit/rollback (`committedState`) to obtain the caller/transaction-observable state.

With whole-program determinism (`EVM.run_det`) this relation is functional — see
`RunCommitted.det`. -/
def RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm)
    (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run EVM.evm prog st0 V' st' o ∧ stObs = committedState st0 st'

/-- `RunCommitted` is functional: `committedState` is a function of the (unique, by `EVM.run_det`)
raw run result. -/
theorem RunCommitted.det {prog st0 V₁ s₁ o₁ V₂ s₂ o₂}
    (h₁ : RunCommitted prog st0 V₁ s₁ o₁) (h₂ : RunCommitted prog st0 V₂ s₂ o₂) :
    V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  obtain ⟨st₁', hrun₁, rfl⟩ := h₁
  obtain ⟨st₂', hrun₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun₁ hrun₂
  exact ⟨rfl, rfl, rfl⟩

end YulSemantics
