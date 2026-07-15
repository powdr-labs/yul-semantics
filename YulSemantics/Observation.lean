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
outcome marker and exposed return data) on a `revert`/`invalid`/`invalidMemoryAccess` halt. This
file lifts it to whole-program runs (`RunCommitted`) and proves the payoff the raw exact-state
semantics cannot: a **dead store before a revert is observationally invisible**.

## What `EquivStmt`/`Run` alone cannot see

`EquivStmt`/`EquivBlock` compare the *entire* `Step` state exactly. Under them,
`{ sstore(0,1); revert(0,0) }` and `{ revert(0,0) }` are **not** equivalent: the first leaves
`storage[0] = 1` in the raw halt state, the second does not. That is faithful to `Step`, but it is
*not* what an EVM caller observes — a reverted frame discards its storage write. `committedState`
restores that observation, and `deadStore_revert_obs_eq` proves the two programs are equal *as
observed*.
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

/-! ### Payoff: a dead `sstore` before a `revert` is observationally invisible -/

/-- `{ sstore(0, 1); revert(0, 0) }` — a storage write immediately shadowed by a revert. -/
def deadStoreRevert : Block EVM.Op :=
  [ .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)]),
    .exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)]) ]

/-- `{ revert(0, 0) }` — the bare revert. -/
def bareRevert : Block EVM.Op :=
  [ .exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)]) ]

/-- The dead-store program runs (raw, exact-state) to a `revert` halt, and its committed observation
rolls every effect back to `st0` with only the `revert` marker set. The raw result state — left
implicit — still carries `storage[0] = 1`; `committedState` is what discards it. -/
private theorem run_dead (st0 : EvmState) (hstatic : st0.env.static = false) :
    ∃ st', Run EVM.evm deadStoreRevert st0 [] st' .halt ∧
      committedState st0 st' = { st0 with halted := some (.revert, []) } := by
  -- With a non-static frame the guarded `sstore` takes its write branch; pin its result state
  -- explicitly so the run's final state stays concrete.
  have hss : evm.Builtin .sstore [evm.litValue (.number 0), evm.litValue (.number 1)] st0
      (.ok [] { st0 with
        storage := upd st0.storage (evm.litValue (.number 0)) (evm.litValue (.number 1)),
        env := { st0.env with
          storageOf := updAccount st0.env.storageOf st0.env.address
            (evm.litValue (.number 0)) (evm.litValue (.number 1)) } }) := by
    show stepOp .sstore _ st0 = some _
    simp [stepOp, guardStatic, hstatic]
  have hrun : Run EVM.evm deadStoreRevert st0 [] _ .halt :=
    Step.block (Step.seqCons
      (Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) hss))
      (Step.seqStop
        (Step.exprStmtHalt (Step.builtinHalt
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
        (by decide)))
  exact ⟨_, hrun, rfl⟩

/-- The bare revert runs to the same committed observation from `st0`. -/
private theorem run_bare (st0 : EvmState) :
    ∃ st', Run EVM.evm bareRevert st0 [] st' .halt ∧
      committedState st0 st' = { st0 with halted := some (.revert, []) } := by
  have hrun : Run EVM.evm bareRevert st0 [] _ .halt :=
    Step.block (Step.seqStop
      (Step.exprStmtHalt (Step.builtinHalt
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
      (by decide))
  exact ⟨_, hrun, rfl⟩

/-- Both programs observe the same canonical committed state: `st0` with only the `revert` marker
set (all world changes discarded, no return data). -/
theorem deadStoreRevert_committed (st0 : EvmState) (hstatic : st0.env.static = false) :
    RunCommitted deadStoreRevert st0 [] { st0 with halted := some (.revert, []) } .halt := by
  obtain ⟨st', hrun, heq⟩ := run_dead st0 hstatic
  exact ⟨st', hrun, heq.symm⟩

theorem bareRevert_committed (st0 : EvmState) :
    RunCommitted bareRevert st0 [] { st0 with halted := some (.revert, []) } .halt := by
  obtain ⟨st', hrun, heq⟩ := run_bare st0
  exact ⟨st', hrun, heq.symm⟩

/-- **The general theorem.** From every *non-static* initial state `st0`, the dead-store program and
the bare revert have identical observed (committed) runs. In particular the shadowed `sstore(0, 1)`
is invisible at the frame boundary — the raw exact-state relations (`EquivBlock`, which compare the
full `Step` state) cannot prove this, because they see the un-rolled-back storage write. Proven
relationally via whole-program determinism (`EVM.run_det`), quantified over all non-static `st0`.

The `st0.env.static = false` hypothesis is essential and faithful: under a `STATICCALL` context the
two programs genuinely differ — `sstore` itself halts with `.invalid` (exceptional), so the
dead-store program observes an `.invalid` halt while the bare revert observes `.revert`. -/
theorem deadStore_revert_obs_eq (st0 : EvmState) (hstatic : st0.env.static = false)
    (V' : VEnv EVM.evm) (stObs : EvmState) (o : Outcome) :
    RunCommitted deadStoreRevert st0 V' stObs o ↔ RunCommitted bareRevert st0 V' stObs o := by
  obtain ⟨sd, hd, hde⟩ := run_dead st0 hstatic
  obtain ⟨sb, hb, hbe⟩ := run_bare st0
  constructor
  · rintro ⟨st', hrun, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun hd
    exact ⟨sb, hb, by rw [hde, hbe]⟩
  · rintro ⟨st', hrun, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun hb
    exact ⟨sd, hd, by rw [hbe, hde]⟩

/-! ### Concrete demonstration

The raw run keeps the dead write (`storage[0] = 1`); the committed observation rolls it back
(`storage[0] = 0`, as in the initial state). -/

example :
    ∃ st', Run EVM.evm deadStoreRevert EvmState.init [] st' .halt ∧
      st'.storage 0 = 1 ∧
      (committedState EvmState.init st').storage 0 = 0 := by
  have hrun : Run EVM.evm deadStoreRevert EvmState.init [] _ .halt :=
    Step.block (Step.seqCons
      (Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
      (Step.seqStop
        (Step.exprStmtHalt (Step.builtinHalt
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
        (by decide)))
  exact ⟨_, hrun, by decide, by decide⟩

end YulSemantics
