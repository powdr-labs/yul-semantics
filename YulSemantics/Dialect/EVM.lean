import Mathlib.Tactic.SplitIfs
import YulSemantics.Dialect.EVMExec

/-!
# YulSemantics.Dialect.EVM

The **metatheory** of the EVM dialect (effect-classification soundness, executable-dialect
lawfulness, `@[simp]` state-helper lemmas, and worked examples). The Mathlib-free executable
interpreter (`Op`, `stepOp`, the `evm` dialect instance, all state defs) lives in
`YulSemantics.Dialect.EVMExec`; this module imports it and adds the proofs, keeping Mathlib off
the import path of code that only needs to *run* the dialect.

## Imports

This module deliberately does **not** `import Mathlib`. Every Lean module's `initialize_*`
function calls the initializer of each module it imports, and that is a genuine symbol
reference the linker cannot discard — so a single bare `import Mathlib` anywhere in a
downstream executable's import closure keeps all ~8200 Mathlib object files alive at link
time. The only Mathlib entry point this file actually needs is the `split_ifs` tactic.
-/

namespace YulSemantics.EVM

open YulSemantics

/-- Test-only fixture for the `SELFDESTRUCT` effect guards below. -/
private def selfdestructTestState (createdThisTx : Bool) : EvmState :=
  { EvmState.init with
    env := { EvmState.init.env with
      address := 0x10
      selfBalance := 7
      createdThisTx
      balanceOf := fun address =>
        if accountKey address = accountKey 0x10 then 7
        else if accountKey address = accountKey 0x20 then 5 else 0 } }

@[simp] theorem committedState_none {st0 st' : EvmState} (h : st'.halted = none) :
    committedState st0 st' = st' := by simp [committedState, h]

/-- A committing halt commits `st'` unchanged. Not a `simp` lemma: its left-hand side
`committedState st0 st'` does not determine `k`/`data` (they appear only in the hypotheses), so
`simp` could never apply it — invoke it by name or pass it explicitly to `simp`. -/
theorem committedState_commit {st0 st' : EvmState} {k data}
    (h : st'.halted = some (k, data)) (hk : k.commits = true) :
    committedState st0 st' = st' := by simp [committedState, h, hk]

theorem committedState_rollback {st0 st' : EvmState} {k data}
    (h : st'.halted = some (k, data)) (hk : k.commits = false) :
    committedState st0 st' = { st0 with halted := st'.halted, returndata := st'.returndata } := by
  simp [committedState, h, hk]

@[simp] theorem finishCreate_returndata (st response offset size) :
    (finishCreate st response offset size).returndata = response.visibleReturnData := rfl

/-- A failed create rolls back storage to the pre-state. -/
@[simp] theorem finishCreate_failure_storage (st response offset size key)
    (h : response.created = none) :
    (finishCreate st response offset size).storage key = st.storage key := by
  simp [finishCreate, h, touchMemory]

/-- A successful create installs the response world's storage. -/
@[simp] theorem finishCreate_success_storage (st response offset size key)
    (h : response.created.isSome = true) :
    (finishCreate st response offset size).storage key = response.world.storage key := by
  simp [finishCreate, h, CallWorld.install]

/-- The creator nonce bump is committed on both the success and failure paths. -/
@[simp] theorem finishCreate_nonce (st response offset size address) :
    (finishCreate st response offset size).env.nonceOf address = response.world.nonceOf address := by
  simp only [finishCreate]
  split <;> simp [CallWorld.install]

@[simp] theorem finishCall_returndata (kind st response inputOffset inputSize outputOffset
    outputSize) :
    (finishCall kind st response inputOffset inputSize outputOffset outputSize).returndata =
      response.returndata := rfl

/-- A failed call cannot commit external or re-entrant storage changes. -/
@[simp] theorem finishCall_failure_storage (kind st response inputOffset inputSize outputOffset
    outputSize key) (h : response.success = false) :
    (finishCall kind st response inputOffset inputSize outputOffset outputSize).storage key =
      st.storage key := by
  simp [finishCall, h, touchMemory2, touchMemory]

/-- `staticcall` cannot commit external or re-entrant storage changes. -/
@[simp] theorem finishCall_static_storage (st response inputOffset inputSize outputOffset outputSize
    key) :
    (finishCall .staticcall st response inputOffset inputSize outputOffset outputSize).storage key =
      st.storage key := by
  simp [finishCall, touchMemory2, touchMemory]

/-- A successful non-static call installs the supplied post-storage. This explicitly includes
changes made by a callback into the caller. -/
@[simp] theorem finishCall_success_storage (kind st response inputOffset inputSize outputOffset
    outputSize key) (hs : response.success = true) (hk : kind ≠ .staticcall) :
    (finishCall kind st response inputOffset inputSize outputOffset outputSize).storage key =
      response.world.storage key := by
  simp [finishCall, hs, hk, CallWorld.install]

/-- The EVM executable dialect is lawful: `Builtin` and `builtinFn` agree definitionally (both are
`stepOp`). -/
theorem exec_lawful : exec.Lawful := fun _ _ _ _ => Iff.rfl

set_option linter.unusedSimpArgs false in
/-- The EVM dialect's effect flags soundly over-approximate its built-in semantics. In particular,
operations marked non-writing return the input state unchanged, and operations marked non-halting
can only produce a normal result. -/
theorem effects_sound : evm.EffectsSound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro op _
    exact exec_lawful.deterministic op
  · -- read: every `reads = false` op returns values fixed by its arguments. The `reads = true` ops
    -- are discharged by `simp [effects] at hr`; the survivors are the pure ops (`rets = f args`), the
    -- blind writers `mstore`/`mstore8`/`sstore`/`tstore` (`rets = []`; the storage writers split on
    -- the static guard, both branches with `rets = []`), and `stop`/`invalid` (never `.ok`, vacuous).
    intro op hr
    cases op <;> simp [effects] at hr
    all_goals
      intro args st1 st2 rets1 st1' rets2 st2' h1 h2
      change stepOp _ args st1 = some (.ok rets1 st1') at h1
      change stepOp _ args st2 = some (.ok rets2 st2') at h2
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, args⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1, guardStatic] <;>
        split_ifs at h1 h2 <;> simp_all
  · intro op hw
    cases op <;> simp [effects] at hw
    all_goals
      intro args st r hb
      change stepOp _ args st = some r at hb
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, args⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1] <;> subst r <;> rfl
  · intro op hh
    cases op <;> simp [effects] at hh
    all_goals
      intro args st r hb
      change stepOp _ args st = some r at hb
      rcases args with
        _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, args⟩⟩⟩⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1] <;> subst r <;> rfl

/-- The effect classification remains sound for every external call/create relation. External
operations carry no determinism, non-writing, or non-halting promise (the call/create family is
now marked `halts := true` to cover static-context write protection), so only the non-halting
*local* built-ins remain to discharge; their `Builtin` is definitionally `stepOp`. -/
theorem effects_sound_withExternal (calls : ExternalCalls) (creates : ExternalCreates) :
    (evmWithExternal calls creates).EffectsSound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro op hd
    have hlocal := effects_sound.det op hd
    cases op <;> simp [effects, Effects.top] at hd
    all_goals
      intro args st r₁ r₂ h₁ h₂
      apply hlocal args st r₁ r₂
      · simpa [evmWithExternal, builtinWithExternal] using h₁
      · simpa [evmWithExternal, builtinWithExternal] using h₂
  · -- read: none of the `reads = false` ops are external (call/create/gas all carry `reads := true`),
    -- so each survivor's `Builtin` reduces definitionally to `stepOp` and we delegate to the local
    -- `effects_sound.read`.
    intro op hr
    have hlocal := effects_sound.read op hr
    cases op <;> simp [effects, Effects.top] at hr
    all_goals
      intro args st1 st2 rets1 st1' rets2 st2' h1 h2
      apply hlocal args st1 st2 rets1 st1' rets2 st2'
      · simpa [evmWithExternal, builtinWithExternal] using h1
      · simpa [evmWithExternal, builtinWithExternal] using h2
  · intro op hw
    have hlocal := effects_sound.write op hw
    cases op <;> simp [effects, Effects.top] at hw
    all_goals
      intro args st r h
      apply hlocal args st r
      simpa [evmWithExternal, builtinWithExternal] using h
  · intro op hh
    -- After marking the static-guarded writers (`sstore`/`tstore`/`log*`) and the whole
    -- call/create family with `halts := true`, the only ops left to discharge here are the
    -- genuinely non-halting *local* built-ins, whose `Builtin` is definitionally `stepOp`.
    cases op <;> simp [effects, Effects.top] at hh
    all_goals
      intro args st r hb
      change stepOp _ args st = some r at hb
      rcases args with
        _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, args⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp_all [stepOp, un, bin, ter, rd0, rd1] <;> subst r <;> rfl

/-- Compatibility specialization for call-only clients. -/
theorem effects_sound_withCalls (external : ExternalCalls) :
    (evmWithCalls external).EffectsSound :=
  effects_sound_withExternal external ExternalCreates.none

example (x : U256) (st : EvmState) : stepOp .add [x, 0] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .mul [x, 1] st = some (.ok [x] st) := by simp [stepOp, bin]
example (x : U256) (st : EvmState) : stepOp .and [x, x] st = some (.ok [x] st) := by simp [stepOp, bin]
example (st : EvmState) : stepOp .caller [] st = some (.ok [st.env.caller] st) := by simp [stepOp, rd0]
example (st : EvmState) : stepOp .clz [0] st = some (.ok [256] st) := by simp [stepOp, un, clzVal]

/-- `extcodehash` reads through `projectedCodeHash`, tying the code hash to the account's code,
nonce, and balance rather than an unconstrained map. -/
example (st : EvmState) (a : U256) :
    stepOp .extcodehash [a] st =
      some (.ok [projectedCodeHash st.env st.env.balanceOf a] st) := by simp [stepOp, rd1]

/-- Under `ExecEnv.WF`, the `projectedCodeHash`-based `extcodehash` agrees with the raw
`extCodeHashOf` map, so routing through the derived rule loses no behavior on consistent worlds. -/
example (st : EvmState) (a : U256) (hwf : st.env.WF) :
    stepOp .extcodehash [a] st = some (.ok [st.env.extCodeHashOf a] st) := by
  simp [stepOp, rd1, hwf.1 a]

example : (effects .msize).writes = false := rfl
example : (effects .mload).writes = true := rfl
example : (effects .returndatacopy).halts = true := rfl

-- `reads` guards: a pure op and a blind writer are both `reads := false` and are proven
-- non-reading by `effects_sound.read`, even though the writer mutates state (`writes := true`).
example : (effects .add).reads = false := rfl
example : (effects .sstore).reads = false ∧ (effects .sstore).writes = true := ⟨rfl, rfl⟩
example : evm.NonReading .add := effects_sound.read .add rfl
example : evm.NonReading .sstore := effects_sound.read .sstore rfl
example : (effects .stop).writes = true := rfl
example : effects .selfdestruct =
    { deterministic := true, reads := true, writes := true, halts := true } := rfl
example : effects .gas = Effects.top := rfl

example :
    let st := finishSelfdestruct (selfdestructTestState false) 0x20
    (st.env.selfBalance, st.env.balanceOf 0x10, st.env.balanceOf 0x20,
      st.selfdestructs, st.halted) =
      (0, 0, 12, [(0x10, false)], some (.selfdestruct, [])) := by rfl

example :
    let st := finishSelfdestruct (selfdestructTestState false) 0x10
    (st.env.selfBalance, st.env.balanceOf 0x10) = (7, 7) := by rfl

example :
    let st := finishSelfdestruct (selfdestructTestState true) 0x10
    (st.env.selfBalance, st.env.balanceOf 0x10) = (0, 0) := by rfl

example (st : EvmState) (response : CallResponse) (key : U256)
    (hs : response.success = true) :
    (finishCall .call st response 0 0 0 0).storage key = response.world.storage key := by
  simp [hs]

example (st : EvmState) (response : CallResponse) (key : U256)
    (hf : response.success = false) :
    (finishCall .call st response 0 0 0 0).storage key = st.storage key := by
  simp [hf]

example (st : EvmState) (response : CallResponse) (key : U256) :
    (finishCall .staticcall st response 0 0 0 0).storage key = st.storage key := by
  simp

example (external : ExternalCalls) (st : EvmState) (response : CallResponse)
    (hstatic : st.env.static = false)
    (hresponse : external.Call
      { kind := .call, gas := 1, target := 2, value := 3, input := [] } st response) :
    (evmWithCalls external).Builtin .call [1, 2, 3, 0, 0, 0, 0] st
      (.ok [response.flag] (finishCall .call st response 0 0 0 0)) := by
  have hc : ¬ (st.env.static ∧ (3 : U256) ≠ 0) := by simp [hstatic]
  simp only [evmWithCalls, evmWithExternal, builtinWithExternal, if_neg hc]
  exact ⟨response, hresponse, rfl⟩

example (external : ExternalCalls) (st : EvmState) (g : U256) :
    (evmWithCalls external).Builtin .gas [] st (.ok [g] st) := ⟨g, rfl⟩

example (calls : ExternalCalls) (creates : ExternalCreates) (st : EvmState) (g : U256) :
    (evmWithExternal calls creates).Builtin .gas [] st (.ok [g] st) := ⟨g, rfl⟩

example (st : EvmState) : stepOp .gas [] st = none := rfl

-- `loadimmutable` reads the environment's immutable map, keyed by the name's string encoding,
-- exactly as `dataoffset`/`datasize` read the layout maps.
example (st : EvmState) (k : U256) :
    stepOp .loadimmutable [k] st = some (.ok [st.env.immutable k] st) := by
  simp [stepOp, rd1]

-- It is a *read*: the state is untouched, and two reads of the same name agree (so it may be
-- CSE'd, unlike `gas()`).
example (st : EvmState) (k : U256) (v₁ v₂ : U256)
    (h₁ : stepOp .loadimmutable [k] st = some (.ok [v₁] st))
    (h₂ : stepOp .loadimmutable [k] st = some (.ok [v₂] st)) : v₁ = v₂ := by
  simp_all

-- Wrong arity is stuck, like every other unary reader.
example (st : EvmState) : stepOp .loadimmutable [] st = none := rfl

-- The idiomatic `call(gas(), …)` pattern now has a derivation: pick the gas oracle's word, then
-- take any external response for the call it feeds.
example (external : ExternalCalls) (st : EvmState) (g : U256) (response : CallResponse)
    (hstatic : st.env.static = false)
    (hresponse : external.Call
      { kind := .call, gas := g, target := 2, value := 3, input := [] } st response) :
    (evmWithCalls external).Builtin .gas [] st (.ok [g] st) ∧
    (evmWithCalls external).Builtin .call [g, 2, 3, 0, 0, 0, 0] st
      (.ok [response.flag] (finishCall .call st response 0 0 0 0)) := by
  refine ⟨⟨g, rfl⟩, ?_⟩
  have hc : ¬ (st.env.static ∧ (3 : U256) ≠ 0) := by simp [hstatic]
  simp only [evmWithCalls, evmWithExternal, builtinWithExternal, if_neg hc]
  exact ⟨response, hresponse, rfl⟩

example (response : CreateResponse) (address : U256)
    (h : response.created = some address) : response.result = address := by
  simp [CreateResponse.result, h]

example (response : CreateResponse)
    (h : response.created = none) : response.result = 0 := by
  simp [CreateResponse.result, h]

example (st : EvmState) (response : CreateResponse) (address : U256)
    (h : response.created = some address) :
    (finishCreate st response 0 0).returndata = [] := by
  simp [CreateResponse.visibleReturnData, h]

/-- A failed create (`created = none`) rolls storage back to the pre-state: only the creator nonce
survives, exactly as CALL rolls back on failure. -/
example (st : EvmState) (response : CreateResponse) (key : U256)
    (h : response.created = none) :
    (finishCreate st response 0 0).storage key = st.storage key := by
  simp [finishCreate, h, touchMemory]

/-- A successful create installs the response world's storage. -/
example (st : EvmState) (response : CreateResponse) (key address : U256)
    (h : response.created = some address) :
    (finishCreate st response 0 0).storage key = response.world.storage key := by
  simp [finishCreate, CallWorld.install, h]

/-- The creator nonce bump is committed on both paths. -/
example (st : EvmState) (response : CreateResponse) (a : U256) :
    (finishCreate st response 0 0).env.nonceOf a = response.world.nonceOf a := by
  simp

example (creates : ExternalCreates) (st : EvmState) (response : CreateResponse)
    (hstatic : st.env.static = false)
    (hresponse : creates.Create
      { kind := .create2, value := 7, initCode := [], salt := some 11 } st response) :
    (evmWithExternal ExternalCalls.none creates).Builtin .create2 [7, 0, 0, 11] st
      (.ok [response.result] (finishCreate st response 0 0)) := by
  have hc : ¬ (st.env.static = true) := by simp [hstatic]
  simp only [evmWithExternal, builtinWithExternal, if_neg hc]
  exact ⟨response, hresponse, rfl⟩

/-- Local writes (in a non-static frame) update both the executing-account view and the global world
projection. -/
example (st : EvmState) (key value : U256) (hstatic : st.env.static = false) :
    ∃ st', stepOp .sstore [key, value] st = some (.ok [] st') ∧
      st'.storage key = value ∧ st'.env.storageOf st.env.address key = value := by
  refine ⟨{ st with
      storage := upd st.storage key value
      env := { st.env with storageOf := updAccount st.env.storageOf st.env.address key value } },
    ?_, ?_, ?_⟩
  · simp [stepOp, guardStatic, hstatic]
  · simp [upd]
  · simp [updAccount]

/-- A static frame's `sstore` halts exceptionally with `.staticViolation` and does not write. -/
example (st : EvmState) (key value : U256) (hstatic : st.env.static = true) :
    stepOp .sstore [key, value] st = some (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [stepOp, guardStatic, hstatic]

/-- A static frame's `tstore` likewise halts exceptionally. -/
example (st : EvmState) (key value : U256) (hstatic : st.env.static = true) :
    stepOp .tstore [key, value] st = some (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [stepOp, guardStatic, hstatic]

/-- A static frame's `log0` halts exceptionally. -/
example (st : EvmState) (p n : U256) (hstatic : st.env.static = true) :
    stepOp .log0 [p, n] st = some (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [stepOp, guardStatic, hstatic]

/-- A static frame's `selfdestruct` halts exceptionally (no balance transfer). -/
example (st : EvmState) (b : U256) (hstatic : st.env.static = true) :
    stepOp .selfdestruct [b] st = some (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [stepOp, guardStatic, hstatic]

/-- A static frame's value-bearing `call` halts exceptionally under `builtinWithExternal`. -/
example (calls : ExternalCalls) (creates : ExternalCreates) (st : EvmState)
    (hstatic : st.env.static = true) :
    builtinWithExternal calls creates .call [0, 0, 1, 0, 0, 0, 0] st
      (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [builtinWithExternal, hstatic]

/-- A static frame's `create` halts exceptionally under `builtinWithExternal`. -/
example (calls : ExternalCalls) (creates : ExternalCreates) (st : EvmState)
    (hstatic : st.env.static = true) :
    builtinWithExternal calls creates .create [0, 0, 0] st
      (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [builtinWithExternal, hstatic]

/-- A zero-value `call` is still permitted in a static frame (delegates to the external relation). -/
example (calls : ExternalCalls) (creates : ExternalCreates) (st : EvmState) (response : CallResponse)
    (hstatic : st.env.static = true)
    (hresponse : calls.Call
      { kind := .call, gas := 1, target := 2, value := 0,
        input := readBytes st.memory 0 0 } st response) :
    builtinWithExternal calls creates .call [1, 2, 0, 0, 0, 0, 0] st
      (.ok [response.flag] (finishCall .call st response 0 0 0 0)) := by
  simp only [builtinWithExternal, hstatic]
  refine ⟨response, hresponse, rfl⟩

/-- A value-bearing `callcode` delegates to the external relation regardless of the static flag (its
self-transfer is a no-op, so — unlike `call` — the EVM does not reject it in a static frame). The
result is the same whether or not `st.env.static` holds. -/
example (calls : ExternalCalls) (creates : ExternalCreates) (st : EvmState) (response : CallResponse)
    (hresponse : calls.Call
      { kind := .callcode, gas := 1, target := 2, value := 3,
        input := readBytes st.memory 0 0 } st response) :
    builtinWithExternal calls creates .callcode [1, 2, 3, 0, 0, 0, 0] st
      (.ok [response.flag] (finishCall .callcode st response 0 0 0 0)) := by
  simp only [builtinWithExternal]
  refine ⟨response, hresponse, rfl⟩

/-- New effect flags: the static-guarded writers now advertise possible halting. -/
example : (effects .sstore).halts = true := rfl
example : (effects .tstore).halts = true := rfl
example : (effects .log0).halts = true := rfl
example : (effects .call).halts = true := rfl
example : (effects .create).halts = true := rfl
example : (effects .sstore).writes = true := rfl

end YulSemantics.EVM
