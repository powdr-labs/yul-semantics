# Audit: yul-semantics — soundness & spec holes (2026-07-15)

## Summary

The formalization is careful and genuinely proven: **no `sorry`, `admit`, `axiom`, `unsafe`, or `partial def` anywhere**; determinism is a real full rule-induction; adequacy (soundness + completeness) is proven under a definitional `Lawful` hypothesis; the local arithmetic/bitwise/memory opcodes are modeled correctly on the edge cases checked (`sdiv(-2^255,-1)`, `smod=srem`, `signextend`, `byte`, shifts ≥ 256, `addmod/mulmod`, `returndatacopy` bounds, big-endian load/store, `msize` rounding, `clz`). The CALL/CREATE open-world boundary design is thoughtful.

Three high-severity gaps let real EVM behavior escape the spec, plus several medium/low items. Findings are ranked.

---

## HIGH — 1. `revert` / exceptional halt does not roll back the frame's own state

`stepOp` for `.revert`, `.invalid`, and the `returndatacopy` OOB path only set `st.halted`; they leave every prior `sstore`/`tstore`/`log`/balance/`selfdestruct` effect in `st` (EVM.lean:731-796). In real EVM, a reverted or exceptionally-halted frame discards **all** its state changes — only return-data (and consumed gas) survive.

- **Already handled:** the *call boundary* is correct — `finishCall` on `success = false` keeps the caller's pre-call storage and discards `response.world` (proven: `finishCall_failure_storage`). Nested reverts compose correctly.
- **Where it bites:** the **top-level `Run`** and the **equivalence notion**. `EquivStmt`/`EquivBlock` compare the entire `st'` exactly (Equiv.lean:59), and `Run` returns the un-rolled-back `st'`. So `Run p st0` for a reverting `p` yields a state that does not match EVM; DESIGN.md lists "resulting storage/logs" as the observable with no revert caveat; the future compiler theorem ("EVM ends in a state matching σ'") becomes false/unprovable for reverting frames unless the match relation special-cases revert; and valid EVM optimizations (dead `sstore` before a `revert`) are not provable.

Conservative for the current narrow Yul→Yul rewrites (never unsound there), but a real faithfulness hole for the compiler direction and the "resulting storage" observable.

**Fix:** roll back persistent state on `revert`/`invalid`/exceptional halt (snapshot at frame entry), or define an explicit `Behavior`/observation function that projects a reverting run to `(revert, returndata)`, prove equivalence over that, and document it.

## HIGH — 2. `gas()` is *stuck*, not the nondeterministic oracle the design promises

DESIGN.md says `gas()` is "modeled as an oracle / non-deterministic read." The implementation does the opposite: `stepOp .gas = none` (EVM.lean:780-781) and `builtinWithExternal` has no rule for `.gas`, so `Builtin .gas args st r ↔ False`. Any program calling `gas()` has no derivation — stuck, not nondeterministic.

Because the idiomatic external call is `call(gas(), addr, …)`, the ubiquitous real-world call pattern is unanalyzable — the CALL machinery the recent PRs added can't be exercised on realistic code.

**Fix:** add a nondeterministic rule to `builtinWithExternal` (or a gas-oracle relation parameter): `gas()` returns an arbitrary `U256`, state unchanged. `effects .gas = top` already permits it; determinism already excludes `evm` from the open-world dialect.

## HIGH — 3. Static-call context is not modeled

There is no `static` flag in `ExecEnv`/the frame. In a static context, `sstore`, `tstore`, `log0-4`, `create`/`create2`, `selfdestruct`, and `call` with nonzero value must cause an exceptional halt; here they always succeed. The staticcall callee boundary is handled (rollback in `finishCall`), but the current frame has no way to know it is itself static. Subtly unsound even for Yul→Yul (removing a dead `sstore` turns exceptional-halt into normal under a static context).

**Fix:** add `static : Bool` to the environment; make the writing built-ins halt exceptionally when set; thread it through the staticcall boundary.

---

## MEDIUM

**4. CREATE boundary has no structural rollback guarantee (asymmetric with CALL).** `finishCreate` always installs `response.world` on every path (EVM.lean:544). All correctness of a failed creation is pushed entirely into the `ExternalCreates` relation — no analogue of `finishCall_failure_storage`, and `ExternalCreates.any` permits any world on any path. Consider splitting the response into a committed part (nonce bump) and a tentative part (committed only on success), mirroring CALL.

**5. `selfdestructs` list is lossy post-EIP-6780.** `finishSelfdestruct` appends `self` unconditionally (EVM.lean:346), even when `createdThisTx = false` (Cancun does not delete the account then). Record the `createdThisTx` bit alongside, or only schedule when set.

**6. No account-state consistency invariants across the abstract env maps.** `balanceOf`/`nonceOf`/`extCodeOf`/`extCodeHashOf`/`storageOf` are independent, so the spec admits worlds EVM never has (e.g. `extcodehash(a) ≠ keccak(code(a))`). `projectedCodeHash` encodes the right rule but is used only in selfdestruct — the `extcodehash` opcode reads the raw map (EVM.lean:770). Consider a well-formedness predicate on `ExecEnv` and routing `extcodehash` through `projectedCodeHash`.

## LOW / NOTES

**7. Meta-theory scope.** Determinism, the interpreter, and adequacy cover only the closed-world local `evm`. The open-world `evmWithExternal` (calls/creates) has no interpreter, no adequacy, and determinism does not apply. The README should say this explicitly.

**8. `reads` effect flag is unproven and oddly assigned.** `EffectsSound` proves `det`/`write`/`halt` but not `reads` (deferred). Writers like `mstore`/`sstore` carry `reads := false`; there is no `NonReading` predicate. Latent risk for any future CSE/reordering pass that leans on `reads`/`Effects.pure`.

**9. `exp` via `a.toNat ^ b.toNat`** — intentional: the spec is math only; the executable impl is expected to do square-and-multiply. Left as-is by design.

**10. Argument-order TODO is resolvable.** BigStep.lean:45 flags "right-to-left … TODO: confirm." The Yul spec mandates right-to-left evaluation, and the semantics matches it. The TODO can be removed.

---

## Verified-correct (spot checks)
Arithmetic/signed edge cases, shift saturation, big-endian memory, `msize` rounding, `returndatacopy` OOB→exceptional halt, `selfdestruct` EIP-6780 self-beneficiary split, CALL success/failure/static rollback lemmas, the equivalence congruence lemmas. These are solid.
