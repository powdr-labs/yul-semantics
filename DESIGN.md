# Yul Semantics — Design

This repository defines a formal semantics for the [Yul](https://docs.soliditylang.org/en/latest/yul.html)
intermediate language in Lean 4. It is the foundation for a separate, future project: a
**verified optimizing compiler from Yul to EVM bytecode**. That compiler will build *on top* of
this repository; the EVM bytecode semantics lives in a *different* repository and is not included
here.

Scope of this repo: **the Yul semantics only.** No compiler, no bytecode.

## Guiding decisions

### 1. Gas is not modeled

The Yul semantics is **gas-free**. There is no gas field in the machine state and no gas in the
control-flow outcome. Consequences:

- Yul→Yul optimization correctness is purely *functional equivalence* — same result, no gas
  obligation. We deliberately prove **nothing** about gas going up or down (some passes trade it).
- Gas is the optimizer's *motivation*, never a correctness obligation.

The one place gas leaks into the *language* is via built-ins, handled in the Dialect (see "Effect
classification" and "Gas" below).

Although gas costs are absent, the EVM dialect tracks the active-memory high-water mark because
`msize()` exposes it as a functional program result. Memory-touching operations update that mark;
no gas is charged for the expansion.

### 2. Ground truth is a big-step relational semantics

The canonical definition of "what a Yul program means" is an **inductive big-step (natural)
semantics** — an evaluation relation, not an executable function.

Rationale: empirical validation against `solc`'s Yul interpreter is **not** a priority for this
project, so the main advantage of an executable interpreter (differential testing) does not apply.
The relational semantics reads like a specification, is the natural object for inductive
meta-theory (logic soundness, compiler simulation), and models non-determinism natively.

An **executable fuel-indexed interpreter** is a *derived* view (`YulSemantics/Interp.lean`), built
over an `ExecDialect` (a `Dialect` plus a computable `builtinFn`). It is not itself a correctness
foundation; it is tied to the ground truth by the **adequacy** theorem (`YulSemantics/Adequacy.lean`):
the interpreter is sound at any fuel and complete at sufficiently large fuel for terminating runs.
Together with determinism, this pins the interpreter down as *the* computational content of the
semantics. It also lets us *run* programs end-to-end (see the `native_decide` tests in
`YulSemantics/Examples.lean`).

### 3. The semantics is parameterized over an abstract `Dialect`

Yul is dialect-agnostic by design: the core language (control flow, scoping, functions) is
independent of the built-in functions. We reflect this with an abstract `Dialect` providing:

- `Op` — the built-in operation type (a finite enum for the EVM dialect); the AST is parameterized
  over it (see "AST" below).
- `Value` — the value type (for the EVM dialect: `BitVec 256`).
- `State` — the machine/world state (memory, storage, environment, logs, …).
- `Builtin` — interpretation of built-in functions as a *relation*: operation + argument values +
  state ↦ result values + new state (+ possible halt). A relation, not a function, so that
  non-deterministic built-ins (`gas()`, external calls) can be modeled.
- `litValue` — interpretation of literals as values.
- effect classification of built-ins (see below).

This keeps the repository pure Yul. The compiler project instantiates the Dialect using the *real*
EVM state and opcode semantics from the other repository.

### 4. EVM dialect: values are `BitVec 256`

For the concrete EVM dialect, `Value := BitVec 256`.

Rationale: EVM word semantics *is* two's-complement bitvector arithmetic mod `2^256`. A large
fraction of opcodes are bit-oriented (`and`/`or`/`xor`/`not`/`shl`/`shr`/`sar`, and signed
`slt`/`sgt`/`sdiv`/`smod`/`signextend`). `BitVec` supports all of these natively and — crucially —
comes with `bv_decide`/`bv_omega` automation, which is exactly what the optimizer's word-level
rewrite proofs (the bulk of the future verification work, and all on the Yul side) need. `Fin`/
`ZMod` would force us to hand-define every bitwise/signed op with no bitvector automation.

**The EVM repo uses `Fin (2^256)` for words.** This is *not* a problem: in Lean core `BitVec n` is
*defined* as a one-field wrapper around `Fin (2^n)`
(`structure BitVec (w) where ofFin :: toFin : Fin (2^w)`). So `BitVec 256` and `Fin (2^256)` are the
same data; `BitVec.toFin`/`BitVec.ofFin` are inverse projections with `simp` support. The compiler's
match relation relates words by this coercion — a definitional coercion, not a real conversion. We
do **not** change the EVM repo.

### 5. Concrete-syntax DSL

A `syntax`/macro embedding lets us write real Yul concrete syntax that elaborates to the AST
(similar in spirit to EVMYulLean), so tests and examples read like Yul.

## Language model

### AST

Yul's grammar (EVM dialect) is small and fixed:

- **Expressions**: literals, identifiers, and function calls only.
- **Statements**: block, function definition (multiple returns, `-> a, b`), `let` declaration,
  assignment, `if` (no `else`), `switch`/`case`/`default`, `for { init } cond { post } { body }`,
  `break`, `continue`, `leave`, and expression-statements.
- **Objects**: named code block + sub-objects + data.

**Built-ins are a first-class enum, and the AST is parameterized over it.** A call is either a
dialect built-in (`Expr.builtin op args`, `op : Op`) or a user-defined function call
(`Expr.call fn args`, `fn : Ident`). The AST is generic in the *type* `Op` (the dialect supplies it),
so:

- the core stays **dialect-agnostic** — a generic pass has type `∀ Op, …` and *cannot* inspect
  specific built-ins beyond their `effects`, so "correct for every dialect" holds by parametricity,
  not by discipline;
- **dialect-specific** optimizations (constant folding, algebraic identities) fix `Op := EVM.Op` and
  pattern-match on it structurally (exhaustive, type-checked), with correctness proofs connecting
  `op` directly to the built-in semantics;
- name→`Op` resolution happens at parse time, sound because Yul forbids user functions from
  shadowing built-ins. User functions remain `Ident`, resolved via the environment.

```lean
inductive Expr (Op : Type)
  | lit     (l : Literal)
  | var     (x : Ident)
  | builtin (op : Op)    (args : List (Expr Op))   -- dialect built-in
  | call    (fn : Ident) (args : List (Expr Op))   -- user-defined function

inductive Stmt (Op : Type)
  | block   (body : List (Stmt Op))
  | funDef  (name : Ident) (params rets : List Ident) (body : List (Stmt Op))
  | letDecl (vars : List Ident) (val : Option (Expr Op))
  | assign  (vars : List Ident) (val : Expr Op)
  | cond    (c : Expr Op) (body : List (Stmt Op))                 -- `if`
  | switch  (c : Expr Op) (cases : List (Literal × List (Stmt Op))) (dflt : Option (List (Stmt Op)))
  | forLoop (init : List (Stmt Op)) (c : Expr Op) (post : List (Stmt Op)) (body : List (Stmt Op))
  | exprStmt (e : Expr Op)
  | «break» | «continue» | leave
```

A dialect's built-in interpretation dispatches on `Op` **`op`-first, then arity** (see
`stepOp` in `Dialect/EVM.lean`): this keeps each arm tiny so reducing a built-in on a concrete `op`
in a proof is cheap. A single flat `match` on `(op, args, state)`, or string-keyed dispatch, blows
past the reduction budget (`maxRecDepth`/heartbeats) and should be avoided.

### Control-flow outcomes

Statement execution yields not just a state but a control outcome. Non-normal outcomes propagate
through the tree and are caught at the right boundary:

```lean
inductive Outcome
  | normal
  | break | continue    -- caught by the enclosing `for`
  | leave               -- caught by the enclosing function body
  | halt                -- from halting built-ins (return/revert/stop); propagates to the top;
                        --   the payload (kind + data) lives in the machine state
```

Argument lists are evaluated **right-to-left** (Yul's specified order); values are collected in
source order.

### Scoping

Yul is lexically scoped. A block first collects its function definitions (functions may be
forward-referenced within a block), then executes its statements. The environment maps variable
names to values and function names to definitions.

### Effect classification

The `Dialect` classifies each built-in by effect — whether it is *deterministic*, *reads* state,
*writes* state, and/or *halts*. This classification is what makes optimization proofs sound
(CSE/DCE/reordering may only move or drop calls with the right effects). The EVM dialect proves that
these flags soundly over-approximate `stepOp`: deterministic operations have at most one result,
non-writing operations preserve the entire state, and non-halting operations only return normally
(`EVM.effects_sound`; `EVM.effects_sound_withExternal` for the open-world dialect).

Because static-call write protection (see below) lets the state-modifying built-ins halt when the
frame is static, and `effects` cannot observe `ExecEnv.static`, `sstore`/`tstore`/`log0`–`log4` and
the whole call/create family carry `halts := true`. This is a faithful over-approximation that
slightly weakens the non-halting guarantee for these writers — a deliberate tradeoff of modeling
static context.

(The `reads` flag is documented but its soundness is not yet machine-checked — see "What is not done,
and why".)

## EVM dialect: external calls and contract creation

External calls and contract creation use the relational dialect directly.
`EVM.evmWithExternal calls creates` takes separate `ExternalCalls` and `ExternalCreates` relations
from a request and pre-operation state to a completed response; `evmWithCalls` remains the
call-only compatibility entry point. Responses contain return data and the caller-observable
post-world, including global nonces and per-account persistent/transient storage. They may therefore
summarize arbitrarily deep execution, including nested creation and callbacks into the current
contract. Log entries carry their emitting address explicitly, so the post-world can also retain
logs from arbitrary callees and init code. The semantics itself does not assume callee or init-code
behavior. It fixes the boundary:

- caller memory is copied into the request before the external execution;
- a frame that is itself static (`ExecEnv.static`) applies EVM write protection: `sstore`, `tstore`,
  `log0`–`log4`, `selfdestruct`, `create`/`create2`, and value-bearing `call`/`callcode` halt
  exceptionally with `.invalid` instead of taking effect, while `staticcall`, `delegatecall`, and
  zero-value `call` remain permitted (`STATICCALL` sets this bit on the callee frame);
- successful non-static calls commit the supplied post-world;
- failure and `staticcall` roll back all supplied world changes;
- creation installs the committed post-world on every path (a creator nonce bump can survive failed
  deployment) and returns the created address or zero; a *failed* creation commits **only** the
  creator nonce bump, rolling everything else back, exactly as a call rolls back on failure
  (`finishCreate_failure_storage` / `finishCreate_success_storage`);
- return data is retained in full, while only its requested prefix is copied to caller memory; and
- the call expression evaluates to the EVM success word.

For `create`/`create2`, the init-code memory slice is copied into the request and expands active
memory. A successful response installs its selected address and clears returndata; failure returns
zero and may expose revert data. CREATE2 requests also carry their salt. Global nonce and storage
projections make these responses stable across every matching concrete world, including
storage-dependent callees and reentrant execution.

The executable `EVM.evm` keeps calls and creations stuck. There is deliberately no universal
executable choice for an open-world relation. Compiler correctness instead instantiates `external`
with responses realized by complete target-EVM executions. Those executions may take any number of
steps and use an arbitrarily deep call stack, so the simulation boundary does not impose a
no-reentrancy or closed-world assumption.

### `selfdestruct`

`selfdestruct` is local and terminal rather than open-world: it does not invoke unknown code. Its
executable semantics transfers the current balance, appends the executing address (together with its
`createdThisTx` bit) to the ordered destruction schedule, and halts. `ExecEnv.createdThisTx` selects
the post-Cancun behavior when the beneficiary aliases the executing address: a pre-existing account
keeps its balance, whereas an account created in this transaction burns it. Recording the bit
alongside each scheduled address keeps balance-transfer-only distinct from actual deletion. Actual
fork-dependent account deletion is deferred to transaction finalization and is intentionally outside
this frame semantics. External call and creation worlds carry newly scheduled destructions so nested
executions remain observable.

### Gas

Two built-ins interact with gas and are classified as **impure / non-deterministic** even though we
do not model gas:

- `gas()` returns *remaining* gas — a value that changes during execution. It is modeled as an
  oracle / non-deterministic read (never a constant; two `gas()` calls may differ, so they cannot be
  CSE'd). Concretely, the open-world dialects (`evmWithExternal`/`evmWithCalls`) interpret `gas()`
  via `builtinWithExternal`: it returns an *arbitrary* word and leaves the state unchanged, so
  `call(gas(), …)` — the idiomatic call pattern — is derivable. The executable reference dialect
  `evm` has no oracle, so `gas()` stays stuck there (`stepOp .gas = none`); this is why `evm` is
  deterministic while the open-world dialects are not.
- gas forwarding + failure of `call`/`callcode`/`staticcall`/`delegatecall`: external call outcomes
  are modeled by the open-world relation (they can depend on out-of-gas in the callee, which a
  gas-free model cannot itself calculate).

### Frame-boundary observation (commit vs. rollback)

`stepOp` records only *which* halt fired — its `HaltKind` and exposed return/revert data — in
`st.halted`. It deliberately does **not** undo the storage/transient/log/balance/selfdestruct
effects a frame accumulated before halting, because the `Step` judgment is shared between the
top-level frame and every sub-frame. For a **sub-frame**, `finishCall` (and `finishCreate`) already
resolve this on return: `revert`/failure roll all supplied world changes back, only return data
survives. The **top-level** frame has no caller, so its resolution happens at the *observation*
boundary instead of inside `Step`:

- `EVM.HaltKind.commits` classifies halts: `stop`/`return`/`selfdestruct` **commit** the frame's
  changes; `revert`/`invalid`/`invalidMemoryAccess` **discard** them.
- `EVM.committedState st0 st'` is the boundary map. On a committing (or absent) halt it returns `st'`
  unchanged; on a non-committing halt it rolls everything back to the frame's initial state `st0`,
  carrying over only the outcome marker (`halted`) and the exposed `returndata` — exactly what real
  EVM leaves visible to the caller/transaction.
- `EVM.RunCommitted prog st0 V' stObs o` is the observed whole-program run (`Run` followed by
  `committedState`); `RunCommitted.det` shows it is functional given `EVM.run_det`.

This is what makes dead-effect reasoning sound at the frame level. The raw exact-state relations
(`EquivStmt`/`EquivBlock`, which compare the full `Step` state) cannot equate a dead write before a
revert with the bare revert, because they see the un-rolled-back write. Observed through
`committedState` they *are* equal: `EVM.deadStore_revert_obs_eq` proves `{ sstore(0,1); revert(0,0) }`
and `{ revert(0,0) }` have identical committed runs from every non-static initial state. (The
non-static condition is essential and faithful: under `STATICCALL` the `sstore` itself halts with
`.invalid`, so the two programs genuinely differ.)

## What is proven

- **Determinism** (`YulSemantics/Determinism.lean`). `Step.det` by a single rule induction, given
  deterministic built-ins; corollaries for the five conceptual relations and whole-program runs.
  `EVM.evm_deterministic` discharges the hypothesis for the EVM dialect (`EVM.run_det`). Two design
  notes make this a standard tactic proof: (1) `switch` dispatches through `selectSwitch` (requiring
  `[DecidableEq D.Value]` on the judgment), so it is deterministic by construction; (2) the semantics
  is encoded as a **single indexed judgment** `Step` over a `Code`/`Res` sum rather than five literal
  `mutual` relations — Lean's `induction` tactic does not support mutual inductive predicates and the
  equation compiler cannot compile mutual structural recursion over them, so the single-judgment
  encoding is what makes this (and every future derivation induction) a standard `induction … with`
  proof. The five relation names survive as abbreviations with unchanged signatures.
- **Adequacy** (`YulSemantics/Adequacy.lean`). Under `ExecDialect.Lawful` (the executable `builtinFn`
  agrees exactly with the relational `Builtin`; definitional for the EVM dialect): **soundness**
  (interpreter `.ok` at any fuel ⇒ derivation; induction on fuel) and **completeness** (derivation ⇒
  interpreter `.ok` at every sufficiently large fuel; rule induction — the `∀ n ≥ N` form embeds fuel
  monotonicity, so no separate monotonicity lemma). Combined as `Interp.adequacy` /
  `Interp.run_adequacy`, instantiated hypothesis-free for EVM as `EVM.run_adequacy`.
- **Effect-classification soundness** (`EVM.effects_sound`, `EVM.effects_sound_withExternal`) — the
  `deterministic`/`writes`/`halts` flags are proven to over-approximate the built-in semantics.
- **Optimization meta-theory** (`YulSemantics/Equiv.lean`, `YulSemantics/Rewrites.lean`). Pointwise
  semantic equivalences for all five syntactic classes (`EquivExpr`/`EquivArgs`/`EquivStmt`/
  `EquivStmts`/`EquivBlock`, each an equivalence relation); behavior (`EquivBlock.run_iff`);
  **congruence lemmas** for built-in/user calls (argument lists via `Forall₂`),
  `let`/`assign`/`exprStmt`/`cond`/`switch` (labels + case blocks + default) / `forLoop`
  (cond/post/body), sequences, and blocks. Validated by sample EVM rewrites: constant folding
  `add(2,3) ≈ 5`, the identity `add(x,0) ≈ x` (stated for a *variable* — `add(e,0) ≈ e` is false for
  a multi-valued `e`, a real optimizer precondition surfaced by the proofs), and that identity lifted
  through congruence to `sstore(0, add(x,0)) ≈ sstore(0, x)` at statement and whole-program (DSL)
  level.
- **Frame-boundary observation** (`YulSemantics/Observation.lean`) — `committedState`, `RunCommitted`
  (functional via `RunCommitted.det`), and `deadStore_revert_obs_eq`.
- **Objects** (`YulSemantics/Object.lean`, `YulSemantics/ObjectRun.lean`) — a layout-consistency
  predicate relating a compiler's byte layout to an object, and a symbolic proof that the canonical
  constructor (`datacopy`/`return`) returns a data segment's bytes.

### Meta-theory scope (which guarantees apply to which dialect)

The determinism lemma, the fuel-indexed interpreter, and the adequacy theorem are all stated for the
**closed-world local dialect `EVM.evm`**. They do **not** apply to the **open-world
`EVM.evmWithExternal` (call/create)**: that dialect is relational and may be non-deterministic (the
environment picks the external response), so it is not covered by determinism; and because there is
no universal executable choice for the open-world relation, it has neither an interpreter nor an
adequacy result — the executable dialect leaves `gas()` and the whole call/create family stuck. The
one meta-theoretic property that *is* proven for the open world is effect-classification soundness
(`EVM.effects_sound_withExternal`). Consequently, programs that call `gas()` or perform external
calls/creations are outside the determinism and adequacy guarantees.

## What is not done, and why

- **Yul→EVM compiler correctness** — out of scope for this repo (it lives in the separate compiler
  project); the target is described under "Toward Yul→EVM compiler correctness" below.
- **Inlining / function-body congruence.** There is no `funDef`-body congruence yet: rewriting inside
  a function *body* changes the `FDecl` stored by block-hoisting, so relating the two programs needs a
  relation on function environments ("environments with pointwise-equivalent bodies") threaded through
  the judgment. That machinery belongs with function-level optimizations (inlining) and is deferred.
  Relatedly, block congruence carries a `hoist`-agreement side condition (`rfl` for rewrites that do
  not touch top-level `funDef` statements).
- **`reads`-flag soundness.** `EffectsSound` proves the `deterministic`/`writes`/`halts` clauses; a
  machine-checked soundness for `reads` (result independent of the unread part of the state) needs a
  notion of state observation / read footprint, and is deferred. The flag is documented and currently
  unused by any proof.
- **Account-map consistency.** The abstract world maps (`balanceOf`/`nonceOf`/`extCodeOf`/
  `extCodeHashOf`/`storageOf`) are independent; the intended cross-map invariants (e.g. `extcodehash`
  = keccak of code for non-empty accounts, zero for empty ones) are captured by an optional
  `ExecEnv.WF` predicate available to downstream proofs, not globally enforced. `extcodehash` itself
  is computed through `projectedCodeHash` so it is internally consistent with code/nonce/balance.
- **Program logic (Hoare / separation).** An optional convenience layer, deferred until needed — see
  below.
- **Divergence reasoning.** Deferred indefinitely — not needed for the main compiler theorem (see
  below).
- **Gas.** Not modeled by design (§1). Within-frame out-of-gas is not expressible; out-of-gas in a
  callee is subsumed by the open-world call relation.

## Toward Yul→EVM compiler correctness (future, separate repo)

Because the EVM semantics **tracks gas fully**, the EVM machine always terminates (normal halt or
out-of-gas). Two consequences:

- **No divergence machinery needed on the Yul side.** There is nothing to "preserve" about diverging
  sources on a target that cannot diverge. Big-step ground truth suffices; no small-step or
  coinductive Yul semantics is required for the main theorem.
- The correctness theorem is a **conditional-on-gas forward simulation**, proven by induction on the
  Yul big-step derivation:

  > If Yul `p ⇓ (outcome, σ')` (terminating), then from a matching EVM state with gas `g`, the
  > compiled code either out-of-gas-reverts, or (for sufficient `g`) terminates in an EVM state
  > matching `σ'` with the **same functional observable**.

  The "sufficient gas" caveat is safe, not a hole: out-of-gas **rolls back the frame**, so
  insufficient gas yields a clean revert, never a partial/corrupt committed state. Gas is threaded
  through the induction (each instruction decrements a known amount; a terminating derivation ⇒
  bounded total gas), so no explicit closed-form gas bound is needed.

- **Gas lives only in the EVM machine.** The Yul Dialect stays gas-free; the match relation
  *projects gas away*. Built-in ↔ opcode correspondence reads: "same effect on the non-gas part; the
  opcode additionally decrements gas." Words are related by the `BitVec`/`Fin` coercion (§4).

- An *optional* stronger claim — "a diverging source only ever out-of-gas-reverts, never fabricates a
  real return" — is the only thing that would ever need divergence reasoning, and is deferred
  indefinitely.

## Program logic (optional layer)

A Hoare / separation logic can be layered on top of the relational semantics, with two Yul-specific
features, and is deferred until needed:

- **Outcome-indexed postconditions**: a triple carries one postcondition per `Outcome`
  (`normal`/`break`/`continue`/`leave`/`halt`), as in program logics for languages with
  `break`/`return`/exceptions.
- **Separation logic** for the machine state: memory and storage are finite word→word maps, so
  points-to assertions + the frame rule give local reasoning about `mload`/`mstore`/`sload`/`sstore`.

Soundness would be proven against the relational semantics. This layer is a convenience, not required
for the equivalence/simulation results above.

## Dependencies

- Lean toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`).
- [Mathlib](https://github.com/leanprover-community/mathlib4), pinned to the matching tag.
