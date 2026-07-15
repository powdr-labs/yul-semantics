# yul-semantics

A formal semantics for the [Yul](https://docs.soliditylang.org/en/latest/yul.html) intermediate
language, written in Lean 4.

This repository defines **only the Yul semantics**. It is the foundation for a separate, future
project — a *verified optimizing compiler from Yul to EVM bytecode* — that will build on top of it.
The EVM bytecode semantics lives in a different repository.

## Design

See [`DESIGN.md`](./DESIGN.md) for the full design and its rationale. In short:

- **Gas is not modeled.** Yul→Yul optimization correctness is functional equivalence, not a gas
  obligation.
- **The ground truth is a big-step relational semantics** (an inductive evaluation relation). A
  fuel-indexed executable interpreter is a derived view, proven adequate.
- The semantics is **parameterized over an abstract `Dialect`** (value type, machine state, built-in
  interpretation), keeping the core dialect-agnostic.
- The **EVM dialect uses `BitVec 256`** for words.

## Building

Requires the Lean toolchain pinned in [`lean-toolchain`](./lean-toolchain) (managed by
[`elan`](https://github.com/leanprover/elan)).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## What is implemented

- **Core semantics** ([`BigStep.lean`](./YulSemantics/BigStep.lean)) — the big-step relational
  ground truth: lexical scoping, block-level function pre-collection (forward references and mutual
  recursion), multiple return values, and `break`/`continue`/`leave`/`halt` outcome propagation. It
  is a single indexed judgment (`Step`) over the five syntactic classes, with the five conceptual
  relations recovered as abbreviations.
- **Determinism** ([`Determinism.lean`](./YulSemantics/Determinism.lean)) — `Step.det`: the judgment
  is deterministic given deterministic built-ins, proven by one rule induction. Discharged for the
  EVM dialect as `EVM.run_det`.
- **Executable interpreter + adequacy** ([`Interp.lean`](./YulSemantics/Interp.lean),
  [`Adequacy.lean`](./YulSemantics/Adequacy.lean)) — a total fuel-indexed interpreter over an
  `ExecDialect`, with a proven **adequacy** theorem (soundness at any fuel; completeness at
  sufficiently large fuel for terminating runs). Instantiated hypothesis-free for EVM as
  `EVM.run_adequacy`.
- **EVM dialect** ([`Dialect/EVM.lean`](./YulSemantics/Dialect/EVM.lean)) — the full user-facing Yul
  EVM built-in set over `BitVec 256` (through the Fusaka fork, including `clz`, `mcopy`, `blobhash`,
  `blobbasefee`). Covered: arithmetic/comparison/bitwise/shifts, memory (with the `msize`
  active-memory high-water mark), storage and transient storage, calldata/code/returndata reads and
  copies (`returndatacopy` bounds failure is an exceptional halt), the execution-environment and
  world-state readers (via abstract environment maps), logs, the object-data ops, and the halting
  ops. `keccak256` uses an environment-supplied oracle, abstract by default and executable when a
  client supplies a concrete implementation.
- **Open-world calls and creation** — `call`/`callcode`/`delegatecall`/`staticcall` and
  `create`/`create2` are interpreted relationally by `EVM.evmWithExternal calls creates`. The
  supplied `ExternalCalls`/`ExternalCreates` relations describe *completed* external executions and
  may summarize arbitrary nested calls, creations, and re-entrant callbacks; the semantics fixes only
  the caller-observable boundary (memory copy-in, world commit/rollback, return-data copy-out, the
  success/address word). `gas()` is a nondeterministic oracle in these dialects. See
  [`DESIGN.md`](./DESIGN.md) for the exact boundary.
- **Static write protection** — a frame flagged static (`ExecEnv.static`, as set on a `STATICCALL`
  callee) enforces EVM write protection: `sstore`/`tstore`/`log0`–`log4`/`selfdestruct`,
  `create`/`create2`, and value-bearing `call`/`callcode` halt exceptionally instead of modifying
  state; `staticcall`, `delegatecall`, and zero-value `call` remain permitted.
- **`selfdestruct`** — transfers the executing account's balance and halts, recording the scheduled
  destruction together with its `createdThisTx` bit (post-EIP-6780: only an account created in the
  current transaction is deletable; the self-beneficiary balance-burn distinction is modeled). Actual
  fork-dependent deletion is a transaction-finalization step, outside this frame semantics.
- **Frame-boundary observation** ([`Observation.lean`](./YulSemantics/Observation.lean)) —
  `revert`/`invalid`/`invalidMemoryAccess` roll the frame's committed world changes back at the
  observation boundary (only the outcome marker and exposed return data survive), while
  `stop`/`return`/`selfdestruct` and normal termination commit — matching real EVM. Applied by
  `EVM.committedState` and the observed whole-program run `EVM.RunCommitted` (functional given
  determinism). This makes dead-effect reasoning sound: `EVM.deadStore_revert_obs_eq` proves a dead
  store before a revert is observationally invisible — something the raw exact-state relations cannot
  see.
- **Effect classification** ([`Dialect.lean`](./YulSemantics/Dialect.lean)) — each built-in is
  classified (deterministic / reads / writes / halts). The EVM dialect proves the classification
  soundly over-approximates its semantics (`EVM.effects_sound`, and `EVM.effects_sound_withExternal`
  for the open world).
- **Objects** ([`Object.lean`](./YulSemantics/Object.lean),
  [`ObjectRun.lean`](./YulSemantics/ObjectRun.lean)) — the Yul object layer (nested
  `code`/`data`/sub-objects): name resolution, a layout-consistency predicate relating a compiler's
  byte layout to an object, and a symbolic proof that the canonical constructor (`datacopy`/`return`)
  returns a data segment's bytes.
- **Surface tooling** ([`Syntax.lean`](./YulSemantics/Syntax.lean),
  [`PrettyPrint.lean`](./YulSemantics/PrettyPrint.lean)) — the `yul%` / `yulObject%` concrete-syntax
  DSL and a pretty-printer.
- **Optimization meta-theory** ([`Equiv.lean`](./YulSemantics/Equiv.lean),
  [`Rewrites.lean`](./YulSemantics/Rewrites.lean)) — pointwise semantic equivalence for all five
  syntactic classes, each proven an equivalence relation; congruence lemmas w.r.t. every AST
  constructor (the workhorse for lifting local rewrites into any context); and worked sample rewrites
  (constant folding, `add(x,0) ≈ x`).

## What is not (yet) done, and why

- **Yul→EVM compiler correctness.** Deliberately out of scope for this repo — it belongs to the
  separate compiler project, which will instantiate the abstract `Dialect` with the real EVM
  semantics and prove a conditional-on-gas forward simulation. See [`DESIGN.md`](./DESIGN.md).
- **Inlining / function-body congruence.** Rewriting *inside* a function body changes the `FDecl`
  that block-hoisting stores, so it needs a relation on function environments threaded through the
  judgment. That machinery belongs with function-level optimizations (inlining) and is deferred; the
  current block congruence carries an explicit `hoist`-agreement side condition (`rfl` for rewrites
  that do not touch top-level `funDef`s).
- **`reads`-flag soundness.** `EVM.effects_sound` proves the `deterministic`/`writes`/`halts` flags
  sound; a machine-checked soundness for `reads` needs a notion of state observation (a read
  footprint) and is deferred. The flag is documented and currently unused by any proof.
- **Program logic (Hoare / separation).** An optional layer on top of the relational semantics;
  deferred until needed. Not required for the equivalence/simulation results.
- **Divergence reasoning.** Not needed for the main compiler theorem (the gas-metered target cannot
  diverge), and deferred indefinitely.
- **Gas.** Not modeled by design (see [`DESIGN.md`](./DESIGN.md) §1). Within-frame out-of-gas is
  therefore not expressible; out-of-gas in a callee is subsumed by the open-world call relation.

### Scope of the meta-theory (important)

The determinism proof, the executable interpreter, and the adequacy theorem are established for the
**closed-world local dialect `EVM.evm`** only. They do **not** extend to the **open-world dialect
`EVM.evmWithExternal` (call/create)**:

- `evmWithExternal` is relational and may be non-deterministic (an external call/create outcome is a
  response chosen by an arbitrary environment), so the determinism theorem does not apply to it.
- It has **no executable interpreter and no adequacy theorem** — there is deliberately no universal
  executable choice for an open-world relation. In the executable dialect (`EVM.evm` / `EVM.exec`),
  `gas()` and the call/create family are intentionally left **stuck** (no reduction).
- What *does* carry over to the open world is effect-classification soundness
  (`EVM.effects_sound_withExternal`).

So do not read "deterministic" or "adequate" as statements about programs that call `gas()` or make
external calls/creations.

## Tests

Correctness is carried by the theorems above; in addition the repository is exercised end-to-end:

- [`Examples.lean`](./YulSemantics/Examples.lean) — interpreter runs via `native_decide` (arithmetic,
  storage, memory and `msize`, the `returndatacopy` bounds exception, `selfdestruct`) and `yul%` DSL
  round-trips.
- [`FibExample.lean`](./YulSemantics/FibExample.lean) — a full worked contract (see below).
- [`ObjectRun.lean`](./YulSemantics/ObjectRun.lean) — a concrete object whose layout is checked
  consistent and whose constructor is run to its returned data segment.
- [`Dialect/EVM.lean`](./YulSemantics/Dialect/EVM.lean) and
  [`Observation.lean`](./YulSemantics/Observation.lean) — inline guards for effect flags, the
  `selfdestruct` cases, the open-world call/create/`gas()` boundary, static write protection, and the
  commit/rollback observation.

## Worked example

[`FibExample.lean`](./YulSemantics/FibExample.lean) is an end-to-end verification: a Yul contract
that reads `n` from calldata, computes the `n`-th Fibonacci number, and returns it. It is proven
correct two ways:

- **concretely**, by running the interpreter for several inputs (`native_decide`); and
- **generally** (`fibContract_correct`): for *every* initial state the contract halts, writes
  `fib(n) mod 2²⁵⁶` to memory, and returns that word. The proof is fully relational — a loop
  invariant (`fibLoop`, `a = fib i`, `b = fib(i+1)`) by induction on the remaining iterations,
  assembled with the prelude and postlude into the whole run.

## Acknowledgements

This project is inspired by [EVMYulLean](https://github.com/NethermindEth/EVMYulLean),
Nethermind's Lean 4 formalization of the EVM and Yul — in particular, embedding Yul concrete
syntax as a Lean DSL follows its spirit. The semantics here is an independent, dialect-parametric
design; see [`DESIGN.md`](./DESIGN.md).

## License

[Apache 2.0](./LICENSE).
