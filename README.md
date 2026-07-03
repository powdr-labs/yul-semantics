# yul-semantics

A formal semantics for the [Yul](https://docs.soliditylang.org/en/latest/yul.html) intermediate
language, written in Lean 4.

This repository defines **only the Yul semantics**. It is the foundation for a future, separate
project — a *verified optimizing compiler from Yul to EVM bytecode* — that will build on top of it.
The EVM bytecode semantics lives in a different repository.

## Design

See [`DESIGN.md`](./DESIGN.md) for the full design and its rationale. In short:

- **Gas is not modeled.** Optimization correctness is functional equivalence.
- **Ground truth is a big-step relational semantics** (an inductive evaluation relation). A
  fuel-indexed executable interpreter is provided as a derived view, proven adequate.
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

## Status

In place:

- **Core semantics** — the big-step relational ground truth, a determinism proof, and a
  fuel-indexed executable interpreter with a proven adequacy (soundness + completeness) theorem.
- **EVM dialect** — the full built-in set (through the upcoming hard fork), over `BitVec 256`.
- **Objects** — the Yul object layer (nested `code`/`data`/sub-objects): name resolution, a
  layout-consistency predicate relating a compiler's byte layout to an object, and a symbolic proof
  that the canonical constructor (`datacopy`/`return`) returns a data segment's bytes.
- **Surface tooling** — the `yul%` / `yulObject%` concrete-syntax DSL and a pretty-printer.
- **Optimization meta-theory** — pointwise program equivalence, congruence lemmas, and a
  verified-pass skeleton.

See the annotated build plan at the end of [`DESIGN.md`](./DESIGN.md) for details and open threads.

## Worked example

[`YulSemantics/FibExample.lean`](./YulSemantics/FibExample.lean) is a first end-to-end verification:
a Yul contract that reads `n` from calldata, computes the `n`-th Fibonacci number, and returns it.
It is proven correct two ways:

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
