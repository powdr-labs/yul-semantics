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

The semantics (relational ground truth, determinism, executable interpreter with a proven
adequacy theorem), the `yul%` DSL, a pretty-printer, and the optimization meta-theory
(equivalences, congruences, a verified-pass skeleton) are in place. See the annotated build plan
at the end of [`DESIGN.md`](./DESIGN.md) for details and open threads.

## Acknowledgements

This project is inspired by [EVMYulLean](https://github.com/NethermindEth/EVMYulLean),
Nethermind's Lean 4 formalization of the EVM and Yul — in particular, embedding Yul concrete
syntax as a Lean DSL follows its spirit. The semantics here is an independent, dialect-parametric
design; see [`DESIGN.md`](./DESIGN.md).

## License

[Apache 2.0](./LICENSE).
