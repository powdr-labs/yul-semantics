# yul-semantics

A formal semantics for the [Yul](https://docs.soliditylang.org/en/latest/yul.html) intermediate
language, written in Lean 4.

This repository defines **only the Yul semantics**. It is the foundation for a future, separate
project — a *verified optimizing compiler from Yul to EVM bytecode* — that will build on top of it.
The EVM bytecode semantics lives in a different repository.

## Design

See [`DESIGN.md`](./DESIGN.md) for the full design and its rationale. In short:

- **Gas is not modeled.** Optimization correctness is functional equivalence.
- **Ground truth is a big-step relational semantics** (an inductive evaluation relation). An
  executable interpreter is optional and deferred.
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

Phase 0 (toolchain, Mathlib, module layout) complete. See the build plan in `DESIGN.md` for the
remaining phases.

## License

[Apache 2.0](./LICENSE).
