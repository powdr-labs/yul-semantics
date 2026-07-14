# Yul Semantics — Design

This repository defines a formal semantics for the [Yul](https://docs.soliditylang.org/en/latest/yul.html)
intermediate language in Lean 4. It is the foundation for a future, separate project: a
**verified optimizing compiler from Yul to EVM bytecode**. That compiler will build *on top* of
this repository; the EVM bytecode semantics lives in a *different* repository and is not included
here.

Scope of this repo: **the Yul semantics only.** No compiler, no bytecode.

## Guiding decisions

These were decided up front and drive everything below.

### 1. Gas is not modeled

The Yul semantics is **gas-free**. There is no gas field in the machine state and no gas in the
control-flow outcome. Consequences:

- Yul→Yul optimization correctness is purely *functional equivalence* — same result, no gas
  obligation. We deliberately prove **nothing** about gas going up or down (some passes trade it).
- Gas is the optimizer's *motivation*, never a correctness obligation.

The one place gas leaks into the *language* is via built-ins, handled in the Dialect (see §"Effect
classification").

Although gas costs are absent, the EVM dialect tracks the active-memory high-water mark because
`msize()` exposes it as a functional program result. Memory-touching operations update that mark;
no gas is charged for the expansion.

### 2. Ground truth is a big-step relational semantics

The canonical definition of "what a Yul program means" is an **inductive big-step (natural)
semantics** — an evaluation relation, not an executable function.

Rationale: empirical validation against `solc`'s Yul interpreter is **not** a priority for this
project, so the main advantage of an executable interpreter (differential testing) does not apply.
The relational semantics reads like a specification, is the natural object for inductive
meta-theory (logic soundness, compiler simulation), models non-determinism natively, and — because
we prove the interpreter equivalent to it if/when we build one — its "silent ill-formedness" risk
is caught by that very equivalence proof (a missing rule makes adequacy unprovable).

An **executable fuel-indexed interpreter** is a *derived* view (`YulSemantics/Interp.lean`), built
over an `ExecDialect` (a `Dialect` plus a computable `builtinFn`). It is not itself a correctness
foundation; **adequacy** — `interp` ⇔ `BigStep` (sound always, complete for terminating runs) — is
the pending proof that ties it to the ground truth. It already lets us *run* programs end-to-end
(see the `native_decide` tests in `YulSemantics/Examples.lean`).

### 3. The semantics is parameterized over an abstract `Dialect`

Yul is dialect-agnostic by design: the core language (control flow, scoping, functions) is
independent of the built-in functions. We reflect this with an abstract `Dialect` providing:

- `Op` — the built-in operation type (a finite enum for the EVM dialect); the AST is parameterized
  over it (see "AST" below).
- `Value` — the value type (for the EVM dialect: `BitVec 256`).
- `State` — the machine/world state (memory, storage, environment, logs, …).
- `builtins` — interpretation of built-in functions: names + argument values + state ↦ result
  values + new state (+ possible halt).
- `litValue` — interpretation of numeric literals as values.
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

### 5. Concrete-syntax DSL, built early

A `syntax`/macro embedding lets us write real Yul concrete syntax that elaborates to the AST
(similar in spirit to EVMYulLean). Built early so tests and examples read like Yul from the start.

## Language model

### AST

Yul's grammar (EVM dialect) is small and fixed:

- **Expressions**: literals, identifiers, and function calls only.
- **Statements**: block, function definition (multiple returns, `-> a, b`), `let` declaration,
  assignment, `if` (no `else`), `switch`/`case`/`default`, `for { init } cond { post } { body }`,
  `break`, `continue`, `leave`, and expression-statements.
- **Objects**: named code block + sub-objects + data.

**Built-ins are a first-class enum, and the AST is parameterized over it (Option D).** A call is
either a dialect built-in (`Expr.builtin op args`, `op : Op`) or a user-defined function call
(`Expr.call fn args`, `fn : Ident`). The AST is generic in the *type* `Op` (the dialect supplies it),
so:

- the core stays **dialect-agnostic** — a generic pass has type `∀ Op, …` and *cannot* inspect
  specific built-ins beyond their `effects`, so "correct for every dialect" holds by parametricity,
  not by discipline;
- **dialect-specific** optimizations (constant folding, algebraic identities) fix `Op := EVM.Op` and
  pattern-match on it structurally (exhaustive, type-checked), with correctness proofs connecting
  `op` directly to the built-in semantics;
- name→`Op` resolution happens at parse time (Phase 4), sound because Yul forbids user functions from
  shadowing built-ins. User functions remain `Ident`, resolved via the environment.

Sketch:

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
  | halt (h : HaltData) -- from halting built-ins (return/revert/stop); propagates to the top
```

### Scoping

Yul is lexically scoped. A block first collects its function definitions (functions may be
forward-referenced within a block), then executes its statements. The environment maps variable
names to values and function names to definitions.

### Effect classification (the one place gas touches the language)

The `Dialect` classifies each built-in by effect — e.g. *pure*, *state-reading*, *state-writing*,
*halting*, and whether it is *deterministic*. This classification is what makes optimization proofs
sound (CSE/DCE/reordering may only move or drop calls with the right effects).
The EVM dialect proves that these flags soundly over-approximate `stepOp`: deterministic operations
have at most one result, non-writing operations preserve the entire state, and non-halting
operations only return normally (`EVM.effects_sound`).

Two built-ins interact with gas and must be classified as **impure / non-deterministic** even
though we do not model gas:

- `gas()` returns *remaining* gas — a value that changes during execution. It is modeled as an
  oracle / non-deterministic read (never a constant; two `gas()` calls may differ, so they cannot be
  CSE'd).
- gas forwarding + failure of `call`/`staticcall`/`delegatecall`: external call outcomes are modeled
  as oracle inputs (they can depend on out-of-gas in the callee, which a gas-free model cannot
  produce).

## Meta-theory / what we are building toward

### Yul→Yul optimization correctness (this repo's proof surface)

Target property: **semantic preservation** = functional equivalence of whole-program behavior. Tools:

1. **Behavior / observation**: halting result (`return`/`revert`/`stop` + returndata), resulting
   storage/logs, and terminate-vs-diverge. (No gas.)
2. **Contextual equivalence as a congruence**: expression- and statement-equivalence proven to be a
   *congruence* w.r.t. every AST constructor. Local rewrites (`add(x,0) → x`, constant folding, …)
   are proven locally and lifted into any context by this congruence lemma — the workhorse.
3. **Effect classification** (above): required for CSE, dead-code elimination, reordering.
4. **Binding discipline for inlining**: substitution / α-renaming with capture avoidance.
5. **Determinism lemma**: the EVM-dialect semantics is deterministic given the dialect (modulo the
   oracle inputs), which turns "equivalence" into "same result."

### Yul→EVM compiler correctness (future, separate repo)

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

Soundness is proven against the relational semantics. This layer is a convenience, not required for
the equivalence/simulation results above.

## Build plan (phases)

- **Phase 0** — Toolchain: add Mathlib (pinned to the toolchain), CI, module layout. *(done)*
- **Phase 1** — AST (`Literal`/`Expr`/`Stmt`/`Object`) + `Outcome`. *(done — `YulSemantics/Ast.lean`)*
- **Phase 2** — `Dialect` abstraction + effect classification; gas-free EVM dialect instance
  (`Value := BitVec 256`). *(done — `YulSemantics/Dialect.lean`, `YulSemantics/Dialect/EVM.lean`)*
- **Phase 3** — Big-step relational semantics (the ground truth): scoping, block-level function
  pre-collection, multiple return values, outcome propagation. *(relation done —
  `YulSemantics/BigStep.lean`, smoke-tested in `YulSemantics/Examples.lean`; determinism proven —
  see below)*
- **Phase 4** — Concrete-syntax DSL (Yul syntax → AST). *(done — `YulSemantics/Syntax.lean`;
  `yul% { … }` → `Block EVM.Op`, round-trip-tested in `YulSemantics/Examples.lean`)*
- **Interpreter** — total fuel-indexed executable interpreter over an `ExecDialect`. *(done —
  `YulSemantics/Interp.lean`; runs programs in `Examples.lean` via `native_decide`)*
- **Phase 5** — Meta-theory foundations: behavior/observation, contextual equivalence + congruence
  lemma, sample local-rewrite equivalences validating the framework.
- **Determinism** — *(done — `YulSemantics/Determinism.lean`)*. `Step.det` by a single rule
  induction, given deterministic built-ins; corollaries for the five conceptual relations and
  whole-program runs; `EVM.evm_deterministic` discharges the hypothesis for the EVM dialect
  (`EVM.run_det`). Two design notes baked in along the way: (1) `switch` dispatches through
  `selectSwitch` (requiring `[DecidableEq D.Value]` on the judgment), making it deterministic by
  construction; (2) the semantics is encoded as a **single indexed judgment** `Step` over a
  `Code`/`Res` sum rather than five literal `mutual` relations — Lean's `induction` tactic does not
  support mutual inductive predicates and the equation compiler cannot compile mutual structural
  recursion over them, so the single-judgment encoding is what makes this (and every future
  derivation induction: adequacy, compiler simulation) a standard tactic proof. The five relation
  names survive as abbreviations with unchanged signatures.
- **Adequacy** — *(done — `YulSemantics/Adequacy.lean`)*. Under `ExecDialect.Lawful` (the executable
  `builtinFn` agrees exactly with the relational `Builtin`; definitional for the EVM dialect):
  **soundness** (interpreter `.ok` at any fuel ⇒ derivation; induction on fuel) and **completeness**
  (derivation ⇒ interpreter `.ok` at every sufficiently large fuel; rule induction — the
  `∀ n ≥ N` form embeds fuel monotonicity, so no separate monotonicity lemma). Combined as
  `Interp.adequacy` / `Interp.run_adequacy`, instantiated hypothesis-free for EVM as
  `EVM.run_adequacy`. With determinism, the interpreter is pinned down as *the* computational
  content of the semantics.
- **Phase 5** — optimization meta-theory. *(first cut done — `YulSemantics/Equiv.lean`,
  `YulSemantics/Rewrites.lean`)*. Pointwise semantic equivalences for all five syntactic classes
  (`EquivExpr`/`EquivArgs`/`EquivStmt`/`EquivStmts`/`EquivBlock`, each an equivalence relation);
  behavior (`EquivBlock.run_iff`); **congruence lemmas** for built-in/user calls (argument lists via
  `Forall₂`), `let`/`assign`/`exprStmt`/`cond`/`switch` (labels + case blocks + default) /`forLoop`
  (cond/post/body), sequences, and blocks. Two honest hoisting-induced side conditions, documented
  in the module: block congruence needs `hoist`-agreement (`rfl` for non-`funDef` rewrites), and
  `funDef`-body congruence is deferred to the function-environment relation that inlining will need.
  Validated by sample EVM rewrites: constant folding `add(2,3) ≈ 5`, the identity `add(x,0) ≈ x`
  (stated for a *variable* — `add(e,0) ≈ e` is false for multi-valued `e`, a real optimizer
  precondition surfaced by the proofs), and the identity lifted through congruence to
  `sstore(0, add(x,0)) ≈ sstore(0, x)` at statement and whole-program (DSL) level.

## Dependencies

- Lean toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`).
- [Mathlib](https://github.com/leanprover-community/mathlib4), pinned to the matching tag.
