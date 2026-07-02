# The `funDef`-body congruence gap

**Status: open.** The equivalence framework (`YulSemantics/Equiv.lean`) has no congruence lemma
for rewriting *inside the body of a function definition*, and consequently the rewriter engine
(`YulSemantics/Optimizer.lean`, `rewriteStmt`) deliberately does **not** descend into `funDef`
bodies. Everything else — expressions, statements, blocks, loop inits, switch cases — is covered.

## The problem, precisely

Function definitions flow into execution through three mechanisms in `YulSemantics/BigStep.lean`:

1. `hoist D body` collects a block's `funDef` statements into an `FScope` — storing each function's
   **body syntactically** in its `FDecl`;
2. the `block` rule pushes that scope onto the function environment (`FunEnv`);
3. the `callOk`/`callHalt` rules look up the callee with `lookupFun` and execute the **stored**
   `decl.body`.

Now consider rewriting inside a function body, e.g.

```text
{ function f() -> r { r := add(x, 0) }  …  }     -- p₁
{ function f() -> r { r := x }          …  }     -- p₂
```

These programs *are* semantically equivalent (the claim is true!). But the framework cannot derive
it, for two stacking reasons:

* **`hoist` disagrees.** `hoist D p₁ ≠ hoist D p₂` — the `FDecl`s store different bodies — so
  `EquivBlock.of_stmts`, whose side condition is `hoist`-agreement, does not apply.
* **Pointwise equivalence quantifies over a *single* function environment.** All our equivalences
  have the shape `∀ funs …, Step D funs … ↔ Step D funs …` — both sides run under the *same*
  `funs`. But after the block rule fires, `p₁` executes under an environment containing `f`'s old
  body while `p₂` executes under an environment containing the new one. The statement we would
  need relates executions under **two different, pointwise-related environments**, which is simply
  not expressible in the current definitions.

Note this is *not* a soundness issue — no false statement is provable — it is an
**incompleteness** of the congruence toolkit: a class of true equivalences is out of reach.

## What is needed: a function-environment relation

The fix is a simulation lemma parameterized by a relation on function environments. Sketch:

```lean
/-- Corresponding declarations: same signature, bodies related. -/
def FDeclRel (R : Block D.Op → Block D.Op → Prop) (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧ R d₁.body d₂.body

/-- Corresponding environments: same shape, same names, related declarations. -/
def FunEnvRel (R) (funs₁ funs₂ : FunEnv D) : Prop :=
  List.Forall₂ (List.Forall₂ (fun p q => p.1 = q.1 ∧ FDeclRel R p.2 q.2)) funs₁ funs₂
```

and the **main lemma** (by rule induction over `Step`, in the style of `Determinism.lean` /
`Adequacy.lean` — the single-judgment encoding makes this a standard induction):

> If `Step D funs₁ V st code res`, and `FunEnvRel R funs₁ funs₂`, and `code` is related to `code₂`
> (same syntax except sub-blocks/bodies related by `R`), then `Step D funs₂ V st code₂ res`,
> where `R` is instantiated with "pairwise-`EquivStmt`-related statement lists".

Key cases:

* **`block`**: the environments are extended with `hoist D body₁` / `hoist D body₂`; a lemma
  `hoist`-of-related-bodies-are-related-scopes extends `FunEnvRel` (this is where the current
  `hoist`-equality side condition generalizes to `hoist`-*relatedness*).
* **`callOk`/`callHalt`**: `lookupFun` on related environments returns related declarations *and*
  related visible-scope tails (a `lookupFun`-respects-`FunEnvRel` lemma); the callee body then
  steps by the induction hypothesis. Same signature (params/rets equality) keeps argument binding
  and return collection identical.
* All other cases are congruence plumbing identical in shape to the existing `Imp` lemmas.

There is a well-foundedness subtlety to watch: the relation `R` used inside `FDeclRel` must be the
*same* relation the theorem establishes (bodies are related by pointwise equivalence **under
related environments**, recursively). The standard resolution is to take `R` to be *syntactic*
pairwise-relatedness (e.g. "identical up to sound rule rewriting", or an inductively defined
"related syntax" relation), **not** the semantic equivalence itself — the induction is then over
the derivation with the syntactic relation fixed, and the semantic statement falls out at the end.
This mirrors how CompCert phrases matching between transformed function environments.

## What it unlocks

* `EquivStmt.funDef_congr` — the missing congruence — and with it a rewriter engine **v2** that
  descends into function bodies (drop the `funDef` short-circuit in `rewriteStmt`, replace the
  `hoist`-equality side conditions with `hoist`-relatedness).
* **Function inlining** and its correctness proof (the environment relation is exactly the
  invariant an inliner maintains).
* **Dead-function elimination** (relating environments of different *shapes* — a mild
  generalization of `FunEnvRel` from `Forall₂` to a sub-environment relation).
* Any per-function optimization pass (running a `CorrectPass` on each function body).

## Current impact and workaround

* The engine (`CorrectPass.ofRule`) rewrites everywhere **except** inside `funDef` bodies; the
  pass is still *correct*, just less complete.
* Yul programs in compiler pipelines typically keep hot code inside functions, so engine v2 is
  needed for the optimizer to be practically useful — this gap is on the critical path of the
  optimizer project, roughly on par with the well-formedness (WF) work.
* Interim workaround for whole-function rewriting: treat each function body as a top-level
  program and re-assemble — but proving *that* correct runs into exactly this gap; there is no
  shortcut around the environment relation.

## Related

* `YulSemantics/Equiv.lean` — module docstring documents the gap and the two `hoist` side
  conditions it induces.
* `YulSemantics/Optimizer.lean` — `rewriteStmt`'s `funDef` case is the engine's short-circuit.
* The WF (well-formedness) thread: the static semantics and the environment relation overlap
  (both talk about signatures of functions in scope); building WF first likely provides the
  signature infrastructure `FDeclRel` needs.
