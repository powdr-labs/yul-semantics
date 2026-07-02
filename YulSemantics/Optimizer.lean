import YulSemantics.Equiv

/-!
# YulSemantics.Optimizer

The formalization of a **correct optimizer**, in three layers (dialect-generic):

1. **`CorrectPass`** — a whole-program transformation bundled with a proof of block-level semantic
   equivalence. Correctness *composes*: `comp`, `pipeline`, and `iterate` are correct by
   construction (`EquivBlock` is reflexive and transitive), so the only proof obligation an
   optimizer ever has is per-pass.
2. **`RuleSound`** — a local rewrite rule `Expr → Option Expr` (declining via `none`) together
   with a soundness property: whatever it rewrites is semantically equivalent.
3. **The rewriter engine** — a generic bottom-up traversal (`rewriteBlock`) applying a rule at
   every expression node, with a *single* correctness theorem (`rewriteBlock_sound`) proven once
   via the congruence lemmas of `YulSemantics.Equiv`. Verifying a new peephole optimization then
   reduces to one `EquivExpr` lemma about two small expressions (`CorrectPass.ofRule`).

**Engine v1 does not descend into `funDef` bodies** — see `docs/fundef-congruence-gap.md`. It
rewrites everywhere else (including `for`-init blocks); since it never adds, removes, or alters a
`funDef` statement, all `hoist`-agreement side conditions are discharged by `hoist_rewrite`.

No improvement obligation is stated anywhere: "correct" means semantics-preserving; gas/size are
benchmarks, not theorems (see `DESIGN.md` §1).
-/

namespace YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Local rewrite rules -/

/-- A local rewrite rule: partial (declines via `none`) so it can be applied everywhere. -/
def RuleSound (D : Dialect) [DecidableEq D.Value] (r : Expr D.Op → Option (Expr D.Op)) : Prop :=
  ∀ e e', r e = some e' → EquivExpr D e e'

/-- Apply a rule at a single node (identity if the rule declines). -/
def applyRule (r : Expr D.Op → Option (Expr D.Op)) (e : Expr D.Op) : Expr D.Op :=
  (r e).getD e

theorem applyRule_equiv {r} (hr : RuleSound D r) (e : Expr D.Op) :
    EquivExpr D e (applyRule r e) := by
  unfold applyRule
  cases h : r e with
  | none => exact EquivExpr.refl e
  | some e' => exact hr e e' h

/-! ### The rewriter -/

mutual

/-- Bottom-up rewriting of an expression: rewrite the sub-expressions, then apply the rule at the
root. -/
def rewriteExpr (r : Expr D.Op → Option (Expr D.Op)) : Expr D.Op → Expr D.Op
  | .lit l => applyRule r (.lit l)
  | .var x => applyRule r (.var x)
  | .builtin op args => applyRule r (.builtin op (rewriteExprs r args))
  | .call fn args => applyRule r (.call fn (rewriteExprs r args))

def rewriteExprs (r : Expr D.Op → Option (Expr D.Op)) : List (Expr D.Op) → List (Expr D.Op)
  | [] => []
  | e :: es => rewriteExpr r e :: rewriteExprs r es

end

/-- Rewrite an optional expression (a `let` initializer). -/
def rewriteOptExpr (r : Expr D.Op → Option (Expr D.Op)) : Option (Expr D.Op) → Option (Expr D.Op)
  | none => none
  | some e => some (rewriteExpr r e)

mutual

/-- Bottom-up rewriting of a statement. Deliberately does **not** descend into `funDef` bodies
(see `docs/fundef-congruence-gap.md`); everything else is rewritten. -/
def rewriteStmt (r : Expr D.Op → Option (Expr D.Op)) : Stmt D.Op → Stmt D.Op
  | .block body => .block (rewriteStmts r body)
  | .funDef n ps rs b => .funDef n ps rs b
  | .letDecl vars val => .letDecl vars (rewriteOptExpr r val)
  | .assign vars e => .assign vars (rewriteExpr r e)
  | .cond c body => .cond (rewriteExpr r c) (rewriteStmts r body)
  | .switch c cs dflt => .switch (rewriteExpr r c) (rewriteCases r cs) (rewriteOptBlock r dflt)
  | .forLoop init c post body =>
      .forLoop (rewriteStmts r init) (rewriteExpr r c) (rewriteStmts r post)
        (rewriteStmts r body)
  | .exprStmt e => .exprStmt (rewriteExpr r e)
  | .«break» => .«break»
  | .«continue» => .«continue»
  | .leave => .leave

def rewriteStmts (r : Expr D.Op → Option (Expr D.Op)) : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: ss => rewriteStmt r s :: rewriteStmts r ss

def rewriteCases (r : Expr D.Op → Option (Expr D.Op)) :
    List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: cs => (l, rewriteStmts r b) :: rewriteCases r cs

def rewriteOptBlock (r : Expr D.Op → Option (Expr D.Op)) :
    Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (rewriteStmts r b)

end

/-- Rewrite a whole program. -/
def rewriteBlock (r : Expr D.Op → Option (Expr D.Op)) (b : Block D.Op) : Block D.Op :=
  rewriteStmts r b

/-- The rewriter never adds, removes, or alters `funDef` statements, so the hoisted function scope
is unchanged — this discharges every `hoist`-agreement side condition in the engine theorem. -/
theorem hoist_rewrite (r : Expr D.Op → Option (Expr D.Op)) (ss : List (Stmt D.Op)) :
    hoist D (rewriteStmts r ss) = hoist D ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      simp only [hoist] at ih ⊢
      cases s <;> simp [rewriteStmts, rewriteStmt, List.filterMap_cons, ih]

/-! ### The engine theorem -/

mutual

theorem rewriteExpr_sound {r} (hr : RuleSound D r) :
    ∀ e : Expr D.Op, EquivExpr D e (rewriteExpr r e)
  | .lit l => by
      simp only [rewriteExpr]; exact applyRule_equiv hr _
  | .var x => by
      simp only [rewriteExpr]; exact applyRule_equiv hr _
  | .builtin op args => by
      simp only [rewriteExpr]
      exact (EquivExpr.builtin_congr op
        (EquivArgs.of_forall₂ (rewriteExprs_sound hr args))).trans (applyRule_equiv hr _)
  | .call fn args => by
      simp only [rewriteExpr]
      exact (EquivExpr.call_congr fn
        (EquivArgs.of_forall₂ (rewriteExprs_sound hr args))).trans (applyRule_equiv hr _)

theorem rewriteExprs_sound {r} (hr : RuleSound D r) :
    ∀ es : List (Expr D.Op), List.Forall₂ (EquivExpr D) es (rewriteExprs r es)
  | [] => by simp only [rewriteExprs]; exact .nil
  | e :: es => by
      simp only [rewriteExprs]
      exact .cons (rewriteExpr_sound hr e) (rewriteExprs_sound hr es)

end

mutual

theorem rewriteStmt_sound {r} (hr : RuleSound D r) :
    ∀ s : Stmt D.Op, EquivStmt D s (rewriteStmt r s)
  | .block body => by
      simp only [rewriteStmt]
      exact EquivBlock.of_forall₂ (rewriteStmts_sound hr body) (hoist_rewrite r body).symm
  | .funDef n ps rs b => by
      simp only [rewriteStmt]; exact EquivStmt.refl _
  | .letDecl vars none => by
      simp only [rewriteStmt, rewriteOptExpr]; exact EquivStmt.refl _
  | .letDecl vars (some e) => by
      simp only [rewriteStmt, rewriteOptExpr]
      exact EquivStmt.letDecl_congr vars (rewriteExpr_sound hr e)
  | .assign vars e => by
      simp only [rewriteStmt]
      exact EquivStmt.assign_congr vars (rewriteExpr_sound hr e)
  | .cond c body => by
      simp only [rewriteStmt]
      exact EquivStmt.cond_congr (rewriteExpr_sound hr c)
        (EquivBlock.of_forall₂ (rewriteStmts_sound hr body) (hoist_rewrite r body).symm)
  | .switch c cs none => by
      simp only [rewriteStmt, rewriteOptBlock]
      exact EquivStmt.switch_congr (rewriteExpr_sound hr c) (rewriteCases_sound hr cs)
        (EquivBlock.refl _)
  | .switch c cs (some d) => by
      simp only [rewriteStmt, rewriteOptBlock]
      exact EquivStmt.switch_congr (rewriteExpr_sound hr c) (rewriteCases_sound hr cs)
        (EquivBlock.of_forall₂ (rewriteStmts_sound hr d) (hoist_rewrite r d).symm)
  | .forLoop init c post body => by
      simp only [rewriteStmt]
      exact EquivStmt.forLoop_congr
        (EquivStmts.of_forall₂ (rewriteStmts_sound hr init)) (hoist_rewrite r init).symm
        (rewriteExpr_sound hr c)
        (EquivBlock.of_forall₂ (rewriteStmts_sound hr post) (hoist_rewrite r post).symm)
        (EquivBlock.of_forall₂ (rewriteStmts_sound hr body) (hoist_rewrite r body).symm)
  | .exprStmt e => by
      simp only [rewriteStmt]
      exact EquivStmt.exprStmt_congr (rewriteExpr_sound hr e)
  | .«break» => by simp only [rewriteStmt]; exact EquivStmt.refl _
  | .«continue» => by simp only [rewriteStmt]; exact EquivStmt.refl _
  | .leave => by simp only [rewriteStmt]; exact EquivStmt.refl _

theorem rewriteStmts_sound {r} (hr : RuleSound D r) :
    ∀ ss : List (Stmt D.Op), List.Forall₂ (EquivStmt D) ss (rewriteStmts r ss)
  | [] => by simp only [rewriteStmts]; exact .nil
  | s :: ss => by
      simp only [rewriteStmts]
      exact .cons (rewriteStmt_sound hr s) (rewriteStmts_sound hr ss)

theorem rewriteCases_sound {r} (hr : RuleSound D r) :
    ∀ cs : List (Literal × Block D.Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (rewriteCases r cs)
  | [] => by simp only [rewriteCases]; exact .nil
  | (l, b) :: cs => by
      simp only [rewriteCases]
      exact .cons ⟨rfl, EquivBlock.of_forall₂ (rewriteStmts_sound hr b) (hoist_rewrite r b).symm⟩
        (rewriteCases_sound hr cs)

end

/-- **The engine theorem**: bottom-up rewriting with a sound rule preserves the semantics of any
program. -/
theorem rewriteBlock_sound {r} (hr : RuleSound D r) (b : Block D.Op) :
    EquivBlock D b (rewriteBlock r b) :=
  EquivBlock.of_forall₂ (rewriteStmts_sound hr b) (hoist_rewrite r b).symm

/-! ### Correct passes -/

/-- A semantics-preserving whole-program transformation: the contract every optimizer pass must
satisfy. Block-level pointwise equivalence is the weakest of our equivalences that still composes
and is closed under all contexts. -/
structure CorrectPass (D : Dialect) [DecidableEq D.Value] where
  /-- The transformation. -/
  run : Block D.Op → Block D.Op
  /-- Semantic preservation. -/
  sound : ∀ p, EquivBlock D p (run p)

namespace CorrectPass

/-- The identity pass. -/
protected def id : CorrectPass D := ⟨fun p => p, fun p => EquivBlock.refl p⟩

/-- Sequential composition — correct by transitivity, no new proof obligation. -/
def comp (f g : CorrectPass D) : CorrectPass D :=
  ⟨g.run ∘ f.run, fun p => (f.sound p).trans (g.sound (f.run p))⟩

/-- A pipeline of passes, run left to right. -/
def pipeline (ps : List (CorrectPass D)) : CorrectPass D :=
  ps.foldl comp CorrectPass.id

/-- Iterate a pass a fixed number of times (fixpoint iteration with an explicit budget). -/
def iterate (f : CorrectPass D) : Nat → CorrectPass D
  | 0 => CorrectPass.id
  | n + 1 => (iterate f n).comp f

/-- The behavioral guarantee consumed by the compiler: identical whole-program runs. -/
theorem run_iff (f : CorrectPass D) (p : Block D.Op) {st0 V' st' o} :
    Run D p st0 V' st' o ↔ Run D (f.run p) st0 V' st' o :=
  (f.sound p).run_iff

/-- Build a correct pass from a sound local rewrite rule: the entire proof obligation for a
peephole optimization is one `EquivExpr` lemma. -/
def ofRule (r : Expr D.Op → Option (Expr D.Op)) (hr : RuleSound D r) : CorrectPass D :=
  ⟨rewriteBlock r, fun p => rewriteBlock_sound hr p⟩

end CorrectPass

end YulSemantics
