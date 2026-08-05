import YulSemantics.BigStep

/-!
# YulSemantics.Equiv

The optimization meta-theory foundations: **semantic equivalence** and its **congruence** properties
— the layer Yul→Yul optimization-pass correctness proofs stand on (see `DESIGN.md`).

## Equivalences

`EquivExpr`/`EquivArgs`/`EquivStmt`/`EquivStmts`/`EquivBlock` are *pointwise* equivalences of the
big-step judgment: same results from **every** configuration (function environment, variable
environment, state). This is stronger than observational equivalence, which makes it exactly the
right notion for local rewrites: a pointwise-equivalent replacement is undetectable in any context.

## Congruence

Local rewrites lift through syntax: every congruence lemma says "replacing a constituent with an
equivalent one yields an equivalent whole". Provided here:

* expressions: `EquivExpr.builtin_congr`, `EquivExpr.call_congr` (argument lists via `EquivArgs`);
* statements: `letDecl`/`assign`/`exprStmt`/`cond`/`switch`/`forLoop` congruences;
* sequences and blocks: `EquivStmts.of_forall₂`, `EquivBlock.of_stmts`.

Two honest side conditions, both consequences of Yul's **function hoisting**:

* `EquivBlock.of_stmts` requires `hoist D b₁ = hoist D b₂`: a block brings its `funDef`s into
  scope, so equivalent statement lists with *different* function definitions need not form
  equivalent blocks. For rewrites that do not touch top-level `funDef` statements this is `rfl`.
* There is **no `funDef` congruence yet**: rewriting inside a function *body* changes the `FDecl`
  stored by `hoist`, so relating the two programs requires a relation on function environments
  ("environments with pointwise-equivalent bodies") threaded through the judgment. That machinery
  belongs with function-level optimizations (inlining) and is deferred.

## Behavior

For whole programs, equivalence of the top-level blocks gives identical `Run` results
(`EquivBlock.run_iff`) — with determinism, identical *unique* results.
-/

namespace YulSemantics

/-- Pointwise lifting of a relation to lists: `Forall₂ R l₁ l₂` holds when `l₁` and `l₂` have the
same length and `R` relates their elements position-wise. (A local stand-in for Mathlib's
`List.Forall₂` — the congruence lemmas below need nothing more than the inductive and `imp`.) -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  /-- Two empty lists are pointwise related. -/
  | nil : Forall₂ R [] []
  /-- Related heads on pointwise-related tails give pointwise-related lists. -/
  | cons : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

/-- `Forall₂` is monotone in the relation. -/
theorem Forall₂.imp {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (t.imp H)

variable {D : Dialect} [DecidableEq D.Value]

/-! ### The equivalences -/

/-- Pointwise semantic equivalence of expressions: same evaluation results from every
configuration. -/
def EquivExpr (D : Dialect) [DecidableEq D.Value] (e₁ e₂ : Expr D.Op) : Prop :=
  ∀ funs V st r, EvalExpr D funs V st e₁ r ↔ EvalExpr D funs V st e₂ r

/-- Pointwise semantic equivalence of argument lists. -/
def EquivArgs (D : Dialect) [DecidableEq D.Value] (es₁ es₂ : List (Expr D.Op)) : Prop :=
  ∀ funs V st r, EvalArgs D funs V st es₁ r ↔ EvalArgs D funs V st es₂ r

/-- Pointwise semantic equivalence of statements. -/
def EquivStmt (D : Dialect) [DecidableEq D.Value] (s₁ s₂ : Stmt D.Op) : Prop :=
  ∀ funs V st V' st' o, ExecStmt D funs V st s₁ V' st' o ↔ ExecStmt D funs V st s₂ V' st' o

/-- Pointwise semantic equivalence of statement sequences (at a *fixed* function environment — no
hoisting is involved at this level; blocks add it). -/
def EquivStmts (D : Dialect) [DecidableEq D.Value] (ss₁ ss₂ : List (Stmt D.Op)) : Prop :=
  ∀ funs V st V' st' o, ExecStmts D funs V st ss₁ V' st' o ↔ ExecStmts D funs V st ss₂ V' st' o

/-- Equivalence of blocks, *as blocks*: each side hoists its own function definitions. -/
def EquivBlock (D : Dialect) [DecidableEq D.Value] (b₁ b₂ : Block D.Op) : Prop :=
  EquivStmt D (.block b₁) (.block b₂)

/-! ### Basic properties -/

theorem EquivExpr.refl (e : Expr D.Op) : EquivExpr D e e := fun _ _ _ _ => Iff.rfl
theorem EquivExpr.symm {e₁ e₂} (h : EquivExpr D e₁ e₂) : EquivExpr D e₂ e₁ :=
  fun funs V st r => (h funs V st r).symm
theorem EquivExpr.trans {e₁ e₂ e₃} (h₁ : EquivExpr D e₁ e₂) (h₂ : EquivExpr D e₂ e₃) :
    EquivExpr D e₁ e₃ := fun funs V st r => (h₁ funs V st r).trans (h₂ funs V st r)
theorem EquivExpr.mp {e₁ e₂} (h : EquivExpr D e₁ e₂) {funs V st r}
    (h' : EvalExpr D funs V st e₁ r) : EvalExpr D funs V st e₂ r := (h funs V st r).mp h'

theorem EquivArgs.refl (es : List (Expr D.Op)) : EquivArgs D es es := fun _ _ _ _ => Iff.rfl
theorem EquivArgs.symm {es₁ es₂} (h : EquivArgs D es₁ es₂) : EquivArgs D es₂ es₁ :=
  fun funs V st r => (h funs V st r).symm
theorem EquivArgs.trans {es₁ es₂ es₃} (h₁ : EquivArgs D es₁ es₂) (h₂ : EquivArgs D es₂ es₃) :
    EquivArgs D es₁ es₃ := fun funs V st r => (h₁ funs V st r).trans (h₂ funs V st r)
theorem EquivArgs.mp {es₁ es₂} (h : EquivArgs D es₁ es₂) {funs V st r}
    (h' : EvalArgs D funs V st es₁ r) : EvalArgs D funs V st es₂ r := (h funs V st r).mp h'

theorem EquivStmt.refl (s : Stmt D.Op) : EquivStmt D s s := fun _ _ _ _ _ _ => Iff.rfl
theorem EquivStmt.symm {s₁ s₂} (h : EquivStmt D s₁ s₂) : EquivStmt D s₂ s₁ :=
  fun funs V st V' st' o => (h funs V st V' st' o).symm
theorem EquivStmt.trans {s₁ s₂ s₃} (h₁ : EquivStmt D s₁ s₂) (h₂ : EquivStmt D s₂ s₃) :
    EquivStmt D s₁ s₃ := fun funs V st V' st' o =>
  (h₁ funs V st V' st' o).trans (h₂ funs V st V' st' o)
theorem EquivStmt.mp {s₁ s₂} (h : EquivStmt D s₁ s₂) {funs V st V' st' o}
    (h' : ExecStmt D funs V st s₁ V' st' o) : ExecStmt D funs V st s₂ V' st' o :=
  (h funs V st V' st' o).mp h'

theorem EquivStmts.refl (ss : List (Stmt D.Op)) : EquivStmts D ss ss := fun _ _ _ _ _ _ => Iff.rfl
theorem EquivStmts.symm {ss₁ ss₂} (h : EquivStmts D ss₁ ss₂) : EquivStmts D ss₂ ss₁ :=
  fun funs V st V' st' o => (h funs V st V' st' o).symm
theorem EquivStmts.trans {ss₁ ss₂ ss₃} (h₁ : EquivStmts D ss₁ ss₂) (h₂ : EquivStmts D ss₂ ss₃) :
    EquivStmts D ss₁ ss₃ := fun funs V st V' st' o =>
  (h₁ funs V st V' st' o).trans (h₂ funs V st V' st' o)
theorem EquivStmts.mp {ss₁ ss₂} (h : EquivStmts D ss₁ ss₂) {funs V st V' st' o}
    (h' : ExecStmts D funs V st ss₁ V' st' o) : ExecStmts D funs V st ss₂ V' st' o :=
  (h funs V st V' st' o).mp h'

theorem EquivBlock.refl (b : Block D.Op) : EquivBlock D b b := EquivStmt.refl _
theorem EquivBlock.symm {b₁ b₂} (h : EquivBlock D b₁ b₂) : EquivBlock D b₂ b₁ := EquivStmt.symm h
theorem EquivBlock.trans {b₁ b₂ b₃} (h₁ : EquivBlock D b₁ b₂) (h₂ : EquivBlock D b₂ b₃) :
    EquivBlock D b₁ b₃ := EquivStmt.trans h₁ h₂
theorem EquivBlock.mp {b₁ b₂} (h : EquivBlock D b₁ b₂) {funs V st V' st' o}
    (h' : ExecStmt D funs V st (.block b₁) V' st' o) : ExecStmt D funs V st (.block b₂) V' st' o :=
  EquivStmt.mp h h'

/-! ### Behavior: whole-program runs -/

/-- Equivalent top-level blocks produce identical runs (from every initial state). With
determinism (`Run.det`), equivalent programs have identical unique results. -/
theorem EquivBlock.run_iff {p₁ p₂ : Block D.Op} (h : EquivBlock D p₁ p₂) {st0 V' st' o} :
    Run D p₁ st0 V' st' o ↔ Run D p₂ st0 V' st' o :=
  h [] [] st0 V' st' o

/-! ### Congruence: argument lists -/

private theorem argsImp {es₁ es₂ : List (Expr D.Op)}
    (h : Forall₂
      (fun e₁ e₂ => ∀ funs V st r, EvalExpr D funs V st e₁ r → EvalExpr D funs V st e₂ r) es₁ es₂) :
    ∀ funs V st r, EvalArgs D funs V st es₁ r → EvalArgs D funs V st es₂ r := by
  induction h with
  | nil => exact fun _ _ _ _ h => h
  | cons he _ ih =>
      intro funs V st r h
      cases h with
      | argsCons ha hh => exact Step.argsCons (ih _ _ _ _ ha) (he _ _ _ _ hh)
      | argsRestHalt ha => exact Step.argsRestHalt (ih _ _ _ _ ha)
      | argsHeadHalt ha hh => exact Step.argsHeadHalt (ih _ _ _ _ ha) (he _ _ _ _ hh)

private theorem forall₂_symm {α : Type _} {R : α → α → Prop} {l₁ l₂ : List α}
    (hsym : ∀ {a b}, R a b → R b a) (h : Forall₂ R l₁ l₂) : Forall₂ R l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (hsym hh) ih

/-- Pairwise-equivalent argument lists are equivalent. -/
theorem EquivArgs.of_forall₂ {es₁ es₂ : List (Expr D.Op)}
    (h : Forall₂ (EquivExpr D) es₁ es₂) : EquivArgs D es₁ es₂ :=
  fun _ _ _ _ =>
    ⟨argsImp (h.imp fun _ _ he funs V st r => (he funs V st r).mp) _ _ _ _,
     argsImp ((forall₂_symm (fun he => he.symm) h).imp
       fun _ _ he funs V st r => (he funs V st r).mp) _ _ _ _⟩

/-! ### Congruence: expressions -/

private theorem builtinImp {op : D.Op} {es₁ es₂} (ha : EquivArgs D es₁ es₂) {funs V st r}
    (h : EvalExpr D funs V st (.builtin op es₁) r) : EvalExpr D funs V st (.builtin op es₂) r := by
  cases h with
  | builtinOk h₁ h₂ => exact Step.builtinOk (ha.mp h₁) h₂
  | builtinHalt h₁ h₂ => exact Step.builtinHalt (ha.mp h₁) h₂
  | builtinArgsHalt h₁ => exact Step.builtinArgsHalt (ha.mp h₁)

/-- Congruence: a built-in call with equivalent arguments. -/
theorem EquivExpr.builtin_congr (op : D.Op) {es₁ es₂} (h : EquivArgs D es₁ es₂) :
    EquivExpr D (.builtin op es₁) (.builtin op es₂) :=
  fun _ _ _ _ => ⟨builtinImp h, builtinImp h.symm⟩

private theorem callImp {fn : Ident} {es₁ es₂} (ha : EquivArgs D es₁ es₂) {funs V st r}
    (h : EvalExpr D funs V st (.call fn es₁) r) : EvalExpr D funs V st (.call fn es₂) r := by
  cases h with
  | callOk h₁ h₂ h₃ h₄ h₅ => exact Step.callOk (ha.mp h₁) h₂ h₃ h₄ h₅
  | callHalt h₁ h₂ h₃ h₄ => exact Step.callHalt (ha.mp h₁) h₂ h₃ h₄
  | callArgsHalt h₁ => exact Step.callArgsHalt (ha.mp h₁)

/-- Congruence: a user-function call with equivalent arguments. -/
theorem EquivExpr.call_congr (fn : Ident) {es₁ es₂} (h : EquivArgs D es₁ es₂) :
    EquivExpr D (.call fn es₁) (.call fn es₂) :=
  fun _ _ _ _ => ⟨callImp h, callImp h.symm⟩

/-! ### Congruence: statement sequences and blocks -/

private theorem consImp {s₁ s₂ : Stmt D.Op} {ss₁ ss₂} (hs : EquivStmt D s₁ s₂)
    (hss : EquivStmts D ss₁ ss₂) {funs V st V' st' o}
    (h : ExecStmts D funs V st (s₁ :: ss₁) V' st' o) :
    ExecStmts D funs V st (s₂ :: ss₂) V' st' o := by
  cases h with
  | seqCons h₁ h₂ => exact Step.seqCons (hs.mp h₁) (hss.mp h₂)
  | seqStop h₁ h₂ => exact Step.seqStop (hs.mp h₁) h₂

/-- Congruence: sequences extend equivalences element-wise. -/
theorem EquivStmts.cons_congr {s₁ s₂ : Stmt D.Op} {ss₁ ss₂} (hs : EquivStmt D s₁ s₂)
    (hss : EquivStmts D ss₁ ss₂) : EquivStmts D (s₁ :: ss₁) (s₂ :: ss₂) :=
  fun _ _ _ _ _ _ => ⟨consImp hs hss, consImp hs.symm hss.symm⟩

/-- Pairwise-equivalent statement sequences are equivalent. -/
theorem EquivStmts.of_forall₂ {ss₁ ss₂ : List (Stmt D.Op)}
    (h : Forall₂ (EquivStmt D) ss₁ ss₂) : EquivStmts D ss₁ ss₂ := by
  induction h with
  | nil => exact EquivStmts.refl []
  | cons hh _ ih => exact EquivStmts.cons_congr hh ih

private theorem blockImp {b₁ b₂ : Block D.Op} (hss : EquivStmts D b₁ b₂)
    (hh : hoist D b₁ = hoist D b₂) {funs V st V' st' o}
    (h : ExecStmt D funs V st (.block b₁) V' st' o) :
    ExecStmt D funs V st (.block b₂) V' st' o := by
  cases h with
  | block hb => exact Step.block (hh ▸ hss.mp hb)

/-- Congruence for blocks: equivalent bodies that hoist the **same function scope** form
equivalent blocks. The hoist condition is `rfl` whenever the rewrite does not touch top-level
`funDef` statements; rewrites *inside* function bodies need the (deferred) function-environment
relation — see the module docstring. -/
theorem EquivBlock.of_stmts {b₁ b₂ : Block D.Op} (hss : EquivStmts D b₁ b₂)
    (hh : hoist D b₁ = hoist D b₂) : EquivBlock D b₁ b₂ :=
  fun _ _ _ _ _ _ => ⟨blockImp hss hh, blockImp hss.symm hh.symm⟩

/-- Convenience: pairwise-equivalent bodies with equal hoisted scopes form equivalent blocks. -/
theorem EquivBlock.of_forall₂ {b₁ b₂ : Block D.Op} (h : Forall₂ (EquivStmt D) b₁ b₂)
    (hh : hoist D b₁ = hoist D b₂) : EquivBlock D b₁ b₂ :=
  EquivBlock.of_stmts (EquivStmts.of_forall₂ h) hh

/-! ### Congruence: statements -/

private theorem letImp {vars} {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) {funs V st V' st' o}
    (h : ExecStmt D funs V st (.letDecl vars (some e₁)) V' st' o) :
    ExecStmt D funs V st (.letDecl vars (some e₂)) V' st' o := by
  cases h with
  | letVal h₁ h₂ => exact Step.letVal (he.mp h₁) h₂
  | letHalt h₁ => exact Step.letHalt (he.mp h₁)

/-- Congruence: `let` with an equivalent initializer. -/
theorem EquivStmt.letDecl_congr (vars : List Ident) {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) :
    EquivStmt D (.letDecl vars (some e₁)) (.letDecl vars (some e₂)) :=
  fun _ _ _ _ _ _ => ⟨letImp he, letImp he.symm⟩

private theorem assignImp {vars} {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) {funs V st V' st' o}
    (h : ExecStmt D funs V st (.assign vars e₁) V' st' o) :
    ExecStmt D funs V st (.assign vars e₂) V' st' o := by
  cases h with
  | assignVal h₁ h₂ => exact Step.assignVal (he.mp h₁) h₂
  | assignHalt h₁ => exact Step.assignHalt (he.mp h₁)

/-- Congruence: assignment with an equivalent right-hand side. -/
theorem EquivStmt.assign_congr (vars : List Ident) {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) :
    EquivStmt D (.assign vars e₁) (.assign vars e₂) :=
  fun _ _ _ _ _ _ => ⟨assignImp he, assignImp he.symm⟩

private theorem exprStmtImp {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) {funs V st V' st' o}
    (h : ExecStmt D funs V st (.exprStmt e₁) V' st' o) :
    ExecStmt D funs V st (.exprStmt e₂) V' st' o := by
  cases h with
  | exprStmt h₁ => exact Step.exprStmt (he.mp h₁)
  | exprStmtHalt h₁ => exact Step.exprStmtHalt (he.mp h₁)

/-- Congruence: expression statements. -/
theorem EquivStmt.exprStmt_congr {e₁ e₂ : Expr D.Op} (he : EquivExpr D e₁ e₂) :
    EquivStmt D (.exprStmt e₁) (.exprStmt e₂) :=
  fun _ _ _ _ _ _ => ⟨exprStmtImp he, exprStmtImp he.symm⟩

private theorem condImp {c₁ c₂ : Expr D.Op} {b₁ b₂ : Block D.Op} (hc : EquivExpr D c₁ c₂)
    (hb : EquivBlock D b₁ b₂) {funs V st V' st' o}
    (h : ExecStmt D funs V st (.cond c₁ b₁) V' st' o) :
    ExecStmt D funs V st (.cond c₂ b₂) V' st' o := by
  cases h with
  | ifTrue h₁ h₂ h₃ => exact Step.ifTrue (hc.mp h₁) h₂ (hb.mp h₃)
  | ifFalse h₁ h₂ => exact Step.ifFalse (hc.mp h₁) h₂
  | ifHalt h₁ => exact Step.ifHalt (hc.mp h₁)

/-- Congruence: `if` with an equivalent condition and body. -/
theorem EquivStmt.cond_congr {c₁ c₂ : Expr D.Op} {b₁ b₂ : Block D.Op} (hc : EquivExpr D c₁ c₂)
    (hb : EquivBlock D b₁ b₂) : EquivStmt D (.cond c₁ b₁) (.cond c₂ b₂) :=
  fun _ _ _ _ _ _ => ⟨condImp hc hb, condImp hc.symm hb.symm⟩

/-- `selectSwitch` respects pairwise-related cases: equal labels, equivalent blocks. -/
private theorem selectSwitch_congr {cv : D.Value} {cs₁ cs₂ : List (Literal × Block D.Op)}
    {dflt₁ dflt₂ : Option (Block D.Op)}
    (hcases : Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs₁ cs₂)
    (hdflt : EquivBlock D (dflt₁.getD []) (dflt₂.getD [])) :
    EquivBlock D (selectSwitch D cv cs₁ dflt₁) (selectSwitch D cv cs₂ dflt₂) := by
  induction hcases with
  | nil => simpa [selectSwitch] using hdflt
  | @cons p q t₁ t₂ hpq ht ih =>
      obtain ⟨hl, hb⟩ := hpq
      by_cases hcv : cv = D.litValue p.1
      · have h₁ : List.find? (fun r => decide (cv = D.litValue r.1)) (p :: t₁) = some p :=
          List.find?_cons_of_pos (by simp [hcv])
        have h₂ : List.find? (fun r => decide (cv = D.litValue r.1)) (q :: t₂) = some q :=
          List.find?_cons_of_pos (by simp [← hl, hcv])
        simpa only [selectSwitch, h₁, h₂] using hb
      · have h₁ : List.find? (fun r => decide (cv = D.litValue r.1)) (p :: t₁) =
            List.find? (fun r => decide (cv = D.litValue r.1)) t₁ :=
          List.find?_cons_of_neg (by simp [hcv])
        have h₂ : List.find? (fun r => decide (cv = D.litValue r.1)) (q :: t₂) =
            List.find? (fun r => decide (cv = D.litValue r.1)) t₂ :=
          List.find?_cons_of_neg (by simp [← hl, hcv])
        simpa only [selectSwitch, h₁, h₂] using ih

private theorem switchImp {c₁ c₂ : Expr D.Op} {cs₁ cs₂ dflt₁ dflt₂} (hc : EquivExpr D c₁ c₂)
    (hsel : ∀ cv, EquivBlock D (selectSwitch D cv cs₁ dflt₁) (selectSwitch D cv cs₂ dflt₂))
    {funs V st V' st' o} (h : ExecStmt D funs V st (.switch c₁ cs₁ dflt₁) V' st' o) :
    ExecStmt D funs V st (.switch c₂ cs₂ dflt₂) V' st' o := by
  cases h with
  | switchExec h₁ h₂ => exact Step.switchExec (hc.mp h₁) ((hsel _).mp h₂)
  | switchHalt h₁ => exact Step.switchHalt (hc.mp h₁)

/-- Congruence: `switch` with an equivalent scrutinee, pairwise-related cases (equal labels,
equivalent blocks), and equivalent defaults. -/
theorem EquivStmt.switch_congr {c₁ c₂ : Expr D.Op} {cs₁ cs₂ : List (Literal × Block D.Op)}
    {dflt₁ dflt₂ : Option (Block D.Op)} (hc : EquivExpr D c₁ c₂)
    (hcases : Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs₁ cs₂)
    (hdflt : EquivBlock D (dflt₁.getD []) (dflt₂.getD [])) :
    EquivStmt D (.switch c₁ cs₁ dflt₁) (.switch c₂ cs₂ dflt₂) := by
  have hcases' := forall₂_symm
    (R := fun (p q : Literal × Block D.Op) => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
    (fun h => ⟨h.1.symm, h.2.symm⟩) hcases
  exact fun _ _ _ _ _ _ =>
    ⟨switchImp hc (fun cv => selectSwitch_congr hcases hdflt),
     switchImp hc.symm (fun cv => selectSwitch_congr hcases' hdflt.symm)⟩

private theorem loopImp {c₁ c₂ : Expr D.Op} {post₁ post₂ body₁ body₂ : Block D.Op}
    (hc : EquivExpr D c₁ c₂) (hpost : EquivBlock D post₁ post₂) (hbody : EquivBlock D body₁ body₂) :
    ∀ {funs V st code res}, Step D funs V st code res →
      code = .loop c₁ post₁ body₁ →
      Step D funs V st (.loop c₂ post₂ body₂) res := by
  intro funs V st code res h
  induction h
  case loopDone hcv hz _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopDone (hc.mp hcv) hz
  case loopCondHalt hcv _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopCondHalt (hc.mp hcv)
  case loopStep hcv hnz hb hob hp _ _ _ _ ihr =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopStep (hc.mp hcv) hnz (hbody.mp hb) hob (hpost.mp hp) (ihr rfl)
  case loopPostHalt hcv hnz hb hob hp _ _ _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopPostHalt (hc.mp hcv) hnz (hbody.mp hb) hob (hpost.mp hp)
  case loopBreak hcv hnz hb _ _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopBreak (hc.mp hcv) hnz (hbody.mp hb)
  case loopLeave hcv hnz hb _ _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopLeave (hc.mp hcv) hnz (hbody.mp hb)
  case loopBodyHalt hcv hnz hb _ _ =>
      intro hcode
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopBodyHalt (hc.mp hcv) hnz (hbody.mp hb)
  all_goals exact nofun

private theorem forImp {init} {c₁ c₂ : Expr D.Op} {post₁ post₂ body₁ body₂ : Block D.Op}
    (hc : EquivExpr D c₁ c₂) (hpost : EquivBlock D post₁ post₂) (hbody : EquivBlock D body₁ body₂)
    {funs V st V' st' o} (h : ExecStmt D funs V st (.forLoop init c₁ post₁ body₁) V' st' o) :
    ExecStmt D funs V st (.forLoop init c₂ post₂ body₂) V' st' o := by
  cases h with
  | forLoop hinit hloop => exact Step.forLoop hinit (loopImp hc hpost hbody hloop rfl)
  | forInitHalt hinit => exact Step.forInitHalt hinit

/-- Congruence: `for` with an equivalent condition, post-block, and body (the `init` block is
fixed — it is both executed *and* hoisted, so changing it needs `EquivBlock.of_stmts`-style side
conditions at the statement level). -/
theorem EquivStmt.forLoop_congr (init : Block D.Op) {c₁ c₂ : Expr D.Op}
    {post₁ post₂ body₁ body₂ : Block D.Op} (hc : EquivExpr D c₁ c₂)
    (hpost : EquivBlock D post₁ post₂) (hbody : EquivBlock D body₁ body₂) :
    EquivStmt D (.forLoop init c₁ post₁ body₁) (.forLoop init c₂ post₂ body₂) :=
  fun _ _ _ _ _ _ =>
    ⟨forImp hc hpost hbody, forImp hc.symm hpost.symm hbody.symm⟩

end YulSemantics
