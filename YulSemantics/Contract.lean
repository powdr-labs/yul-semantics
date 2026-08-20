import YulSemantics.BigStep

/-!
# Relational execution contracts

This module adds a proof-facing layer over the concrete big-step semantics.  A contract exposes
only a precondition and a postcondition while retaining the authoritative `Run`/`Step` derivation
as evidence.  In particular, clients need not name the complete final state in theorem statements
or repeatedly unfold it while composing proofs.

`RunContract` is the whole-program interface.  `StmtContract` and `StmtsContract` provide the
same abstraction inside a program, where sequential and block composition are available.
-/

namespace YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- A Hoare-style contract for a complete Yul run.  The postcondition may relate the initial
state to the final variable environment, state, and control-flow outcome. -/
def RunContract (program : Block D.Op) (pre : D.State → Prop)
    (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ initial, pre initial →
    ∃ finalEnv final outcome,
      Run D program initial finalEnv final outcome ∧
      post initial finalEnv final outcome

namespace RunContract

/-- Establish a contract from a pointwise source-execution proof. -/
theorem intro {program : Block D.Op} {pre : D.State → Prop}
    {post : D.State → VEnv D → D.State → Outcome → Prop}
    (h : ∀ initial, pre initial →
      ∃ finalEnv final outcome,
        Run D program initial finalEnv final outcome ∧
        post initial finalEnv final outcome) :
    RunContract program pre post :=
  h

/-- Strengthen the precondition and weaken the postcondition. -/
theorem consequence {program : Block D.Op}
    {pre pre' : D.State → Prop}
    {post post' : D.State → VEnv D → D.State → Outcome → Prop}
    (h : RunContract program pre post)
    (hpre : ∀ initial, pre' initial → pre initial)
    (hpost : ∀ initial finalEnv final outcome,
      pre' initial → post initial finalEnv final outcome →
        post' initial finalEnv final outcome) :
    RunContract program pre' post' := by
  intro initial hi
  obtain ⟨finalEnv, final, outcome, hrun, hp⟩ := h initial (hpre initial hi)
  exact ⟨finalEnv, final, outcome, hrun, hpost initial finalEnv final outcome hi hp⟩

/-- Keep an additional property of the final execution without exposing its concrete value. -/
theorem and_post {program : Block D.Op} {pre : D.State → Prop}
    {post extra : D.State → VEnv D → D.State → Outcome → Prop}
    (h : RunContract program pre post)
    (hextra : ∀ initial finalEnv final outcome,
      pre initial → Run D program initial finalEnv final outcome →
        post initial finalEnv final outcome →
        extra initial finalEnv final outcome) :
    RunContract program pre (fun initial finalEnv final outcome =>
      post initial finalEnv final outcome ∧ extra initial finalEnv final outcome) := by
  intro initial hi
  obtain ⟨finalEnv, final, outcome, hrun, hp⟩ := h initial hi
  exact ⟨finalEnv, final, outcome, hrun, hp,
    hextra initial finalEnv final outcome hi hrun hp⟩

/-- Transport a contract across a pointwise implication between whole-program runs.  This is the
standard bridge used by verified source transformations. -/
theorem map_program {program program' : Block D.Op} {pre : D.State → Prop}
    {post : D.State → VEnv D → D.State → Outcome → Prop}
    (hmap : ∀ initial finalEnv final outcome,
      Run D program initial finalEnv final outcome →
      Run D program' initial finalEnv final outcome)
    (h : RunContract program pre post) :
    RunContract program' pre post := by
  intro initial hi
  obtain ⟨finalEnv, final, outcome, hrun, hp⟩ := h initial hi
  exact ⟨finalEnv, final, outcome, hmap initial finalEnv final outcome hrun, hp⟩

end RunContract

/-- A contract for one statement under a fixed function environment. -/
def StmtContract (funs : FunEnv D) (stmt : Stmt D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ initialEnv initial, pre initialEnv initial →
    ∃ finalEnv final outcome,
      ExecStmt D funs initialEnv initial stmt finalEnv final outcome ∧
      post initialEnv initial finalEnv final outcome

/-- A contract for a statement sequence under a fixed function environment. -/
def StmtsContract (funs : FunEnv D) (stmts : Block D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ initialEnv initial, pre initialEnv initial →
    ∃ finalEnv final outcome,
      ExecStmts D funs initialEnv initial stmts finalEnv final outcome ∧
      post initialEnv initial finalEnv final outcome

namespace StmtContract

/-- Strengthen a statement precondition and weaken its postcondition. -/
theorem consequence {funs : FunEnv D} {stmt : Stmt D.Op}
    {pre pre' : VEnv D → D.State → Prop}
    {post post' : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtContract funs stmt pre post)
    (hpre : ∀ V st, pre' V st → pre V st)
    (hpost : ∀ V st V' st' outcome,
      pre' V st → post V st V' st' outcome → post' V st V' st' outcome) :
    StmtContract funs stmt pre' post' := by
  intro V st hi
  obtain ⟨V', st', outcome, hexec, hp⟩ := h V st (hpre V st hi)
  exact ⟨V', st', outcome, hexec, hpost V st V' st' outcome hi hp⟩

end StmtContract

namespace StmtsContract

/-- The empty sequence preserves its environment and state and returns normally. -/
theorem nil {funs : FunEnv D} (pre : VEnv D → D.State → Prop) :
    StmtsContract funs [] pre
      (fun V st V' st' outcome => V' = V ∧ st' = st ∧ outcome = .normal) := by
  intro V st _
  exact ⟨V, st, .normal, Step.seqNil, rfl, rfl, rfl⟩

/-- Strengthen a sequence precondition and weaken its postcondition. -/
theorem consequence {funs : FunEnv D} {stmts : Block D.Op}
    {pre pre' : VEnv D → D.State → Prop}
    {post post' : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtsContract funs stmts pre post)
    (hpre : ∀ V st, pre' V st → pre V st)
    (hpost : ∀ V st V' st' outcome,
      pre' V st → post V st V' st' outcome → post' V st V' st' outcome) :
    StmtsContract funs stmts pre' post' := by
  intro V st hi
  obtain ⟨V', st', outcome, hexec, hp⟩ := h V st (hpre V st hi)
  exact ⟨V', st', outcome, hexec, hpost V st V' st' outcome hi hp⟩

/-- Prefix a normally-returning statement contract to a sequence contract.  `mid` is the
intermediate assertion; the tail contract may retain the original state through its closure. -/
theorem cons {funs : FunEnv D} {stmt : Stmt D.Op} {stmts : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (head : StmtContract funs stmt pre
      (fun _ _ V' st' outcome => outcome = .normal ∧ mid V' st'))
    (tail : ∀ V st, pre V st →
      StmtsContract funs stmts mid (fun _ _ V' st' outcome => post V st V' st' outcome)) :
    StmtsContract funs (stmt :: stmts) pre post := by
  intro V st hi
  obtain ⟨V₁, st₁, outcome₁, hhead, houtcome, hmid⟩ := head V st hi
  subst outcome₁
  obtain ⟨V₂, st₂, outcome₂, htail, hp⟩ := tail V st hi V₁ st₁ hmid
  exact ⟨V₂, st₂, outcome₂, Step.seqCons hhead htail, hp⟩

/-- Lift a statement-sequence contract through the lexical scope introduced by a block. -/
theorem block {funs : FunEnv D} {body : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtsContract (hoist D body :: funs) body pre
      (fun V st V' st' outcome => post V st (restore V V') st' outcome)) :
    StmtContract funs (.block body) pre post := by
  intro V st hi
  obtain ⟨V', st', outcome, hexec, hp⟩ := h V st hi
  exact ⟨restore V V', st', outcome, Step.block hexec, hp⟩

end StmtsContract

/-- View a statement-sequence contract for the top-level hoisted scope as a whole-program
contract.  This is the final composition step used by source-level program proofs. -/
theorem RunContract.of_stmts {program : Block D.Op} {pre : D.State → Prop}
    {post : D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtsContract [hoist D program] program (fun V st => V = [] ∧ pre st)
      (fun _ st V' st' outcome => post st (restore [] V') st' outcome)) :
    RunContract program pre post := by
  intro st hi
  obtain ⟨V', st', outcome, hexec, hp⟩ := h [] st ⟨rfl, hi⟩
  exact ⟨restore [] V', st', outcome, Step.block hexec, hp⟩

end YulSemantics
