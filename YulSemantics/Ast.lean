/-!
# YulSemantics.Ast

The abstract syntax tree of Yul, together with the control-flow `Outcome` produced by executing a
statement. See `DESIGN.md` for the overall design.

This module is deliberately dependency-light (no Mathlib): it is pure syntax.

## Modeling decisions (see `DESIGN.md`)

* **Built-ins are a first-class enum, and the AST is parameterized over it.** The AST is parameterized over an
  operation type `Op`; a call is either a dialect built-in (`Expr.builtin op args`, with `op : Op`)
  or a user-defined function call (`Expr.call fn args`, with `fn : Ident`). The core stays
  dialect-agnostic (it is generic in the *type* `Op`), while dialect-specific optimizations can
  pattern-match on `Op` structurally and dialect-agnostic passes are `∀ Op, …` — the type system
  enforces the separation. Name→`Op` resolution happens at parse time, sound because Yul
  forbids user functions from shadowing built-ins.
* **Single-sorted.** The EVM dialect has one type (`u256`); type annotations carry no semantic
  content and are omitted (the DSL parses and discards optional `: TypeName`).
* **Dialect-agnostic literals.** A `Literal` holds only *syntactic* data; a `Dialect` interprets it
  (`litValue`).
* **`Outcome` is dialect-agnostic.** Halting built-ins signal `.halt`; the payload lives in the
  machine state, not in `Outcome`.
-/

namespace YulSemantics

/-- Yul identifiers (variable, function, and object names). Yul allows `[a-zA-Z_$][a-zA-Z_$0-9.]*`;
we keep them as raw strings and rely on a freshness discipline for α-renaming later. -/
abbrev Ident := String

/-- A Yul literal. Purely syntactic; interpretation into a value is a `Dialect` concern.

* `number n` — a decimal or hexadecimal number literal (both denote the same `Nat`).
* `bool b`   — the `true` / `false` literals.
* `string s` — a (short) string literal (Yul string literals are byte strings of at most 32 bytes;
  modeled as `String` for now). -/
inductive Literal
  | number (n : Nat)
  | bool   (b : Bool)
  | string (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- A Yul expression, parameterized over the dialect's built-in operation type `Op`.

* `lit` / `var` — a literal or variable reference;
* `builtin op args` — a call to the dialect built-in `op`;
* `call fn args` — a call to the *user-defined* function named `fn`.

Syntactic equality is executable, which lets clients certify that a concrete
parser result is the same readable AST used by a proof. -/
inductive Expr (Op : Type)
  | lit     (l : Literal)
  | var     (x : Ident)
  | builtin (op : Op) (args : List (Expr Op))
  | call    (fn : Ident) (args : List (Expr Op))
  deriving Repr, Inhabited

/-- A Yul statement, parameterized over the built-in operation type `Op`.

Note on scoping (enforced by the semantics, not by the AST):
* function definitions are visible throughout their enclosing block (forward references allowed);
* variables declared in a `forLoop`'s `init` block are visible in its `cond`, `post`, and `body`. -/
inductive Stmt (Op : Type)
  /-- `{ body }` — a nested block, introducing a new scope. -/
  | block   (body : List (Stmt Op))
  /-- `function name(params) -> rets { body }`. `rets` may be empty; multiple returns allowed. -/
  | funDef  (name : Ident) (params rets : List Ident) (body : List (Stmt Op))
  /-- `let vars := val` or, when `val = none`, `let vars` (zero-initialized by the dialect). -/
  | letDecl (vars : List Ident) (val : Option (Expr Op))
  /-- `vars := val` — assignment to already-declared variables. -/
  | assign  (vars : List Ident) (val : Expr Op)
  /-- `if c { body }`. Yul has no `else`. -/
  | cond    (c : Expr Op) (body : List (Stmt Op))
  /-- `switch c (case lit { … })* (default { … })?`. -/
  | switch  (c : Expr Op) (cases : List (Literal × List (Stmt Op))) (dflt : Option (List (Stmt Op)))
  /-- `for { init } c { post } { body }`. -/
  | forLoop (init : List (Stmt Op)) (c : Expr Op) (post : List (Stmt Op)) (body : List (Stmt Op))
  /-- An expression evaluated for its effects; it must produce no values. -/
  | exprStmt (e : Expr Op)
  /-- `break` — exit the enclosing `for` loop. -/
  | «break»
  /-- `continue` — skip to the `post` block of the enclosing `for` loop. -/
  | «continue»
  /-- `leave` — return from the enclosing function with the current output-variable values. -/
  | leave
  deriving Repr, Inhabited

/-- A block is a sequence of statements. -/
abbrev Block (Op : Type) := List (Stmt Op)

/-! ### Executable syntactic equality

The standard deriving handlers cannot construct equality through the mutually
recursive `List` occurrences in this AST.  These small boolean comparators are
the executable substitute.  Their one-way soundness theorems below are enough
to turn a native check of a concrete parser result into propositional equality.
-/

namespace SyntaxEq

variable {Op : Type} [BEq Op]

mutual
def exprBeq : Expr Op → Expr Op → Bool
  | .lit left, .lit right => left == right
  | .var left, .var right => left == right
  | .builtin leftOp leftArgs, .builtin rightOp rightArgs =>
      leftOp == rightOp && exprsBeq leftArgs rightArgs
  | .call leftName leftArgs, .call rightName rightArgs =>
      leftName == rightName && exprsBeq leftArgs rightArgs
  | _, _ => false

def exprsBeq : List (Expr Op) → List (Expr Op) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      exprBeq left right && exprsBeq leftRest rightRest
  | _, _ => false
end

def optionalExprBeq : Option (Expr Op) → Option (Expr Op) → Bool
  | none, none => true
  | some left, some right => exprBeq left right
  | _, _ => false

mutual
def stmtBeq : Stmt Op → Stmt Op → Bool
  | .block left, .block right => stmtsBeq left right
  | .funDef ln lp lr lb, .funDef rn rp rr rb =>
      ln == rn && lp == rp && lr == rr && stmtsBeq lb rb
  | .letDecl lv le, .letDecl rv re => lv == rv && optionalExprBeq le re
  | .assign lv le, .assign rv re => lv == rv && exprBeq le re
  | .cond le lb, .cond re rb => exprBeq le re && stmtsBeq lb rb
  | .switch le lc ld, .switch re rc rd =>
      exprBeq le re && casesBeq lc rc && optionalStmtsBeq ld rd
  | .forLoop li lc lp lb, .forLoop ri rc rp rb =>
      stmtsBeq li ri && exprBeq lc rc && stmtsBeq lp rp && stmtsBeq lb rb
  | .exprStmt left, .exprStmt right => exprBeq left right
  | .break, .break | .continue, .continue | .leave, .leave => true
  | _, _ => false

def stmtsBeq : List (Stmt Op) → List (Stmt Op) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      stmtBeq left right && stmtsBeq leftRest rightRest
  | _, _ => false

def casesBeq : List (Literal × Block Op) → List (Literal × Block Op) → Bool
  | [], [] => true
  | (leftLit, leftBody) :: leftRest, (rightLit, rightBody) :: rightRest =>
      leftLit == rightLit && stmtsBeq leftBody rightBody &&
        casesBeq leftRest rightRest
  | _, _ => false

def optionalStmtsBeq : Option (Block Op) → Option (Block Op) → Bool
  | none, none => true
  | some left, some right => stmtsBeq left right
  | _, _ => false
end

section Soundness

variable [LawfulBEq Op]

set_option linter.unusedSectionVars false in
mutual
theorem exprBeq_eq : ∀ (left right : Expr Op),
    exprBeq left right = true → left = right
  | .lit left, right, h => by
      cases right with
      | lit right => exact congrArg Expr.lit (eq_of_beq h)
      | var | builtin | call => exact Bool.noConfusion h
  | .var left, right, h => by
      cases right with
      | var right => exact congrArg Expr.var (eq_of_beq h)
      | lit | builtin | call => exact Bool.noConfusion h
  | .builtin leftOp leftArgs, right, h => by
      cases right with
      | builtin rightOp rightArgs =>
          simp only [exprBeq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, exprsBeq_eq leftArgs rightArgs h.2]
      | lit | var | call => exact Bool.noConfusion h
  | .call leftName leftArgs, right, h => by
      cases right with
      | call rightName rightArgs =>
          simp only [exprBeq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, exprsBeq_eq leftArgs rightArgs h.2]
      | lit | var | builtin => exact Bool.noConfusion h

theorem exprsBeq_eq : ∀ (left right : List (Expr Op)),
    exprsBeq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [exprsBeq, Bool.and_eq_true] at h
      rw [exprBeq_eq left right h.1, exprsBeq_eq leftRest rightRest h.2]
  | [], _ :: _, h | _ :: _, [], h => Bool.noConfusion h
end

theorem optionalExprBeq_eq : ∀ (left right : Option (Expr Op)),
    optionalExprBeq left right = true → left = right
  | none, none, _ => rfl
  | some left, some right, h => congrArg some (exprBeq_eq left right h)
  | none, some _, h | some _, none, h => absurd h Bool.false_ne_true

set_option linter.unusedSectionVars false in
mutual
theorem stmtBeq_eq : ∀ (left right : Stmt Op),
    stmtBeq left right = true → left = right
  | .block left, right, h => by
      cases right with
      | block right =>
          exact congrArg Stmt.block (stmtsBeq_eq left right (by simpa only [stmtBeq] using h))
      | funDef | letDecl | assign | cond | switch | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .funDef ln lp lr lb, right, h => by
      cases right with
      | funDef rn rp rr rb =>
          simp only [stmtBeq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1.1, h.1.1.2, h.1.2, stmtsBeq_eq lb rb h.2]
      | block | letDecl | assign | cond | switch | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .letDecl lv le, right, h => by
      cases right with
      | letDecl rv re =>
          simp only [stmtBeq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, optionalExprBeq_eq le re h.2]
      | block | funDef | assign | cond | switch | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .assign lv le, right, h => by
      cases right with
      | assign rv re =>
          simp only [stmtBeq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, exprBeq_eq le re h.2]
      | block | funDef | letDecl | cond | switch | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .cond le lb, right, h => by
      cases right with
      | cond re rb =>
          simp only [stmtBeq, Bool.and_eq_true] at h
          rw [exprBeq_eq le re h.1, stmtsBeq_eq lb rb h.2]
      | block | funDef | letDecl | assign | switch | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .switch le lc ld, right, h => by
      cases right with
      | switch re rc rd =>
          simp only [stmtBeq, Bool.and_eq_true] at h
          rw [exprBeq_eq le re h.1.1, casesBeq_eq lc rc h.1.2,
            optionalStmtsBeq_eq ld rd h.2]
      | block | funDef | letDecl | assign | cond | forLoop | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .forLoop li lc lp lb, right, h => by
      cases right with
      | forLoop ri rc rp rb =>
          simp only [stmtBeq, Bool.and_eq_true] at h
          rw [stmtsBeq_eq li ri h.1.1.1, exprBeq_eq lc rc h.1.1.2,
            stmtsBeq_eq lp rp h.1.2, stmtsBeq_eq lb rb h.2]
      | block | funDef | letDecl | assign | cond | switch | exprStmt |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .exprStmt left, right, h => by
      cases right with
      | exprStmt right =>
          exact congrArg Stmt.exprStmt (exprBeq_eq left right (by simpa only [stmtBeq] using h))
      | block | funDef | letDecl | assign | cond | switch | forLoop |
          «break» | «continue» | leave => simp [stmtBeq] at h
  | .break, right, h => by
      cases right with
      | «break» => rfl
      | block | funDef | letDecl | assign | cond | switch | forLoop | exprStmt |
          «continue» | leave => simp [stmtBeq] at h
  | .continue, right, h => by
      cases right with
      | «continue» => rfl
      | block | funDef | letDecl | assign | cond | switch | forLoop | exprStmt |
          «break» | leave => simp [stmtBeq] at h
  | .leave, right, h => by
      cases right with
      | leave => rfl
      | block | funDef | letDecl | assign | cond | switch | forLoop | exprStmt |
          «break» | «continue» => simp [stmtBeq] at h

theorem stmtsBeq_eq : ∀ (left right : List (Stmt Op)),
    stmtsBeq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [stmtsBeq, Bool.and_eq_true] at h
      rw [stmtBeq_eq left right h.1, stmtsBeq_eq leftRest rightRest h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [stmtsBeq] at h

theorem casesBeq_eq : ∀ (left right : List (Literal × Block Op)),
    casesBeq left right = true → left = right
  | [], [], _ => rfl
  | (leftLit, leftBody) :: leftRest,
      (rightLit, rightBody) :: rightRest, h => by
      simp only [casesBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, stmtsBeq_eq leftBody rightBody h.1.2,
        casesBeq_eq leftRest rightRest h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [casesBeq] at h

theorem optionalStmtsBeq_eq : ∀ (left right : Option (Block Op)),
    optionalStmtsBeq left right = true → left = right
  | none, none, _ => rfl
  | some left, some right, h => by
      simp only [optionalStmtsBeq] at h
      exact congrArg some (stmtsBeq_eq left right h)
  | none, some _, h | some _, none, h => by simp [optionalStmtsBeq] at h
end

end Soundness

end SyntaxEq

/-- The contents of a `data` segment of an object: raw bytes, written as a hex or string literal. -/
inductive Data
  | hex    (bytes : List UInt8)
  | string (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- A Yul object: a named `code` block together with nested sub-objects and named data segments.
Parameterized over the built-in operation type `Op`. -/
inductive Object (Op : Type)
  | mk (name : String) (code : Block Op) (subObjects : List (Object Op)) (data : List (String × Data))
  deriving Repr, Inhabited

namespace Object
variable {Op : Type}

/-- The object's name. -/
def name : Object Op → String                    | .mk n _ _ _ => n
/-- The object's top-level `code` block. -/
def codeBlock : Object Op → Block Op             | .mk _ c _ _ => c
/-- The object's nested sub-objects. -/
def subObjects : Object Op → List (Object Op)    | .mk _ _ s _ => s
/-- The object's named data segments. (Named `dataSegs`, not `data`, since `data` is a reserved
keyword in the DSL — see `YulSemantics.Syntax`.) -/
def dataSegs : Object Op → List (String × Data)  | .mk _ _ _ d => d

end Object

/-- The control-flow outcome of executing a statement or block. Non-`normal` outcomes propagate
outward until caught at the appropriate boundary:

* `.break` / `.continue` are caught by the enclosing `forLoop`;
* `.leave` is caught by the enclosing function body;
* `.halt` (from a halting built-in such as `return`/`revert`/`stop`) propagates all the way to the
  top of execution — its payload lives in the machine state, not here. -/
inductive Outcome
  | normal
  | «break»
  | «continue»
  | leave
  | halt
  deriving Repr, DecidableEq, Inhabited

end YulSemantics
