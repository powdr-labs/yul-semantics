/-!
# YulSemantics.Ast

The abstract syntax tree of Yul, together with the control-flow `Outcome` produced by executing a
statement. See `DESIGN.md` for the overall design.

This module is deliberately dependency-light (no Mathlib): it is pure syntax.

## Modeling decisions (see `DESIGN.md`)

* **Built-ins are a first-class enum, parameterized (Option D).** The AST is parameterized over an
  operation type `Op`; a call is either a dialect built-in (`Expr.builtin op args`, with `op : Op`)
  or a user-defined function call (`Expr.call fn args`, with `fn : Ident`). The core stays
  dialect-agnostic (it is generic in the *type* `Op`), while dialect-specific optimizations can
  pattern-match on `Op` structurally and dialect-agnostic passes are `∀ Op, …` — the type system
  enforces the separation. Name→`Op` resolution happens at parse time (Phase 4), sound because Yul
  forbids user functions from shadowing built-ins.
* **Single-sorted.** The EVM dialect has one type (`u256`); type annotations carry no semantic
  content and are omitted (the DSL parses and discards optional `: TypeName`).
* **Dialect-agnostic literals.** A `Literal` holds only *syntactic* data; a `Dialect` interprets it
  (`litValue`, Phase 2).
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

`DecidableEq`/`BEq` are intentionally not derived (the deriving handlers do not support recursion
through `List`); syntactic equality is first needed for the optimization proofs (Phase 5). -/
inductive Expr (Op : Type)
  | lit     (l : Literal)
  | var     (x : Ident)
  | builtin (op : Op) (args : List (Expr Op))
  | call    (fn : Ident) (args : List (Expr Op))
  deriving Repr, Inhabited

/-- A Yul statement, parameterized over the built-in operation type `Op`.

Note on scoping (enforced by the semantics in Phase 3, not by the AST):
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
def name : Object Op → String                | .mk n _ _ _ => n
/-- The object's top-level `code` block. -/
def code : Object Op → Block Op              | .mk _ c _ _ => c
/-- The object's nested sub-objects. -/
def subObjects : Object Op → List (Object Op) | .mk _ _ s _ => s
/-- The object's named data segments. -/
def data : Object Op → List (String × Data)   | .mk _ _ _ d => d

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
