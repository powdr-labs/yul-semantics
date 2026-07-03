import YulSemantics.Syntax

/-!
# YulSemantics.PrettyPrint

A pretty-printer from Yul ASTs back to concrete Yul source. Dialect-generic: parameterized by a
built-in name function `Op → String` (`EVM.opName` for the EVM dialect; the `EVM.print*` wrappers
below specialize it).

**Untrusted utility**: nothing in the semantics or the proofs depends on it. Its purpose is
inspecting optimizer output, producing Yul that external tools (`solc --strict-assembly`) can
consume, and future per-pass pipeline dumps. A round-trip theorem is not currently statable — the
`yul%` DSL is an elaboration-time macro, not a runtime parser; if a runtime parser is added later,
`parse (print p) = some p` becomes the verification story for both.

Caveats (fine for the intended uses, noted for honesty):
* numbers print in decimal;
* string literals are quoted naively (no escaping); data segments print as `"…"`/`hex"…"`;
* identifiers are printed verbatim — output is lexically valid Yul only if they are;
* objects print their `code`, then sub-objects, then data (source interleaving of the latter two
  is not preserved — the `Object` AST does not record it).
-/

namespace YulSemantics

variable {Op : Type}

/-- Indentation: four spaces per level. -/
def pad (n : Nat) : String := "".pushn ' ' (4 * n)

/-- Print a literal (numbers in decimal). -/
def ppLiteral : Literal → String
  | .number n => toString n
  | .bool true => "true"
  | .bool false => "false"
  | .string s => "\"" ++ s ++ "\""

mutual

/-- Print an expression. -/
def ppExpr (pOp : Op → String) : Expr Op → String
  | .lit l => ppLiteral l
  | .var x => x
  | .builtin op args => pOp op ++ "(" ++ ppExprs pOp args ++ ")"
  | .call fn args => fn ++ "(" ++ ppExprs pOp args ++ ")"

/-- Print a comma-separated argument list. -/
def ppExprs (pOp : Op → String) : List (Expr Op) → String
  | [] => ""
  | [e] => ppExpr pOp e
  | e :: es => ppExpr pOp e ++ ", " ++ ppExprs pOp es

end

mutual

/-- Print a single statement at indentation level `ind` (no leading indentation; the caller adds
it). Nested blocks indent one level deeper and close at level `ind`. -/
def ppStmt (pOp : Op → String) (ind : Nat) : Stmt Op → String
  | .block body =>
      "{\n" ++ ppStmts pOp (ind + 1) body ++ pad ind ++ "}"
  | .funDef n ps rs b =>
      "function " ++ n ++ "(" ++ String.intercalate ", " ps ++ ")" ++
        (if rs.isEmpty then " " else " -> " ++ String.intercalate ", " rs ++ " ") ++
        "{\n" ++ ppStmts pOp (ind + 1) b ++ pad ind ++ "}"
  | .letDecl vars none => "let " ++ String.intercalate ", " vars
  | .letDecl vars (some e) =>
      "let " ++ String.intercalate ", " vars ++ " := " ++ ppExpr pOp e
  | .assign vars e => String.intercalate ", " vars ++ " := " ++ ppExpr pOp e
  | .cond c body =>
      "if " ++ ppExpr pOp c ++ " {\n" ++ ppStmts pOp (ind + 1) body ++ pad ind ++ "}"
  | .switch c cs dflt =>
      "switch " ++ ppExpr pOp c ++ ppCases pOp ind cs ++
        (match dflt with
         | none => ""
         | some d => "\n" ++ pad ind ++ "default {\n" ++ ppStmts pOp (ind + 1) d ++ pad ind ++ "}")
  | .forLoop init c post body =>
      "for {\n" ++ ppStmts pOp (ind + 1) init ++ pad ind ++ "} " ++ ppExpr pOp c ++ " {\n" ++
        ppStmts pOp (ind + 1) post ++ pad ind ++ "} {\n" ++
        ppStmts pOp (ind + 1) body ++ pad ind ++ "}"
  | .exprStmt e => ppExpr pOp e
  | .«break» => "break"
  | .«continue» => "continue"
  | .leave => "leave"

/-- Print a statement sequence: one statement per line, each indented at level `ind`. -/
def ppStmts (pOp : Op → String) (ind : Nat) : List (Stmt Op) → String
  | [] => ""
  | s :: ss => pad ind ++ ppStmt pOp ind s ++ "\n" ++ ppStmts pOp ind ss

/-- Print `switch` cases, one per line at level `ind`. -/
def ppCases (pOp : Op → String) (ind : Nat) : List (Literal × Block Op) → String
  | [] => ""
  | (l, b) :: cs =>
      "\n" ++ pad ind ++ "case " ++ ppLiteral l ++ " {\n" ++
        ppStmts pOp (ind + 1) b ++ pad ind ++ "}" ++ ppCases pOp ind cs

end

/-- Print a whole program as a top-level block. -/
def ppProgram (pOp : Op → String) (b : Block Op) : String :=
  "{\n" ++ ppStmts pOp 1 b ++ "}"

/-- Print a data segment's contents (`"…"` or `hex"…"`). -/
def ppData : Data → String
  | .string s => "\"" ++ s ++ "\""
  | .hex bs   => "hex\"" ++ Data.toHex bs ++ "\""

/-- Print an object's named data segments, one per line at level `ind`. -/
def ppDataList (ind : Nat) : List (String × Data) → String
  | []          => ""
  | (n, d) :: ds => pad ind ++ "data \"" ++ n ++ "\" " ++ ppData d ++ "\n" ++ ppDataList ind ds

mutual

/-- Print an object at indentation level `ind` (`code` block, then sub-objects, then data). -/
def ppObject (pOp : Op → String) (ind : Nat) : Object Op → String
  | .mk name codeBlock subs dataSegs =>
      "object \"" ++ name ++ "\" {\n" ++
        pad (ind + 1) ++ "code {\n" ++ ppStmts pOp (ind + 2) codeBlock ++ pad (ind + 1) ++ "}\n" ++
        ppObjects pOp (ind + 1) subs ++
        ppDataList (ind + 1) dataSegs ++
      pad ind ++ "}"

/-- Print a list of sub-objects, one per line at level `ind`. -/
def ppObjects (pOp : Op → String) (ind : Nat) : List (Object Op) → String
  | []      => ""
  | o :: os => pad ind ++ ppObject pOp ind o ++ "\n" ++ ppObjects pOp ind os

end

namespace EVM

/-- Print an EVM-dialect expression. -/
def printExpr (e : Expr EVM.Op) : String := ppExpr EVM.opName e

/-- Print an EVM-dialect statement (at top level). -/
def printStmt (s : Stmt EVM.Op) : String := ppStmt EVM.opName 0 s

/-- Print an EVM-dialect program. -/
def print (b : Block EVM.Op) : String := ppProgram EVM.opName b

/-- Print an EVM-dialect object. -/
def printObject (o : Object EVM.Op) : String := ppObject EVM.opName 0 o

end EVM

/-! ### Lean integration

`Repr` stays the **faithful** constructor-level view (derived, untouched): it is the ground truth
when debugging the DSL or a pass — two different ASTs must never print identically (e.g.
`.call "add"` vs `.builtin .add`). Human-readable Yul goes through Lean's human-readable channel
instead: `ToString` instances (string interpolation, `IO.println`) and `EVM.dump` for multi-line
`#eval` output. We deliberately do not override `Repr` even though `#eval` prefers it.

Caveat: `Block` is an abbreviation for `List Stmt`, so `toString` on a block goes through the
generic `List` instance (`[stmt, …]`) — use `EVM.print`/`EVM.dump` for blocks and programs. -/

instance : ToString Literal := ⟨ppLiteral⟩
instance : ToString (Expr EVM.Op) := ⟨ppExpr EVM.opName⟩
instance : ToString (Stmt EVM.Op) := ⟨ppStmt EVM.opName 0⟩

/-- Multi-line, `#eval`-friendly program dump: `#eval EVM.dump prog`. -/
def EVM.dump (b : Block EVM.Op) : IO Unit := IO.println (EVM.print b)

/-- Multi-line, `#eval`-friendly object dump: `#eval EVM.dumpObject obj`. -/
def EVM.dumpObject (o : Object EVM.Op) : IO Unit := IO.println (EVM.printObject o)

example : s!"{yulE% add(x, 1)}" = "add(x, 1)" := rfl

/-! ### Round-trip checks against the DSL (string-exact, by `rfl`) -/

example : EVM.printExpr (yulE% add(x, 1)) = "add(x, 1)" := rfl

example : EVM.print (yul% { let x := add(2, 3) }) = "{\n    let x := add(2, 3)\n}" := rfl

example :
    EVM.print (yul% { if lt(x, 10) { sstore(0, x) } })
      = "{\n    if lt(x, 10) {\n        sstore(0, x)\n    }\n}" := rfl

-- The intended workflow — printing optimizer output, e.g.
-- `EVM.print (Passes.constantFolding.run p)` — is demonstrated once the `optimizer_correctness`
-- branch (which provides `Passes`) is merged.

/-! ### Object round-trips (DSL → printer) -/

open Yul in
/-- Parsing an object exposes its structure. -/
example : (yulObject% object "C" { code { sstore(0, 1) } }).name = "C" := rfl

open Yul in
example :
    EVM.printObject (yulObject% object "C" { code { sstore(0, 1) } data "meta" "hi" })
      = "object \"C\" {\n    code {\n        sstore(0, 1)\n    }\n    data \"meta\" \"hi\"\n}" := rfl

open Yul in
/-- A hex data segment round-trips through `Data.ofHex`/`Data.toHex`. -/
example :
    EVM.printObject (yulObject% object "C" { code { } data "b" hex"00ff" })
      = "object \"C\" {\n    code {\n    }\n    data \"b\" hex\"00ff\"\n}" := by native_decide

open Yul in
/-- A constructor object with a nested `runtime` sub-object prints with proper nesting. -/
example :
    EVM.printObject
        (yulObject% object "C" {
          code { return(0, datasize("runtime")) }
          object "runtime" { code { sstore(0, 1) } }
        })
      = "object \"C\" {\n    code {\n        return(0, datasize(\"runtime\"))\n    }\n" ++
        "    object \"runtime\" {\n        code {\n            sstore(0, 1)\n        }\n    }\n}"
      := rfl

end YulSemantics
