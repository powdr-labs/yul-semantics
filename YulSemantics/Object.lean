import YulSemantics.Ast

/-!
# YulSemantics.Object

The **object layer** of Yul: name resolution and data sizes over the `Object` AST (defined in
`YulSemantics.Ast`). Dialect-generic (pure syntax over `Object Op`).

A Yul *object* packages a deployable unit: a named `code` block plus nested sub-objects and named
`data` segments. Its distinctive semantic content is that the `code` may reference sibling data and
sub-objects **by name** through the built-ins `dataoffset` / `datasize` / `datacopy` — where those
names resolve to byte *offsets* and *sizes* in the eventual deployed bytecode.

## What is (and isn't) determined at the Yul level

The layout — the concrete byte offsets, and the sizes of *sub-objects* — is fixed only by the
compiler (a sub-object's size is the length of *its compiled bytecode*, which does not exist until
compilation). So at the pure-semantics level these are **abstract**: the EVM dialect reads them
from an execution-environment layout (`dataOffset` / `dataSize` maps in
`YulSemantics.Dialect.EVM.ExecEnv`), and the compiler will later supply a layout consistent with
the object. Only a *data segment's* size is concretely known here (`Data.size`); it can be used to
state a well-formedness/consistency condition on a layout.

This module provides the purely structural half: turning `data` items into bytes and resolving the
dotted name paths that `dataoffset`/`datasize` use.

## Path resolution (as modeled)

`dataoffset("a.b")` names the object/data reachable from the current object by the dotted path
`a.b`. We resolve a path relative to an object by descending through sub-objects, with a leaf being
either a data segment or a sub-object; the leading component may be the current object's own name
(`Object.lookup`). This captures the common cases (a constructor referencing its `runtime`
sub-object and data segments); Yul's full visibility rules (e.g. referencing across the object
tree) are not all modeled — documented here rather than silently assumed.
-/

namespace YulSemantics

namespace Data

/-- The raw bytes of a data segment. -/
def bytes : Data → List UInt8
  | .hex bs   => bs
  | .string s => s.toUTF8.toList

/-- The size, in bytes, of a data segment. -/
def size (d : Data) : Nat := d.bytes.length

/-- Value of a hex digit character, or `none`. -/
def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)            -- '0'..'9'
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10) -- 'a'..'f'
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 65 + 10)  -- 'A'..'F'
  else none

/-- Combine a list of nibbles into bytes (a trailing odd nibble is dropped). -/
def pairNibbles : List Nat → List UInt8
  | hi :: lo :: rest => UInt8.ofNat (hi * 16 + lo) :: pairNibbles rest
  | _ => []

/-- Parse a hex-literal body (e.g. `"00ff"`; non-hex characters are ignored) into bytes. -/
def ofHex (s : String) : List UInt8 := pairNibbles (s.toList.filterMap hexVal)

/-- Render a nibble (`0`–`15`) as a lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (97 + (n - 10))

/-- Render bytes as a lowercase hex string (inverse of `ofHex` on well-formed input). -/
def toHex (bs : List UInt8) : String :=
  String.join (bs.map (fun b => String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]))

end Data

namespace Object

variable {Op : Type}

/-- The direct sub-object with the given name, if any. -/
def subObject (o : Object Op) (name : String) : Option (Object Op) :=
  o.subObjects.find? (fun s => s.name = name)

/-- The direct data segment with the given name, if any. -/
def dataItem (o : Object Op) (name : String) : Option Data :=
  (o.dataSegs.find? (fun p => p.1 = name)).map (·.2)

/-- Resolve a path relative to `o` to a sub-object (`.inl`) or a data segment (`.inr`).

* the empty path is the object itself;
* a single-element path is a data segment or a direct sub-object;
* a longer path descends through the named sub-object. -/
def resolve : Object Op → List String → Option (Object Op ⊕ Data)
  | o, []          => some (.inl o)
  | o, [name]      =>
      match o.dataItem name with
      | some d => some (.inr d)
      | none   => (o.subObject name).map Sum.inl
  | o, name :: rest => (o.subObject name).bind (fun s => resolve s rest)

/-- Resolve a path, allowing its leading component to be the current object's own name. -/
def lookup (o : Object Op) : List String → Option (Object Op ⊕ Data)
  | first :: rest => if first = o.name then o.resolve rest else o.resolve (first :: rest)
  | []            => some (.inl o)

/-- Resolve a dotted reference (`"a.b.c"`) as used by `dataoffset`/`datasize`. -/
def lookupRef (o : Object Op) (ref : String) : Option (Object Op ⊕ Data) :=
  o.lookup (ref.splitOn ".")

/-- The size of a *data segment* referenced by name, when the reference resolves to one. Sub-object
sizes are layout-dependent and are `none` here (they are supplied by the compiler's layout). -/
def dataRefSize (o : Object Op) (ref : String) : Option Nat :=
  match o.lookupRef ref with
  | some (.inr d) => some d.size
  | _             => none

/-- All names directly referenceable from `o` (its sub-objects and data segments). -/
def localNames (o : Object Op) : List String :=
  o.subObjects.map (·.name) ++ o.dataSegs.map (·.1)

end Object

end YulSemantics
