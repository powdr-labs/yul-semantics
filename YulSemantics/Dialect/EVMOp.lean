import YulSemantics.Dialect

/-!
# YulSemantics.Dialect.EVMOp

The **Mathlib-free frontend** of the EVM dialect: the built-in operation enum `Op`, its value type
`U256`, the source-name mapping (`opName`/`parse`/`mkCall`), literal interpretation (`litValue`/
`litWF`), and the effect classification (`effects`). This is everything a *syntactic* client (parser,
compiler front/backend) needs to build and manipulate `Expr Op` — with no reference to the EVM
operational semantics.

The operational semantics (`EvmState`, `stepOp`, `Step`, the `Dialect` instance, …) lives in
`YulSemantics.Dialect.EVM`, which imports this module and Mathlib. Splitting the frontend out keeps
Mathlib off the import path of code that only needs the opcode/AST layer, so a compiler executable
built from that code does not statically link Mathlib. See `DESIGN.md` §4.
-/

namespace YulSemantics.EVM

open YulSemantics

/-- The EVM word: a 256-bit machine value. -/
abbrev U256 := BitVec 256

/-- The Yul EVM-dialect built-in operations (see `YulSemantics.Dialect.EVM` for coverage and
deliberate omissions). `ret` is `return` (a Lean keyword). -/
inductive Op
  -- arithmetic
  | add | sub | mul | div | sdiv | mod | smod | addmod | mulmod | exp | signextend | clz
  -- comparison
  | lt | gt | slt | sgt | eq | iszero
  -- bitwise / shifts
  | and | or | xor | not | byte | shl | shr | sar
  -- hashing / value discard
  | keccak256 | pop
  -- memory / storage / transient storage
  | mload | mstore | mstore8 | mcopy | msize | sload | sstore | tload | tstore
  -- calldata / code / returndata
  | calldataload | calldatasize | calldatacopy | codesize | codecopy
  | returndatasize | returndatacopy
  -- object data (layout-abstracted; see `YulSemantics.Object`)
  | datasize | dataoffset | datacopy
  -- execution environment
  | address | origin | caller | callvalue | gasprice | selfbalance
  | coinbase | timestamp | number | prevrandao | gaslimit | chainid | basefee | blobbasefee
  -- world-state reads
  | balance | extcodesize | extcodecopy | extcodehash | blockhash | blobhash
  -- logging
  | log0 | log1 | log2 | log3 | log4
  -- external interaction (`call*` has an open-world relational interpretation)
  | gas | call | callcode | delegatecall | staticcall | create | create2 | selfdestruct
  -- halting
  | stop | ret | revert | invalid
  deriving Repr, DecidableEq, Inhabited

/-- How a halting built-in terminated, stored in the machine state.

`staticViolation` is the exceptional halt of a state-modifying built-in attempted in a static frame
(`env.static = true`). It is kept distinct from `invalid` (the `INVALID` opcode) because the EVM
raises a dedicated `StaticModeViolation` exception for it; conflating the two would make a Yul→EVM
compiler unable to match the exact exception on this path. -/
inductive HaltKind
  | stop | ret | revert | invalid | invalidMemoryAccess | selfdestruct | staticViolation
  deriving Repr, DecidableEq, Inhabited

/-- Boolean to word: `1` for `true`, `0` for `false`. -/
@[inline] def b2w (c : Bool) : U256 := if c then 1 else 0

/-- Interpret a literal as an EVM word. Numbers wrap mod `2^256`, string literals are big-endian
left-padded into 32 bytes; see `litWF` for well-formedness. -/
def litValue : Literal → U256
  | .number n => BitVec.ofNat 256 n
  | .bool b   => b2w b
  | .string s =>
      let bytes := s.toUTF8.toList.take 32
      let n := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
      BitVec.ofNat 256 (n <<< (8 * (32 - bytes.length)))

/-- Well-formed literals: numbers fit in 256 bits and string literals are at most 32 bytes. -/
def litWF : Literal → Prop
  | .number n => n < 2 ^ 256
  | .bool _   => True
  | .string s => s.toUTF8.size ≤ 32

/-- Effect classification of each built-in (see `YulSemantics.Effects`). The classification is an
over-approximation; its soundness against the semantics is proved as `EVM.effects_sound` in
`YulSemantics.Dialect.EVM`. -/
def effects : Op → Effects
  -- pure computation: no state at all → reads := false
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .addmod | .mulmod | .exp
  | .signextend | .clz | .lt | .gt | .slt | .sgt | .eq | .iszero
  | .and | .or | .xor | .not | .byte | .shl | .shr | .sar | .pop =>
      { deterministic := true, reads := false, writes := false, halts := false }
  -- deterministic state reads: result depends on current state → reads := true
  | .msize | .sload | .tload
  | .calldataload | .calldatasize | .codesize | .returndatasize
  | .address | .origin | .caller | .callvalue | .gasprice | .selfbalance
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .basefee | .blobbasefee
  | .balance | .extcodesize | .extcodehash | .blockhash | .blobhash
  | .datasize | .dataoffset =>
      { deterministic := true, reads := true, writes := false, halts := false }
  -- deterministic *blind* memory writes: the stored bytes come from the arguments, the prior
  -- contents are never observed → reads := false even though writes := true (see the doc comment
  -- above). Memory writes are permitted in a static frame, so they never halt.
  | .mstore | .mstore8 =>
      { deterministic := true, reads := false, writes := true, halts := false }
  -- deterministic *blind* state writes (reads := false, as above); but they halt exceptionally in a
  -- static frame (write protection), so halts := true
  | .sstore | .tstore =>
      { deterministic := true, reads := false, writes := true, halts := true }
  -- deterministic read+write: these move/hash *current* state contents, and memory reads can expand
  -- memory (observable through `msize`) → reads := true, writes := true
  | .keccak256 | .mload | .mcopy | .calldatacopy | .codecopy | .extcodecopy | .datacopy =>
      { deterministic := true, reads := true, writes := true, halts := false }
  -- logging reads memory contents and writes logs; it halts exceptionally in a static frame
  | .log0 | .log1 | .log2 | .log3 | .log4 =>
      { deterministic := true, reads := true, writes := true, halts := true }
  -- reads returndata; returndata bounds failure is an exceptional halt
  | .returndatacopy =>
      { deterministic := true, reads := true, writes := true, halts := true }
  -- calls and creates return normally to the caller but otherwise have every effect (they observe
  -- and mutate the world) → reads := true; they may halt exceptionally under static write protection
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 =>
      { deterministic := false, reads := true, writes := true, halts := true }
  -- remaining gas interaction: conservative
  | .gas => Effects.top
  -- deterministic terminal world update: reads balance to transfer → reads := true
  | .selfdestruct =>
      { deterministic := true, reads := true, writes := true, halts := true }
  -- halting with no return data: sets the halt payload (writes := true) but does not consult prior
  -- state to do so (reads := false)
  | .stop | .invalid =>
      { deterministic := true, reads := false, writes := true, halts := true }
  -- halting with return/revert data read from memory → reads := true
  | .ret | .revert =>
      { deterministic := true, reads := true, writes := true, halts := true }

/-! ### Frontend name mapping (used by the DSL in `YulSemantics.Syntax`; not by the semantics) -/

/-- The Yul source name of a built-in. -/
def opName : Op → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .sdiv => "sdiv"
  | .mod => "mod" | .smod => "smod" | .addmod => "addmod" | .mulmod => "mulmod" | .exp => "exp"
  | .signextend => "signextend" | .clz => "clz"
  | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"
  | .eq => "eq" | .iszero => "iszero" | .and => "and" | .or => "or" | .xor => "xor" | .not => "not"
  | .byte => "byte" | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .keccak256 => "keccak256" | .pop => "pop"
  | .mload => "mload" | .mstore => "mstore" | .mstore8 => "mstore8" | .mcopy => "mcopy"
  | .msize => "msize"
  | .sload => "sload" | .sstore => "sstore" | .tload => "tload" | .tstore => "tstore"
  | .calldataload => "calldataload" | .calldatasize => "calldatasize"
  | .calldatacopy => "calldatacopy" | .codesize => "codesize" | .codecopy => "codecopy"
  | .returndatasize => "returndatasize" | .returndatacopy => "returndatacopy"
  | .datasize => "datasize" | .dataoffset => "dataoffset" | .datacopy => "datacopy"
  | .address => "address" | .origin => "origin" | .caller => "caller"
  | .callvalue => "callvalue" | .gasprice => "gasprice" | .selfbalance => "selfbalance"
  | .coinbase => "coinbase" | .timestamp => "timestamp" | .number => "number"
  | .prevrandao => "prevrandao" | .gaslimit => "gaslimit" | .chainid => "chainid"
  | .basefee => "basefee" | .blobbasefee => "blobbasefee"
  | .balance => "balance" | .extcodesize => "extcodesize" | .extcodecopy => "extcodecopy"
  | .extcodehash => "extcodehash" | .blockhash => "blockhash" | .blobhash => "blobhash"
  | .log0 => "log0" | .log1 => "log1" | .log2 => "log2" | .log3 => "log3" | .log4 => "log4"
  | .gas => "gas" | .call => "call" | .callcode => "callcode"
  | .delegatecall => "delegatecall" | .staticcall => "staticcall"
  | .create => "create" | .create2 => "create2" | .selfdestruct => "selfdestruct"
  | .stop => "stop" | .ret => "return" | .revert => "revert" | .invalid => "invalid"

/-- Resolve a Yul source name to a built-in, or `none` if it is not a built-in (in which case a
call to it is a user-defined function call). -/
def parse : Ident → Option Op
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "sdiv" => some .sdiv | "mod" => some .mod | "smod" => some .smod | "addmod" => some .addmod
  | "mulmod" => some .mulmod | "exp" => some .exp | "signextend" => some .signextend
  | "clz" => some .clz
  | "lt" => some .lt | "gt" => some .gt | "slt" => some .slt | "sgt" => some .sgt
  | "eq" => some .eq | "iszero" => some .iszero | "and" => some .and | "or" => some .or
  | "xor" => some .xor | "not" => some .not | "byte" => some .byte
  | "shl" => some .shl | "shr" => some .shr | "sar" => some .sar
  | "keccak256" => some .keccak256 | "pop" => some .pop
  | "mload" => some .mload | "mstore" => some .mstore | "mstore8" => some .mstore8
  | "mcopy" => some .mcopy | "msize" => some .msize
  | "sload" => some .sload | "sstore" => some .sstore | "tload" => some .tload
  | "tstore" => some .tstore
  | "calldataload" => some .calldataload | "calldatasize" => some .calldatasize
  | "calldatacopy" => some .calldatacopy | "codesize" => some .codesize
  | "codecopy" => some .codecopy | "returndatasize" => some .returndatasize
  | "returndatacopy" => some .returndatacopy
  | "datasize" => some .datasize | "dataoffset" => some .dataoffset | "datacopy" => some .datacopy
  | "address" => some .address | "origin" => some .origin | "caller" => some .caller
  | "callvalue" => some .callvalue | "gasprice" => some .gasprice
  | "selfbalance" => some .selfbalance | "coinbase" => some .coinbase
  | "timestamp" => some .timestamp | "number" => some .number
  | "prevrandao" => some .prevrandao | "gaslimit" => some .gaslimit
  | "chainid" => some .chainid | "basefee" => some .basefee
  | "blobbasefee" => some .blobbasefee
  | "balance" => some .balance | "extcodesize" => some .extcodesize
  | "extcodecopy" => some .extcodecopy | "extcodehash" => some .extcodehash
  | "blockhash" => some .blockhash | "blobhash" => some .blobhash
  | "log0" => some .log0 | "log1" => some .log1 | "log2" => some .log2
  | "log3" => some .log3 | "log4" => some .log4
  | "gas" => some .gas | "call" => some .call | "callcode" => some .callcode
  | "delegatecall" => some .delegatecall | "staticcall" => some .staticcall
  | "create" => some .create | "create2" => some .create2
  | "selfdestruct" => some .selfdestruct
  | "stop" => some .stop | "return" => some .ret | "revert" => some .revert
  | "invalid" => some .invalid
  | _ => none

/-- Smart constructor for a call in source: resolve the name to a built-in if it is one, otherwise
treat it as a user-defined function call. Used by the DSL (`YulSemantics.Syntax`). For a literal
built-in name this reduces to `Expr.builtin op args` definitionally. -/
def mkCall (name : Ident) (args : List (Expr Op)) : Expr Op :=
  match parse name with
  | some op => .builtin op args
  | none    => .call name args

end YulSemantics.EVM
