import YulSemantics.Interp
import YulSemantics.Dialect.EVM
import YulSemantics.Object
import YulSemantics.Syntax

/-!
# YulSemantics.ObjectRun

Running a Yul **object** under a bytecode **layout**, and the consistency condition linking the two.

An object's `code` references its data segments and sub-objects by name through
`dataoffset`/`datasize`/`datacopy`, whose meaning depends on the eventual bytecode layout — an
artifact of the compiler (a sub-object's size is the length of *its* compiled bytecode). This module
introduces that layout as explicit data, the initial machine state it induces, entry points for
running an object (`runObject` executable, `RunObject` relational), and the key notion:

* `Layout.Consistent` — the layout faithfully places every *data segment*: its recorded size is the
  segment's byte length, and its bytes sit at the recorded offset in `code`. (Sub-object offsets and
  sizes are genuine compiler artifacts and are left unconstrained.)

The payoff is `datacopy_copies_data`: under a consistent layout,
`datacopy(t, dataoffset(name), datasize(name))` copies exactly the named segment's bytes — the
correctness content the compiler's layout must guarantee, discharged once here.
-/

namespace YulSemantics.EVM

open YulSemantics

/-- A bytecode layout for an object: the deployed `code`, and the `dataoffset`/`datasize` maps
(keyed by a name's string-literal encoding `litValue (.string name)`, as the built-ins expect).
This is the artifact a compiler produces; the pure semantics is relative to it. -/
structure Layout where
  /-- The deployed bytecode. -/
  code       : List UInt8
  /-- Byte offset of each named segment within `code`, keyed by `litValue (.string name)`. -/
  dataOffset : U256 → U256
  /-- Byte length of each named segment, keyed like `dataOffset`. -/
  dataSize   : U256 → U256

/-- The execution environment induced by a layout (all other fields default). -/
def Layout.env (L : Layout) : ExecEnv :=
  { code := L.code, dataOffset := L.dataOffset, dataSize := L.dataSize }

/-- The initial machine state for running an object under a layout. -/
def Layout.initState (L : Layout) : EvmState := { EvmState.init with env := L.env }

/-- A layout is **consistent** with an object when every data segment is faithfully placed: its
recorded size matches its byte length, and its bytes sit at the recorded offset in `code`.
Sub-object offsets/sizes are compiler artifacts and are left unconstrained. -/
def Layout.Consistent (L : Layout) (o : Object EVM.Op) : Prop :=
  ∀ p ∈ o.dataSegs,
    L.dataSize (litValue (.string p.1)) = BitVec.ofNat 256 p.2.size ∧
    readBytes (byteFrom L.code) (L.dataOffset (litValue (.string p.1))).toNat p.2.size = p.2.bytes

/-- Run an object's `code` under a layout, via the interpreter. -/
def runObject (fuel : Nat) (o : Object EVM.Op) (L : Layout) : Result (Interp.SResult exec) :=
  Interp.run exec fuel o.codeBlock L.initState

/-- Big-step execution of an object's `code` under a layout. -/
def RunObject (o : Object EVM.Op) (L : Layout)
    (V : VEnv evm) (st : EvmState) (out : Outcome) : Prop :=
  Run evm o.codeBlock L.initState V st out

/-! ### Correctness of `datacopy` under a consistent layout -/

/-- Reading back the region a `copyInto` just wrote reproduces the source bytes. -/
theorem readBytes_copyInto (mem : Nat → UInt8) (bytes : List UInt8) (t off sz : Nat) :
    readBytes (copyInto mem t off sz bytes) t sz = readBytes (byteFrom bytes) off sz := by
  simp only [readBytes]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [copyInto]
  rw [if_pos (by omega)]
  congr 1
  omega

/-- **Payoff**: under a layout consistent with `o`, copying a named data segment
(`datacopy(t, dataoffset(name), datasize(name))` reads the segment's offset/size from the layout and
copies from `code`) writes exactly the segment's bytes to `memory[t …]`. -/
theorem datacopy_copies_data (L : Layout) (o : Object EVM.Op) (hc : L.Consistent o)
    {n : Ident} {d : Data} (hmem : (n, d) ∈ o.dataSegs) (mem : Nat → UInt8) (t : Nat) :
    readBytes (copyInto mem t (L.dataOffset (litValue (.string n))).toNat d.size L.code) t d.size
      = d.bytes := by
  obtain ⟨_, hbytes⟩ := hc (n, d) hmem
  rw [readBytes_copyInto]
  exact hbytes

/-! ### The canonical constructor, returning a data segment (general theorem)

The standard deploy-code pattern for a data segment `name`:
`datacopy(0, dataoffset(name), datasize(name)); return(0, datasize(name))`. Under a layout that
places `name` (i.e. a consistent layout, for a segment of the object), running it halts returning
exactly the segment's bytes. -/

/-- The canonical constructor code that copies and returns the data segment `n`. -/
def constructorCode (n : Ident) : Block EVM.Op :=
  [ .exprStmt (.builtin .datacopy
      [.lit (.number 0), .builtin .dataoffset [.lit (.string n)], .builtin .datasize [.lit (.string n)]]),
    .exprStmt (.builtin .ret [.lit (.number 0), .builtin .datasize [.lit (.string n)]]) ]

/-- `datasize(name)` evaluates (at any configuration) to the environment's recorded size. -/
theorem eval_datasize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : Ident) :
    EvalExpr evm funs V st (.builtin .datasize [.lit (.string n)])
      (.vals [st.env.dataSize (litValue (.string n))] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl

/-- `dataoffset(name)` evaluates to the environment's recorded offset. -/
theorem eval_dataoffset (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : Ident) :
    EvalExpr evm funs V st (.builtin .dataoffset [.lit (.string n)])
      (.vals [st.env.dataOffset (litValue (.string n))] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl

/-- **Capstone**: under a layout that places the data segment `n` (of byte length `d.size`, which
must fit a word), the canonical constructor halts, returning exactly `d.bytes`. -/
theorem constructorCode_returns (L : Layout) (n : Ident) (d : Data)
    (hsize : L.dataSize (litValue (.string n)) = BitVec.ofNat 256 d.size)
    (hbytes : readBytes (byteFrom L.code)
      (L.dataOffset (litValue (.string n))).toNat d.size = d.bytes)
    (hlt : d.size < 2 ^ 256) :
    ∃ V st, Run evm (constructorCode n) L.initState V st .halt ∧
      st.halted = some (.ret, d.bytes) := by
  refine ⟨[], _, Step.block (Step.seqCons
      (Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil (eval_datasize _ _ _ _))
          (eval_dataoffset _ _ _ _)) Step.lit) rfl))
      (Step.seqStop
        (Step.exprStmtHalt (Step.builtinHalt
          (Step.argsCons (Step.argsCons Step.argsNil (eval_datasize _ _ _ _)) Step.lit) rfl))
        (by decide))), ?_⟩
  -- remaining goal: the halted field of the (inferred) final state is `some (.ret, d.bytes)`
  have hsz : (L.dataSize (litValue (.string n))).toNat = d.size := by
    rw [hsize, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  simp only [Layout.initState, Layout.env, touchMemory]
  rw [readBytes_copyInto, hsz, hbytes]

/-- The capstone, from consistency and membership: for any data segment of `o`, the canonical
constructor returns its bytes under a consistent layout. -/
theorem constructorCode_returns_of_consistent (L : Layout) (o : Object EVM.Op)
    (hc : L.Consistent o) {n : Ident} {d : Data} (hmem : (n, d) ∈ o.dataSegs)
    (hlt : d.size < 2 ^ 256) :
    ∃ V st, Run evm (constructorCode n) L.initState V st .halt ∧
      st.halted = some (.ret, d.bytes) :=
  have h := hc (n, d) hmem
  constructorCode_returns L n d h.1 h.2 hlt

/-! ### End-to-end demonstration

A constructor object that returns its `blob` data segment, run under a consistent layout. -/

/-- `object "C" { code { datacopy(…); return(0, datasize("blob")) } data "blob" hex"deadbeef" }`. -/
def cObject : Object EVM.Op :=
  yulObject% object "C" {
    code {
      datacopy(0, dataoffset("blob"), datasize("blob"))
      return(0, datasize("blob"))
    }
    data "blob" hex"deadbeef"
  }

/-- A layout placing `blob` at offset 5 (size 4) in the deployed bytecode. -/
def cLayout : Layout :=
  let key := litValue (.string "blob")
  { code       := [0, 0, 0, 0, 0, 0xde, 0xad, 0xbe, 0xef]
    dataOffset := fun k => if k = key then 5 else 0
    dataSize   := fun k => if k = key then 4 else 0 }

/-- The layout is consistent with the object (`blob`'s size and bytes match). -/
example : cLayout.Consistent cObject := by unfold Layout.Consistent; native_decide

/-- Running the constructor halts (via `return`) … -/
example :
    (runObject 100 cObject cLayout).map (·.2.2) = .ok .halt := by native_decide

example :
    (runObject 100 cObject cLayout).map (fun r => r.2.1.halted)
      = .ok (some (.ret, [0xde, 0xad, 0xbe, 0xef])) := by native_decide

end YulSemantics.EVM
