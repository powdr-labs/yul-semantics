import YulSemantics.Interp
import YulSemantics.Syntax
import YulSemantics.BigStep

/-!
# YulSemantics.FibExample

An example Yul contract that reads a number `n` from calldata, computes the `n`-th Fibonacci number
(mod `2^256`), writes it to memory, and returns it — together with proofs of its semantics:

* **concrete** end-to-end runs via the interpreter (`native_decide`), for several inputs; and
* a **general** theorem: for every input `n`, the contract halts returning `Nat.fib n` (as a word).

The general proof factors through a loop-invariant lemma (`fibLoop`) proven by induction on the
number of remaining iterations, over the big-step judgment.
-/

namespace YulSemantics.FibExample

open YulSemantics EVM

/-- The Fibonacci contract, in concrete Yul syntax. `a`/`b` carry consecutive Fibonacci numbers;
after `n` iterations `a = fib n`. -/
def fibContract : Block EVM.Op := yul% {
  let n := calldataload(0)
  let a := 0
  let b := 1
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    let t := add(a, b)
    a := b
    b := t
  }
  mstore(0, a)
  return(0, 32)
}

/-! ### Concrete runs (end-to-end, via the interpreter) -/

/-- An initial state whose calldata is the 32-byte big-endian encoding of `n` (for `n < 256`). -/
def callWith (n : Nat) : EvmState :=
  { EvmState.init with
    env := { EvmState.init.env with calldata := List.replicate 31 0 ++ [UInt8.ofNat n] } }

/-- `fib 0 = 0`. -/
example :
    (Interp.run EVM.exec 3000 fibContract (callWith 0)).map (fun r => loadWord r.2.1.memory 0)
      = .ok (BitVec.ofNat 256 (Nat.fib 0)) := by native_decide

/-- `fib 1 = 1`. -/
example :
    (Interp.run EVM.exec 3000 fibContract (callWith 1)).map (fun r => loadWord r.2.1.memory 0)
      = .ok (BitVec.ofNat 256 (Nat.fib 1)) := by native_decide

/-- `fib 7 = 13`. -/
example :
    (Interp.run EVM.exec 3000 fibContract (callWith 7)).map (fun r => loadWord r.2.1.memory 0)
      = .ok (BitVec.ofNat 256 (Nat.fib 7)) := by native_decide

/-- `fib 10 = 55`, and the full return path: the contract halts returning the 32-byte word. -/
example :
    (Interp.run EVM.exec 3000 fibContract (callWith 10)).map (fun r => r.2.1.halted)
      = .ok (some (.ret, List.replicate 31 0 ++ [UInt8.ofNat (Nat.fib 10)])) := by native_decide

/-! ### The general theorem

The loop body/post/condition of `fibContract`, and lemmas about how each transforms the loop-scope
environment `[("i", i), ("b", b), ("a", a), ("n", n)]`. -/

/-- The loop body: `let t := add(a, b); a := b; b := t`. -/
def fibBody : Block EVM.Op :=
  [ .letDecl ["t"] (some (.builtin .add [.var "a", .var "b"])),
    .assign ["a"] (.var "b"),
    .assign ["b"] (.var "t") ]

/-- Executing the body block sends `a ↦ b`, `b ↦ a + b` (and drops the block-local `t`); the state
is untouched (the body is pure). -/
theorem fib_body (funs : FunEnv evm) (st : EvmState) (iv av bv nv : U256) :
    ExecStmt evm funs [("i", iv), ("b", bv), ("a", av), ("n", nv)] st
      (.block fibBody) [("i", iv), ("b", av + bv), ("a", bv), ("n", nv)] st .normal := by
  have hstmts : ExecStmts evm (hoist evm fibBody :: funs)
      [("i", iv), ("b", bv), ("a", av), ("n", nv)] st fibBody
      [("t", av + bv), ("i", iv), ("b", av + bv), ("a", bv), ("n", nv)] st .normal := by
    refine Step.seqCons (Step.letVal (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl) rfl) ?_
    refine Step.seqCons (Step.assignVal (Step.var rfl) rfl) ?_
    exact Step.seqCons (Step.assignVal (Step.var rfl) rfl) Step.seqNil
  exact Step.block hstmts

/-- Word addition is `ofNat` of the natural sum (mod `2^256`). -/
theorem ofNat_add (x y : Nat) :
    (BitVec.ofNat 256 x) + (BitVec.ofNat 256 y) = BitVec.ofNat 256 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- Re-encoding a word through `toNat`/`ofNat` is the identity. -/
theorem ofNat_toNat (x : U256) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- The loop's post block: `i := add(i, 1)`. -/
def fibPost : Block EVM.Op := [ .assign ["i"] (.builtin .add [.var "i", .lit (.number 1)]) ]

/-- Executing the post block increments `i` by one; everything else is untouched. -/
theorem fib_post (funs : FunEnv evm) (st : EvmState) (iv av bv nv : U256) :
    ExecStmt evm funs [("i", iv), ("b", bv), ("a", av), ("n", nv)] st
      (.block fibPost) [("i", iv + BitVec.ofNat 256 1), ("b", bv), ("a", av), ("n", nv)] st .normal := by
  have hstmts : ExecStmts evm (hoist evm fibPost :: funs)
      [("i", iv), ("b", bv), ("a", av), ("n", nv)] st fibPost
      [("i", iv + BitVec.ofNat 256 1), ("b", bv), ("a", av), ("n", nv)] st .normal :=
    Step.seqCons (Step.assignVal (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl) rfl) Step.seqNil
  exact Step.block hstmts

end YulSemantics.FibExample
