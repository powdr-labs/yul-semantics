import Mathlib

/-!
# Ethereum Keccak-256

A minimal executable implementation of the original Keccak-256 function used by Ethereum. This is
the pre-standardization Keccak variant with padding delimiter `0x01`, not NIST SHA3-256 (which uses
`0x06`). The implementation is deliberately separate from the EVM dialect's opaque hash constant:
the relational semantics remains independent of any hash implementation, while native execution
uses this module through `implemented_by`.

The permutation state consists of 25 64-bit lanes. `hash` implements the Keccak-f[1600] sponge with
a 136-byte rate and produces a 32-byte digest; `digestNat` packs that digest big-endian for the
EVM's 256-bit word representation.
-/

namespace YulSemantics.Keccak

/-- Keccak-f[1600]'s 24 round constants. -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rho rotation offsets, indexed by the lane `x + 5 * y`. -/
def rotationOffsets : Array Nat := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-- Rotate a 64-bit lane left by `n` bits. -/
def rotateLeft (x : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then x else (x <<< UInt64.ofNat n) ||| (x >>> UInt64.ofNat (64 - n))

/-- One Keccak-f round: theta, rho, pi, chi, and iota. -/
def round (state : Array UInt64) (constant : UInt64) : Array UInt64 := Id.run do
  let mut columns : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    columns := columns.set! x
      (state[x]! ^^^ state[x + 5]! ^^^ state[x + 10]! ^^^ state[x + 15]! ^^^ state[x + 20]!)
  let mut deltas : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    deltas := deltas.set! x
      (columns[(x + 4) % 5]! ^^^ rotateLeft columns[(x + 1) % 5]! 1)
  let mut theta := state
  for x in [0:5] do
    for y in [0:5] do
      theta := theta.set! (x + 5 * y) (theta[x + 5 * y]! ^^^ deltas[x]!)

  let mut rhoPi : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      let source := x + 5 * y
      let destination := y + 5 * ((2 * x + 3 * y) % 5)
      rhoPi := rhoPi.set! destination (rotateLeft theta[source]! rotationOffsets[source]!)

  let mut chi : Array UInt64 := Array.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      chi := chi.set! (x + 5 * y)
        (rhoPi[x + 5 * y]! ^^^
          ((rhoPi[((x + 1) % 5) + 5 * y]! ^^^ 0xffffffffffffffff) &&&
            rhoPi[((x + 2) % 5) + 5 * y]!))
  return chi.set! 0 (chi[0]! ^^^ constant)

/-- The 24-round Keccak-f[1600] permutation. -/
def permute (state : Array UInt64) : Array UInt64 := Id.run do
  let mut state := state
  for i in [0:24] do
    state := round state roundConstants[i]!
  return state

/-- Read eight bytes starting at `offset` as a little-endian 64-bit lane. -/
def readLE64 (bytes : ByteArray) (offset : Nat) : UInt64 := Id.run do
  let mut word : UInt64 := 0
  for i in [0:8] do
    let byte : UInt64 := if h : offset + i < bytes.size then bytes[offset + i].toUInt64 else 0
    word := word ||| (byte <<< UInt64.ofNat (8 * i))
  return word

/-- Append a 64-bit lane to `output` in little-endian byte order. -/
def appendLE64 (output : ByteArray) (word : UInt64) : ByteArray := Id.run do
  let mut output := output
  for i in [0:8] do
    output := output.push (((word >>> UInt64.ofNat (8 * i)) &&& 0xff).toUInt8)
  return output

/-- Hash a byte array with Ethereum's original Keccak-256. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let rate := 136
  let mut state : Array UInt64 := Array.replicate 25 0

  let fullBlocks := bytes.size / rate
  for blockIndex in [0:fullBlocks] do
    let base := blockIndex * rate
    for laneIndex in [0:rate / 8] do
      let lane := readLE64 bytes (base + laneIndex * 8)
      state := state.set! laneIndex (state[laneIndex]! ^^^ lane)
    state := permute state

  let remainderBase := fullBlocks * rate
  let remainderSize := bytes.size - remainderBase
  let mut finalBlock := ByteArray.mk (Array.replicate rate 0)
  for i in [0:remainderSize] do
    finalBlock := finalBlock.set! i bytes[remainderBase + i]!
  finalBlock := finalBlock.set! remainderSize (finalBlock[remainderSize]! ^^^ 0x01)
  finalBlock := finalBlock.set! (rate - 1) (finalBlock[rate - 1]! ^^^ 0x80)

  for laneIndex in [0:rate / 8] do
    let lane := readLE64 finalBlock (laneIndex * 8)
    state := state.set! laneIndex (state[laneIndex]! ^^^ lane)
  state := permute state

  let mut output := ByteArray.empty
  for laneIndex in [0:4] do
    output := appendLE64 output state[laneIndex]!
  return output

/-- Interpret bytes as a big-endian natural number. -/
def bytesToNat (bytes : ByteArray) : Nat :=
  bytes.toList.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Ethereum Keccak-256 of a byte list, packed as a big-endian natural number. -/
def digestNat (bytes : List UInt8) : Nat := hash (ByteArray.mk bytes.toArray) |> bytesToNat

end YulSemantics.Keccak
