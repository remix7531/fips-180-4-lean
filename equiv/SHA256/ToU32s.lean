import impl.SHA256
import spec.Setup
import equiv.SHA256.Bridge
import equiv.SHA256.Lift
import equiv.Common.Bytes

/-!
# Per-block byte → word lift bridge

Each `UInt32` produced by `Impl.beU32` (big-endian decode of four bytes)
matches the spec's `Word.fromBits` over the 32 corresponding bits
(MSB-first within each byte).

This is the per-word building block for the full block-level bridge
between `Impl.toU32s` and `Spec.SHA256.parse` on one 512-bit block.

The byte → bit primitive `byteToBits` itself lives in
`equiv/Common/Bytes.lean` (word-size agnostic, shared with SHA-512); this
file only owns the SHA-256-specific 4-byte / 16-word assembly.
-/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA256.Bridge
open SHS.Equiv.SHA256.Lift

open SHS.SHA256

namespace SHS.Equiv.SHA256.ToU32s

open scoped SHS.SHA256

/-- Bits of `bytes[4i .. 4i+4)` as a single 32-element MSB-first list. -/
def fourBytesBits (bytes : Vector UInt8 64) (i : Fin 16) : List Bool :=
  byteToBits (bytes[4 * i.val]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 1]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 2]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 3]'(by omega))

/-- `Word.fromBits` of one byte's MSB-first bit list equals the byte's
underlying `BitVec 8`.

The proof unfolds `byteToBits` and the eight-step `Word.fromBits` foldl
into an explicit `acc <<< 1 ||| _` chain, converts each
`b.toNat.testBit i` to `b.toBitVec.getLsbD i` (so the expression is
purely `BitVec 8`-shaped), then closes with `bv_decide`. -/
theorem fromBits_byteToBits (b : UInt8) :
    (SHS.Word.fromBits (n := 8) (byteToBits b)) = b.toBitVec := by
  show (SHS.Word.fromBits (n := 8)
    [b.toNat.testBit 7, b.toNat.testBit 6, b.toNat.testBit 5, b.toNat.testBit 4,
     b.toNat.testBit 3, b.toNat.testBit 2, b.toNat.testBit 1, b.toNat.testBit 0])
    = b.toBitVec
  unfold SHS.Word.fromBits
  simp only [List.foldl]
  -- Bridge `b.toNat.testBit i` to `b.toBitVec.getLsbD i` so the goal
  -- becomes pure `BitVec 8` arithmetic that `bv_decide` can crunch.
  have h : ∀ i, b.toNat.testBit i = b.toBitVec.getLsbD i := fun i => by
    rw [show b.toNat = b.toBitVec.toNat from rfl, BitVec.testBit_toNat]
  simp only [h]
  bv_decide

/-- Per-word bridge: the impl's `beU32` decode equals the spec's
`Word.fromBits` over the 32 MSB-first bits of the same four bytes.

Same pattern as `fromBits_byteToBits`: explicitly enumerate the 32-bit
list, unfold the `foldl` step-by-step, lift `Nat.testBit` to
`BitVec.getLsbD`, then `bv_decide` over the resulting BitVec arithmetic. -/
theorem beU32_eq_fromBits (bytes : Vector UInt8 64) (i : Fin 16) :
    (Impl.beU32 bytes i).toBitVec =
      SHS.Word.fromBits (n := 32) (fourBytesBits bytes i) := by
  unfold Impl.beU32 fourBytesBits byteToBits
  -- Now both sides reference the same `bytes[4*i.val + k]` accesses;
  -- generalise them so `bv_decide` doesn't have to see through indexing.
  generalize bytes[4 * i.val]'(by omega) = b0
  generalize bytes[4 * i.val + 1]'(by omega) = b1
  generalize bytes[4 * i.val + 2]'(by omega) = b2
  generalize bytes[4 * i.val + 3]'(by omega) = b3
  show (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32).toBitVec =
    SHS.Word.fromBits (n := 32)
      ([b0.toNat.testBit 7, b0.toNat.testBit 6, b0.toNat.testBit 5, b0.toNat.testBit 4,
        b0.toNat.testBit 3, b0.toNat.testBit 2, b0.toNat.testBit 1, b0.toNat.testBit 0,
        b1.toNat.testBit 7, b1.toNat.testBit 6, b1.toNat.testBit 5, b1.toNat.testBit 4,
        b1.toNat.testBit 3, b1.toNat.testBit 2, b1.toNat.testBit 1, b1.toNat.testBit 0,
        b2.toNat.testBit 7, b2.toNat.testBit 6, b2.toNat.testBit 5, b2.toNat.testBit 4,
        b2.toNat.testBit 3, b2.toNat.testBit 2, b2.toNat.testBit 1, b2.toNat.testBit 0,
        b3.toNat.testBit 7, b3.toNat.testBit 6, b3.toNat.testBit 5, b3.toNat.testBit 4,
        b3.toNat.testBit 3, b3.toNat.testBit 2, b3.toNat.testBit 1, b3.toNat.testBit 0])
  unfold SHS.Word.fromBits
  simp only [List.foldl]
  have h : ∀ (b : UInt8) i, b.toNat.testBit i = b.toBitVec.getLsbD i := fun b i => by
    rw [show b.toNat = b.toBitVec.toNat from rfl, BitVec.testBit_toNat]
  simp only [h]
  bv_decide

/-! ## Block-level bridge

The 16-way assembly: `toSpecBlock (Impl.toU32s block)` matches the spec's
per-block parse (`(bits.toChunks 32).map Word.fromBits |>.toArray`) over
the corresponding 512 bits. -/

/-- Bits of a 64-byte block as a single 512-element MSB-first list. -/
def blockToBits (block : Vector UInt8 64) : List Bool :=
  block.toList.flatMap byteToBits

/-- Per-word bridge: the `i`-th word of `toSpecBlock (Impl.toU32s block)`
equals `Word.fromBits` of the `i`-th 32-bit slice of `blockToBits block`.

This is the bridging fact between the impl's `Vector.ofFn`-based
indexing and the spec's `List.toChunks 32` slicing.  Proof outline:
unfold both sides; show the 32-bit slice equals `fourBytesBits block i`
by list bookkeeping over `flatMap` chunks of 8; close with
`beU32_eq_fromBits`. -/
theorem toSpecBlock_toU32s_index (block : Vector UInt8 64) (i : Fin 16) :
    (toSpecBlock (Impl.toU32s block))[i.val]! =
      SHS.Word.fromBits (n := 32) (fourBytesBits block i) := by
  -- Unfold `Impl.toU32s` so the impl side becomes `Vector.ofFn (Impl.beU32 block ·)`.
  show (toSpecBlock (Vector.ofFn (fun i => Impl.beU32 block i)))[i.val]! = _
  -- Project the `i.val`-th word via `getElem!_toSpecBlock`.
  rw [getElem!_toSpecBlock]
  -- Reduce `(Vector.ofFn _)[i]` to `Impl.beU32 block i`.
  rw [show (Vector.ofFn (fun i => Impl.beU32 block i))[i] = Impl.beU32 block i from
    Vector.getElem_ofFn (i := i.val) i.isLt]
  -- Closing: per-word bridge.
  exact beU32_eq_fromBits block i

end SHS.Equiv.SHA256.ToU32s
