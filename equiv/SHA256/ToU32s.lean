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

/-- `beU32` packs the same four bytes in the same order as `Word.fromBits`. -/
theorem beU32_eq_fromBits (bytes : Vector UInt8 64) (i : Fin 16) :
    (Impl.beU32 bytes i).toBitVec =
      SHS.Word.fromBits (n := 32) (fourBytesBits bytes i) := by
  unfold Impl.beU32 fourBytesBits
  simp (discharger := decide) only [FromBits.fromBits_append_same_width, fromBits_byteToBits,
    byteToBits_length, UInt32.toBitVec_or, toBitVec_shl_of_lt, UInt8.toBitVec_toUInt32,
    BitVec.or_assoc]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd, BitVec.or_assoc]
  rfl

/-! ## Block-level bridge

The 16-way assembly: `toSpecBlock (Impl.toU32s block)` matches the spec's
per-block parse (`(listChunks 32 bits).map Word.fromBits |>.toArray`) over
the corresponding 512 bits. -/

/-- Bits of a 64-byte block as a single 512-element MSB-first list. -/
def blockToBits (block : Vector UInt8 64) : List Bool :=
  block.toList.flatMap byteToBits

/-- The indexed word packs the bytes read by the implementation decoder. -/
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

/-- The explicit byte reads in a word form a contiguous slice of the block. -/
private theorem fourBytesBits_eq_slice (block : Vector UInt8 64) (index : Fin 16) :
    fourBytesBits block index =
      ((block.toList.drop (4 * index.val)).take 4).flatMap byteToBits := by
  have wordFits : 4 * index.val + 4 ≤ 64 := by omega
  simp (discharger := (simp only [List.length_drop, Vector.length_toList]; omega))
    only [fourBytesBits, List.take_succ_eq_append_getElem, List.take_zero, List.getElem_drop,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      Vector.getElem_toList, Nat.add_zero, List.append_assoc]

/-- Each decoded word packs one contiguous word-sized slice of the block bits. -/
theorem toSpecBlock_toU32s_slice (block : Vector UInt8 64) (index : Fin 16) :
    (toSpecBlock (Impl.toU32s block))[index.val]! =
      SHS.Word.fromBits (n := 32)
        (((blockToBits block).drop (index.val * 32)).take 32) := by
  rw [toSpecBlock_toU32s_index, fourBytesBits_eq_slice, blockToBits]
  rw [show index.val * 32 = 8 * (4 * index.val) by omega, show 32 = 8 * 4 from rfl,
    flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]

/-! ## Fast `ByteArray`-direct path

`Impl.sha256` no longer materializes the per-block `Vector UInt8 64`
intermediate; instead it calls `toU32sFromBytes data off` which reads
bytes straight out of the input `ByteArray`.  This lemma bridges the
fast path to the existing equivalence machinery (which is stated
against the `Vector`-shaped form). -/

/-- The direct-from-`ByteArray` path produces the same `Block` as the
old `toU32s ∘ Vector.ofFn` shape.  Both bodies are `Vector.ofFn`s
whose underlying functions agree pointwise after one `Vector.ofFn` β-reduction. -/
theorem toU32sFromBytes_eq_toU32s (data : ByteArray) (off : Nat) :
    Impl.toU32sFromBytes data off =
      Impl.toU32s (Vector.ofFn fun j : Fin 64 => data.get! (off + j.val)) := by
  -- Both sides reduce per index `i ∈ {0..15}` to the same four-byte read
  -- expression at `data.get! (off + 4*i + k)` for k ∈ {0..3}.  The LHS is
  -- now an explicit `#v[..16..]` construction; the RHS goes through two
  -- `Vector.ofFn` β-reductions plus an associativity normalization.
  have wordsAgree : ∀ i : Fin 16,
      (Impl.toU32sFromBytes data off)[i] =
        (Impl.toU32s (Vector.ofFn fun j : Fin 64 => data.get! (off + j.val)))[i] := by
    simp only [Impl.toU32sFromBytes, Impl.toU32s, Impl.beU32FromBytes, Impl.beU32,
      Fin.getElem_fin, Vector.getElem_ofFn, ← Nat.add_assoc]
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
    repeat' first | apply And.intro | rfl | trivial
  exact Vector.ext fun i hi => wordsAgree ⟨i, hi⟩

end SHS.Equiv.SHA256.ToU32s
