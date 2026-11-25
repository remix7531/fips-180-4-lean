import impl.SHA512
import spec.Setup
import equiv.SHA512.Bridge
import equiv.SHA512.Lift
import equiv.Common.Bytes

/-!
# Per-block byte → word lift bridge (SHA-512)

Parallel to `equiv/SHA256/ToU32s.lean` at 64-bit width with 8 bytes
per word, 128 bytes per block (16 words).  The byte → bit primitive
`byteToBits` is shared from `equiv/Common/Bytes.lean`.

Each `UInt64` produced by `Impl.beU64` (big-endian decode of eight
bytes) matches the spec's `Word.fromBits` over the 64 corresponding
bits (MSB-first within each byte).  This file only owns the
SHA-512-specific 8-byte / 16-word assembly. -/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA512.Bridge
open SHS.Equiv.SHA512.Lift

open SHS.SHA512

namespace SHS.Equiv.SHA512.ToU64s

open scoped SHS.SHA512

/-- Bits of `bytes[8i .. 8i+8)` as a single 64-element MSB-first list. -/
def eightBytesBits (bytes : Vector UInt8 128) (i : Fin 16) : List Bool :=
  byteToBits (bytes[8 * i.val]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 1]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 2]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 3]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 4]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 5]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 6]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 7]'(by omega))

/-- `beU64` packs the same eight bytes in the same order as `Word.fromBits`. -/
theorem beU64_eq_fromBits (bytes : Vector UInt8 128) (i : Fin 16) :
    (Impl.beU64 bytes i).toBitVec =
      SHS.Word.fromBits (n := 64) (eightBytesBits bytes i) := by
  unfold Impl.beU64 eightBytesBits
  simp (discharger := decide) only [FromBits.fromBits_append_same_width, fromBits_byteToBits,
    byteToBits_length, UInt64.toBitVec_or, toBitVec_shl_of_lt, UInt8.toBitVec_toUInt64,
    BitVec.or_assoc]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd, BitVec.or_assoc]
  rfl

/-! ## Block-level bridge

The 16-way assembly: `toSpecBlock (Impl.toU64s block)` matches the
spec's per-block parse (`(listChunks 64 bits).map Word.fromBits |>.toArray`)
over the corresponding 1024 bits. -/

/-- Bits of a 128-byte block as a single 1024-element MSB-first list. -/
def blockToBits (block : Vector UInt8 128) : List Bool :=
  block.toList.flatMap byteToBits

/-- The indexed word packs the bytes read by the implementation decoder. -/
theorem toSpecBlock_toU64s_index (block : Vector UInt8 128) (i : Fin 16) :
    (toSpecBlock (Impl.toU64s block))[i.val]! =
      SHS.Word.fromBits (n := 64) (eightBytesBits block i) := by
  show (toSpecBlock (Vector.ofFn (fun i => Impl.beU64 block i)))[i.val]! = _
  rw [getElem!_toSpecBlock]
  rw [show (Vector.ofFn (fun i => Impl.beU64 block i))[i] = Impl.beU64 block i from
    Vector.getElem_ofFn (i := i.val) i.isLt]
  exact beU64_eq_fromBits block i

/-- The explicit byte reads in a word form a contiguous slice of the block. -/
private theorem eightBytesBits_eq_slice (block : Vector UInt8 128) (index : Fin 16) :
    eightBytesBits block index =
      ((block.toList.drop (8 * index.val)).take 8).flatMap byteToBits := by
  have wordFits : 8 * index.val + 8 ≤ 128 := by omega
  simp (discharger := (simp only [List.length_drop, Vector.length_toList]; omega))
    only [eightBytesBits, List.take_succ_eq_append_getElem, List.take_zero, List.getElem_drop,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      Vector.getElem_toList, Nat.add_zero, List.append_assoc]

/-- Each decoded word packs one contiguous word-sized slice of the block bits. -/
theorem toSpecBlock_toU64s_slice (block : Vector UInt8 128) (index : Fin 16) :
    (toSpecBlock (Impl.toU64s block))[index.val]! =
      SHS.Word.fromBits (n := 64)
        (((blockToBits block).drop (index.val * 64)).take 64) := by
  rw [toSpecBlock_toU64s_index, eightBytesBits_eq_slice, blockToBits]
  rw [show index.val * 64 = 8 * (8 * index.val) by omega, show 64 = 8 * 8 from rfl,
    flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]

/-! ## Fast `ByteArray`-direct path

`Impl.sha512` reads bytes straight out of the input `ByteArray` via
`toU64sFromBytes data off` rather than materialising a per-block
`Vector UInt8 128`.  This lemma bridges the fast path to the existing
equivalence machinery (which is stated against the `Vector` form). -/

/-- The direct-from-`ByteArray` path produces the same `Block` as the
old `toU64s ∘ Vector.ofFn` shape.  Both bodies are `Vector.ofFn`s
whose underlying functions agree pointwise after `Vector.ofFn` β-reduction. -/
theorem toU64sFromBytes_eq_toU64s (data : ByteArray) (off : Nat) :
    Impl.toU64sFromBytes data off =
      Impl.toU64s (Vector.ofFn fun j : Fin 128 => data.get! (off + j.val)) := by
  apply Vector.ext
  intro i hi
  simp only [Impl.toU64sFromBytes, Impl.toU64s, Impl.beU64FromBytes, Impl.beU64,
    Vector.getElem_ofFn, ← Nat.add_assoc]

end SHS.Equiv.SHA512.ToU64s
