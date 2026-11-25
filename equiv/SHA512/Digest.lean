import equiv.SHA512.Lift
import equiv.Common.Digest
import equiv.SHA512.Bridge

/-! # SHA-512 digest emission

Parallel to `equiv/SHA256/Digest.lean` at 64-bit words, 8 bytes per word,
64-byte (512-bit) full SHA-512 digest. -/

open SHS.Equiv.Bytes SHS.Equiv.Digest
open SHS.Equiv.FromBits
open SHS.Equiv.SHA512.Lift

open SHS.SHA512

namespace SHS.Equiv.SHA512.Digest

open scoped SHS.SHA512

/-- 64-byte digest viewed as a 512-bit MSB-first big-endian `BitVec`. -/
def digestBitVec512 (d : Vector UInt8 64) : BitVec 512 :=
  SHS.Word.fromBits (n := 512)
    (d.toList.flatMap fun b => byteToBits b)

/-- 8-word state → 64-byte big-endian digest. -/
def extractDigest512 (state : Impl.State) : Vector UInt8 64 :=
  Impl.digestExtract state (by decide)

/-- The low byte of an in-range shift is the corresponding word slice. -/
private theorem wordByte_toBitVec (word : UInt64) (shift : Nat) (fits : shift < 64) :
    (((word >>> UInt64.ofNat shift) &&& 0xff).toUInt8).toBitVec =
      word.toBitVec.extractLsb' shift 8 := by
  have shiftNat : (UInt64.ofNat shift).toNat = shift :=
    UInt64.toNat_ofNat_of_lt' (by change shift < 2 ^ 64; omega)
  simp only [UInt64.toUInt8_and, UInt8.toBitVec_and, show (0xff : UInt64).toUInt8.toBitVec =
    BitVec.allOnes 8 from rfl, BitVec.and_allOnes, UInt64.toBitVec_toUInt8,
    SHS.Equiv.SHA512.Bridge.toBitVec_shr_of_lt _ _ (shiftNat.symm ▸ fits), shiftNat,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

/-- An emitted digest containing whole words reconstructs the same state prefix. -/
private theorem packDigestPrefix (state : Impl.State) {wordCount : Nat} (fits : wordCount ≤ 8) :
    SHS.Word.fromBits (n := 8 * (wordCount * 8))
      ((Impl.digestExtract state (n := wordCount * 8) (by omega)).toList.flatMap byteToBits) =
      (BitVec.flattenList (List.ofFn fun i : Fin wordCount =>
        state[i.val]'(Nat.lt_of_lt_of_le i.isLt fits) |>.toBitVec)).setWidth
          (8 * (wordCount * 8)) := by
  unfold Impl.digestExtract
  rw [Vector.toList_ofFn]
  apply packWordBytes (by decide)
  intro index
  simpa only [Nat.mul_comm 8, Fin.getElem_fin, Nat.reduceSub] using
    wordByte_toBitVec (state[index.val / 8]'(by omega)) ((7 - index.val % 8) * 8) (by omega)

theorem digestBitVec512_extract (state : Impl.State) :
    digestBitVec512 (extractDigest512 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := by
  unfold digestBitVec512 extractDigest512
  refine (packDigestPrefix state (wordCount := 8) (by decide)).trans ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by simp)]
  repeat rw [List.ofFn_succ]
  rw [List.ofFn_zero]
  simp (discharger := decide) only [getElem!_pos, toSpecState, Vector.getElem_map,
    toNat_flattenList_cons, toNat_flattenList_nil, BitVec.toNat_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add,
    Nat.shiftLeft_zero, Nat.or_zero, Nat.or_assoc, Fin.val_zero, Fin.val_succ]

/-! ## SHA-384 digest emission (48 bytes = 6 words) -/

/-- Read a SHA-384 byte digest as a 384-bit big-endian word. -/
def digestBitVec384 (d : Vector UInt8 48) : BitVec 384 :=
  SHS.Word.fromBits (n := 384) (d.toList.flatMap fun b => byteToBits b)

/-- Emit the first 48 bytes of the state for SHA-384. -/
def extractDigest384 (state : Impl.State) : Vector UInt8 48 :=
  Impl.digestExtract state (by decide)

theorem digestBitVec384_extract (state : Impl.State) :
    digestBitVec384 (extractDigest384 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! := by
  unfold digestBitVec384 extractDigest384
  refine (packDigestPrefix state (wordCount := 6) (by decide)).trans ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by simp)]
  repeat rw [List.ofFn_succ]
  rw [List.ofFn_zero]
  simp (discharger := decide) only [getElem!_pos, toSpecState, Vector.getElem_map,
    toNat_flattenList_cons, toNat_flattenList_nil, BitVec.toNat_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add,
    Nat.shiftLeft_zero, Nat.or_zero, Nat.or_assoc, Fin.val_zero, Fin.val_succ]

/-! ## SHA-512/256 digest emission (32 bytes = 4 words) -/

/-- Read a SHA-512/256 byte digest as a 256-bit big-endian word. -/
def digestBitVec512_256 (d : Vector UInt8 32) : BitVec 256 :=
  SHS.Word.fromBits (n := 256) (d.toList.flatMap fun b => byteToBits b)

/-- Emit the first 32 bytes of the state for SHA-512/256. -/
def extractDigest512_256 (state : Impl.State) : Vector UInt8 32 :=
  Impl.digestExtract state (by decide)

theorem digestBitVec512_256_extract (state : Impl.State) :
    digestBitVec512_256 (extractDigest512_256 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! := by
  unfold digestBitVec512_256 extractDigest512_256
  refine (packDigestPrefix state (wordCount := 4) (by decide)).trans ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by simp)]
  repeat rw [List.ofFn_succ]
  rw [List.ofFn_zero]
  simp (discharger := decide) only [getElem!_pos, toSpecState, Vector.getElem_map,
    toNat_flattenList_cons, toNat_flattenList_nil, BitVec.toNat_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add,
    Nat.shiftLeft_zero, Nat.or_zero, Nat.or_assoc, Fin.val_zero, Fin.val_succ]

/-! ## SHA-512/224 digest emission (28 bytes — crosses a word boundary)

Unlike the other variants, SHA-512/224 truncates to 224 bits which is
3.5 of the 64-bit hash words.  Rather than reconstruct the partial word
directly, we route through the SHA-512/256 (32-byte) emission and apply
`leftmost 224` via the universal `fromBits_leftmost` identity. -/

/-- Read a SHA-512/224 byte digest as a 224-bit big-endian word. -/
def digestBitVec512_224 (d : Vector UInt8 28) : BitVec 224 :=
  SHS.Word.fromBits (n := 224) (d.toList.flatMap fun b => byteToBits b)

/-- Emit the first 28 bytes of the state for SHA-512/224. -/
def extractDigest512_224 (state : Impl.State) : Vector UInt8 28 :=
  Impl.digestExtract state (by decide)

/-- The 28-byte SHA-512/224 extraction is the first 28 bytes of the 32-byte
SHA-512/256 extraction (same pointwise formula). -/
private theorem extract224_take_of_extract256 (state : Impl.State) :
    (extractDigest512_224 state).toList =
      (extractDigest512_256 state).toList.take 28 := by
  unfold extractDigest512_224 extractDigest512_256 Impl.digestExtract
  apply List.ext_getElem
  · simp only [Vector.toList_ofFn, List.length_ofFn, List.length_take,
      Nat.min_eq_left (show 28 ≤ 32 by decide)]
  · intro index _ _
    simp only [Vector.toList_ofFn, List.getElem_take, List.getElem_ofFn]

theorem digestBitVec512_224_extract (state : Impl.State) :
    digestBitVec512_224 (extractDigest512_224 state) =
      (digestBitVec512_256 (extractDigest512_256 state)).leftmost 224 := by
  unfold digestBitVec512_224 digestBitVec512_256
  rw [extract224_take_of_extract256, ← flatMap_byteToBits_take_8]
  rw [fromBits_leftmost (M := 256) (N := 224)
    (bits := (extractDigest512_256 state).toList.flatMap byteToBits)
    (by rw [flatMap_byteToBits_length]; simp) (by decide)]

end SHS.Equiv.SHA512.Digest
