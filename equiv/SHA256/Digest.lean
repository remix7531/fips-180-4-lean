import equiv.SHA256.Lift
import equiv.Common.Digest
import equiv.SHA256.Bridge

/-! # SHA-256 digest emission

Turn an 8-word `Impl.State` into a 32-byte big-endian digest, and prove
that this byte stream — read back into a `BitVec 256` via
`Word.fromBits` — equals the spec's `H[0]! ++ … ++ H[7]!`. -/

open SHS.Equiv.Bytes SHS.Equiv.Digest
open SHS.Equiv.SHA256.Lift

open SHS.SHA256

namespace SHS.Equiv.SHA256.Digest

open scoped SHS.SHA256

/-- 32-byte digest viewed as a 256-bit MSB-first big-endian `BitVec`,
matching how the spec's `H[0]! ++ … ++ H[7]!` is laid out. -/
def digestBitVec (d : Vector UInt8 32) : BitVec 256 :=
  SHS.Word.fromBits (n := 256)
    (d.toList.flatMap fun b => byteToBits b)

/-- The full SHA-256 state encoded as four big-endian bytes per word. -/
def extractDigest (state : Impl.State) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- The low byte of an in-range shift is the corresponding word slice. -/
private theorem wordByte_toBitVec (word : UInt32) (shift : Nat) (fits : shift < 32) :
    (((word >>> UInt32.ofNat shift) &&& 0xff).toUInt8).toBitVec =
      word.toBitVec.extractLsb' shift 8 := by
  have shiftNat : (UInt32.ofNat shift).toNat = shift :=
    UInt32.toNat_ofNat_of_lt' (by change shift < 2 ^ 32; omega)
  simp only [UInt32.toUInt8_and, UInt8.toBitVec_and, show (0xff : UInt32).toUInt8.toBitVec =
    BitVec.allOnes 8 from rfl, BitVec.and_allOnes, UInt32.toBitVec_toUInt8,
    SHS.Equiv.SHA256.Bridge.toBitVec_shr_of_lt _ _ (shiftNat.symm ▸ fits), shiftNat,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

/-- Final byte-extraction emission matches the spec's `H[0]! ++ … ++ H[7]!`. -/
theorem digestBitVec_extract (state : Impl.State) :
    digestBitVec (extractDigest state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := by
  unfold digestBitVec extractDigest
  rw [Vector.toList_ofFn]
  refine (packWordBytes (wordCount := 8) (bytesPerWord := 4) (by decide)
    (fun i => state[i.val].toBitVec) _ ?_).trans ?_
  · intro index
    simpa only [Nat.mul_comm 8, Fin.getElem_fin, Nat.reduceSub] using
      wordByte_toBitVec (state[index.val / 4]'(by omega)) ((3 - index.val % 4) * 8) (by omega)
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by simp)]
    repeat rw [List.ofFn_succ]
    rw [List.ofFn_zero]
    simp (discharger := decide) only [getElem!_pos, toSpecState, Vector.getElem_map,
      toNat_flattenList_cons, toNat_flattenList_nil, BitVec.toNat_append, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add,
      Nat.shiftLeft_zero, Nat.or_zero, Nat.or_assoc, Fin.val_zero, Fin.val_succ]

/-! ## SHA-224 digest emission -/

/-- 28-byte BE digest viewed as a 224-bit MSB-first big-endian `BitVec`. -/
def digestBitVec224 (d : Vector UInt8 28) : BitVec 224 :=
  SHS.Word.fromBits (n := 224)
    (d.toList.flatMap fun b => byteToBits b)

/-- SHA-224 digest extractor: same big-endian per-word byte layout as
`extractDigest`, restricted to the first seven words. -/
def extractDigest224 (state : Impl.State) : Vector UInt8 28 :=
  Vector.ofFn fun i : Fin 28 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- SHA-224 digest emission agrees with the first seven state words. -/
theorem digestBitVec224_extract (state : Impl.State) :
    digestBitVec224 (extractDigest224 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! := by
  unfold digestBitVec224 extractDigest224
  rw [Vector.toList_ofFn]
  refine (packWordBytes (wordCount := 7) (bytesPerWord := 4) (by decide)
    (fun i => state[i.val].toBitVec) _ ?_).trans ?_
  · intro index
    simpa only [Nat.mul_comm 8, Fin.getElem_fin, Nat.reduceSub] using
      wordByte_toBitVec (state[index.val / 4]'(by omega)) ((3 - index.val % 4) * 8) (by omega)
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by simp)]
    repeat rw [List.ofFn_succ]
    rw [List.ofFn_zero]
    simp (discharger := decide) only [getElem!_pos, toSpecState, Vector.getElem_map,
      toNat_flattenList_cons, toNat_flattenList_nil, BitVec.toNat_append, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add,
      Nat.shiftLeft_zero, Nat.or_zero, Nat.or_assoc, Fin.val_zero, Fin.val_succ]

end SHS.Equiv.SHA256.Digest
