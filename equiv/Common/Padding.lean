import equiv.Common.ByteArray
import equiv.Common.Bytes
import equiv.Common.PaddingLayout

/-! # Common: padding alignment and byte decoding -/

namespace SHS.Equiv.Padding

open SHS.Equiv.ByteArray SHS.Equiv.Bytes

/-- Decode a byte array MSB-first within each byte. -/
def bytesToBitMessage (data : ByteArray) : SHS.Message :=
  data.data.toList.flatMap byteToBits

theorem bytesToBitMessage_length (data : ByteArray) :
    (bytesToBitMessage data).length = 8 * data.size := by
  simp only [bytesToBitMessage, flatMap_byteToBits_length, Array.length_toList,
    ByteArray.size_data]

theorem bytesToBitMessage_append (a b : ByteArray) :
    bytesToBitMessage (a ++ b) = bytesToBitMessage a ++ bytesToBitMessage b := by
  simp [bytesToBitMessage]

/-- The separator byte contributes the initial one bit and seven pad bits. -/
theorem bytesToBitMessage_push_0x80 (data : ByteArray) :
    bytesToBitMessage (data.push 0x80) =
      bytesToBitMessage data ++ ([true] ++ List.replicate 7 false) := by
  simp only [bytesToBitMessage, ByteArray.data_push, Array.toList_push, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem bytesToBitMessage_appendZeros (data : ByteArray) (count : Nat) :
    bytesToBitMessage (appendZeros data count) =
      bytesToBitMessage data ++ List.replicate (8 * count) false := by
  simp only [appendZeros, bytesToBitMessage, ByteArray.toList_data_append,
    Array.toList_replicate, List.flatMap_append, List.flatMap_replicate]
  rw [show byteToBits 0 = List.replicate 8 false from rfl,
    List.flatten_replicate_replicate, Nat.mul_comm]

/-- The implementation's length shift fits in its low 64 bits. -/
theorem totalBits_toNat (data : ByteArray) (fits : data.size < 2 ^ 61) :
    (data.size.toUInt64 <<< 3).toNat = 8 * data.size := by
  rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have sizeFits : data.size < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt sizeFits]
  change (data.size <<< 3) % 2 ^ 64 = 8 * data.size
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  omega

/-- An aligned offset inside the search range is its unique solution. -/
theorem find_modEq_offset {length residue modulus padding : Nat} (fits : padding < modulus)
    (aligned : length + padding ≡ residue [MOD modulus]) :
    (List.range modulus).find? (fun extra => decide (length + extra ≡ residue [MOD modulus])) =
      some padding := by
  rw [List.find?_range_eq_some]
  refine ⟨by simpa using aligned, List.mem_range.mpr fits, ?_⟩
  intro smaller hsmaller
  suffices ¬ (length + smaller ≡ residue [MOD modulus]) by simpa using this
  intro smallerAligned
  obtain ⟨leftMultiple, rightMultiple, multiplesEq⟩ :=
    Nat.mod_eq_mod_iff.mp (aligned.trans smallerAligned.symm)
  have congruent : padding % modulus = smaller % modulus :=
    Nat.mod_eq_mod_iff.mpr ⟨leftMultiple, rightMultiple, by omega⟩
  rw [Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt (Nat.lt_trans hsmaller fits)] at congruent
  omega

/-- The zero-bit count in the spec includes the rest of the separator byte. -/
theorem find_bit_padding (size blockBytes tagBytes : Nat) (tagFits : tagBytes < blockBytes) :
    (List.range (8 * blockBytes)).find?
        (fun extra =>
          decide (8 * size + 1 + extra ≡ 8 * (blockBytes - tagBytes) [MOD 8 * blockBytes])) =
      some (7 + 8 * zeroPaddingCount size blockBytes tagBytes) := by
  apply find_modEq_offset
  · have remainderBound := Nat.mod_lt size (show 0 < blockBytes by omega)
    simp only [zeroPaddingCount]
    split <;> omega
  · change (8 * size + 1 + (7 + 8 * zeroPaddingCount size blockBytes tagBytes)) % (8 * blockBytes) =
      (8 * (blockBytes - tagBytes)) % (8 * blockBytes)
    rw [show 8 * size + 1 + (7 + 8 * zeroPaddingCount size blockBytes tagBytes) =
          8 * (size + 1 + zeroPaddingCount size blockBytes tagBytes) by omega,
      lengthFieldStart size blockBytes tagBytes tagFits, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
      Nat.mul_add_mod_self_right]

/-- The bounded, coordinate-based vector read agrees with a contiguous list slice. -/
private theorem byteWindow_toList (data : ByteArray) (offset count : Nat)
    (fits : offset + count ≤ data.size) :
    (Vector.ofFn (n := count) fun index => data.get! (offset + index.val)).toList =
      (data.data.toList.drop offset).take count := by
  apply List.ext_getElem
  · simp only [Vector.length_toList, List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data]
    exact (Nat.min_eq_left (by omega)).symm
  · intro index indexWindow indexSlice
    have indexBound : index < count := by simpa using indexWindow
    have sourceBound : offset + index < data.size := by omega
    simp only [Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take, List.getElem_drop,
      Array.getElem_toList, get!_eq_getElem!, getElem!_pos data (offset + index) sourceBound,
      ByteArray.getElem_eq_getElem_data]

/-- Reading a bounded byte window and decoding its bits gives the corresponding bit slice. -/
theorem byteWindow_toBits (data : ByteArray) (offset count : Nat)
    (fits : offset + count ≤ data.size) :
    (Vector.ofFn (n := count) fun index => data.get! (offset + index.val)).toList.flatMap
        byteToBits =
      ((bytesToBitMessage data).drop (8 * offset)).take (8 * count) := by
  rw [bytesToBitMessage, flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8, byteWindow_toList]
  exact fits

end SHS.Equiv.Padding
