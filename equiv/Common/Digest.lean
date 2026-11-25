import equiv.Common.Bytes

/-! # Common big-endian digest reconstruction -/

namespace SHS.Equiv.Digest

open SHS.Equiv.Bytes SHS.Equiv.FromBits

/-- Packing a byte list concatenates the bytes in big-endian order. -/
private theorem packBytes {width : Nat} (bytes : List UInt8) :
    SHS.Word.fromBits (n := width) (bytes.flatMap byteToBits) =
      (BitVec.flattenList (bytes.map UInt8.toBitVec)).setWidth width := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    rw [List.flatMap_cons, fromBits_append_same_width, fromBits_byteToBits, ih]
    rw [List.map_cons, BitVec.flattenList, BitVec.setWidth_cast,
      BitVec.setWidth_append_eq_shiftLeft_setWidth_or, flatMap_byteToBits_length]
    simp only [List.length_map]

/-- If the bytes select successive big-endian slices of the words, then
packing the bytes is the same as concatenating the words. -/
theorem packWordBytes {wordCount bytesPerWord : Nat} (positive : 0 < bytesPerWord)
    (wordAt : Fin wordCount → BitVec (8 * bytesPerWord))
    (byteAt : Fin (wordCount * bytesPerWord) → UInt8)
    (agrees : ∀ i, (byteAt i).toBitVec =
      (wordAt ⟨i.val / bytesPerWord, Nat.div_lt_of_lt_mul (by
        simpa only [Nat.mul_comm bytesPerWord wordCount] using i.isLt)⟩).extractLsb'
        (8 * (bytesPerWord - 1 - i.val % bytesPerWord)) 8) :
    SHS.Word.fromBits (n := 8 * (wordCount * bytesPerWord))
      ((List.ofFn byteAt).flatMap byteToBits) =
      (BitVec.flattenList (List.ofFn wordAt)).setWidth (8 * (wordCount * bytesPerWord)) := by
  rw [packBytes]
  apply BitVec.eq_of_getMsbD_eq
  intro index indexFits
  have wordWidth : 8 * bytesPerWord * wordCount = 8 * (wordCount * bytesPerWord) := by ac_rfl
  have byteIndexFits : index / 8 < wordCount * bytesPerWord := Nat.div_lt_of_lt_mul indexFits
  have wordIndexFits : index / (8 * bytesPerWord) < wordCount :=
    Nat.div_lt_of_lt_mul (wordWidth.symm ▸ indexFits)
  simp only [BitVec.getMsbD_setWidth, List.length_map, List.length_ofFn, wordWidth, Nat.sub_self,
    Nat.zero_le, decide_true, Bool.true_and, Nat.add_sub_cancel, BitVec.getMsbD_flattenList,
    List.getElem?_map, List.getElem?_ofFn, dite_eq_left byteIndexFits, dite_eq_left wordIndexFits,
    Option.map_some, Option.getD_some]
  rw [agrees, BitVec.getMsbD_extractLsb']
  have divIndex : index / 8 / bytesPerWord = index / (8 * bytesPerWord) := Nat.div_div_eq_div_mul ..
  have byteInWord : index / 8 % bytesPerWord < bytesPerWord := Nat.mod_lt _ positive
  have bitInByte : index % 8 < 8 := Nat.mod_lt _ (by decide)
  have offsetFits : 8 * (bytesPerWord - 1 - index / 8 % bytesPerWord) + 8 - index % 8 ≤
      8 * bytesPerWord := by omega
  have offset : 8 * bytesPerWord - (8 * (bytesPerWord - 1 - index / 8 % bytesPerWord) + 8 -
      index % 8) = index % (8 * bytesPerWord) := by
    rw [Nat.mod_mul]
    omega
  simp only [divIndex, bitInByte, offsetFits, offset, decide_true, Bool.true_and]

/-- The leading word occupies the bits above the rest of the concatenation. -/
theorem toNat_flattenList_cons {width : Nat} (word : BitVec width) (words : List (BitVec width)) :
    (BitVec.flattenList (word :: words)).toNat =
      word.toNat <<< (width * words.length) ||| (BitVec.flattenList words).toNat := by
  rw [BitVec.flattenList, BitVec.toNat_cast, BitVec.toNat_append]

/-- An empty concatenation contributes no bits. -/
theorem toNat_flattenList_nil {width : Nat} :
    (BitVec.flattenList ([] : List (BitVec width))).toNat = 0 := rfl

end SHS.Equiv.Digest
