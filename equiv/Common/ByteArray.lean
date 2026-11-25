/-! # Common: byte-array padding and indexing -/

namespace SHS.Equiv.ByteArray

/-- Append `n` zero bytes to a `ByteArray`. -/
def appendZeros (bs : ByteArray) (n : Nat) : ByteArray :=
  bs ++ ⟨Array.replicate n 0⟩

@[simp] theorem size_appendZeros (bs : ByteArray) (n : Nat) :
    (appendZeros bs n).size = bs.size + n := by
  rw [appendZeros, ByteArray.size_append]
  change bs.size + (Array.replicate n (0 : UInt8)).size = _
  rw [Array.size_replicate]

/-- Convert the implementation's `ByteArray.get!` to the indexing notation
used by the standard library. -/
theorem get!_eq_getElem! (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, ByteArray.getElem_eq_getElem_data]
    exact getElem!_pos a.data i h
  · rw [getElem!_neg a i h]
    exact getElem!_neg a.data i h

/-- Byte access across the data, separator, zero padding, and length field. -/
theorem get!_append_padding (data lengthField : ByteArray) (zeros pos : Nat) :
    (appendZeros (data.push 0x80) zeros ++ lengthField).get! pos =
      (if pos < data.size then data.get! pos
       else if pos = data.size then 0x80
       else if pos < data.size + 1 + zeros then 0
       else lengthField.get! (pos - (data.size + 1 + zeros))) := by
  simp only [appendZeros, ByteArray.get!, ByteArray.data_append, ByteArray.data_push,
    getElem!_def, Array.getElem?_append, Array.getElem?_push, Array.getElem?_replicate,
    Array.size_append, Array.size_push, Array.size_replicate, ByteArray.size_data]
  by_cases hPrefix : pos < data.size + 1 + zeros
  · rw [ite_eq_left hPrefix]
    by_cases hData : pos < data.size
    · simp [hData, Nat.ne_of_lt hData, show pos < data.size + 1 by omega]
    · by_cases hSeparator : pos = data.size
      · simp [hSeparator]
      · simp [hData, hSeparator, hPrefix, show ¬ pos < data.size + 1 by omega,
          show pos - (data.size + 1) < zeros by omega]
  · simp [hPrefix, show ¬ pos < data.size by omega, show pos ≠ data.size by omega]

end SHS.Equiv.ByteArray
