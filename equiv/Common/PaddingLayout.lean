import equiv.Common.ByteArray

/-! # Geometry of SHA-2 byte padding -/

namespace SHS.Equiv.Padding

/-- Number of zero bytes between the separator and the length field. -/
def zeroPaddingCount (size blockBytes tagBytes : Nat) : Nat :=
  let cutoff := blockBytes - tagBytes
  let remainder := size % blockBytes
  if remainder < cutoff then cutoff - 1 - remainder
  else blockBytes + (cutoff - 1) - remainder

/-- The length field begins at the cutoff of its chosen block. -/
theorem lengthFieldStart (size blockBytes tagBytes : Nat) (tagFits : tagBytes < blockBytes) :
    size + 1 + zeroPaddingCount size blockBytes tagBytes =
      (size / blockBytes + (if size % blockBytes < blockBytes - tagBytes then 0 else 1)) *
        blockBytes + (blockBytes - tagBytes) := by
  have blockPositive : 0 < blockBytes := by omega
  have remainderBound := Nat.mod_lt size blockPositive
  have sizeSplit := Nat.div_add_mod size blockBytes
  rw [Nat.mul_comm blockBytes (size / blockBytes)] at sizeSplit
  by_cases beforeCutoff : size % blockBytes < blockBytes - tagBytes
  · simp only [zeroPaddingCount, beforeCutoff, ↓reduceIte, Nat.add_zero]
    omega
  · simp only [zeroPaddingCount, beforeCutoff, ↓reduceIte, Nat.succ_mul]
    omega

/-- The length field ends at the boundary of its block. -/
theorem paddedSize (size blockBytes tagBytes : Nat) (tagFits : tagBytes < blockBytes) :
    size + 1 + zeroPaddingCount size blockBytes tagBytes + tagBytes =
      (size / blockBytes + (if size % blockBytes < blockBytes - tagBytes then 0 else 1) + 1) *
        blockBytes := by
  rw [lengthFieldStart size blockBytes tagBytes tagFits, Nat.succ_mul]
  omega

/-- Index the padding relative to the start of the first block after the complete data blocks. -/
theorem get!_padding_tail (data lengthField : ByteArray) (blockBytes tagBytes : Nat)
    (tagFits : tagBytes < blockBytes) (index : Nat) :
    let start := data.size / blockBytes * blockBytes
    let remaining := data.size % blockBytes
    let cutoff := blockBytes - tagBytes
    let tagStart := (if remaining < cutoff then 0 else blockBytes) + cutoff
    (ByteArray.appendZeros (data.push 0x80) (zeroPaddingCount data.size blockBytes tagBytes) ++
      lengthField).get! (start + index) =
      if index < remaining then data.get! (start + index)
      else if index = remaining then 0x80
      else if index < tagStart then 0
      else lengthField.get! (index - tagStart) := by
  dsimp only
  have sizeSplit := Nat.div_add_mod data.size blockBytes
  rw [Nat.mul_comm blockBytes] at sizeSplit
  have insideData : (data.size / blockBytes * blockBytes + index < data.size) ↔
      index < data.size % blockBytes := by omega
  have atSeparator : (data.size / blockBytes * blockBytes + index = data.size) ↔
      index = data.size % blockBytes := by omega
  rw [ByteArray.get!_append_padding, lengthFieldStart _ _ _ tagFits]
  by_cases beforeCutoff : data.size % blockBytes < blockBytes - tagBytes <;>
    simp only [insideData, atSeparator, beforeCutoff, ↓reduceIte, Nat.zero_add, Nat.add_zero,
      Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.add_sub_add_left]

end SHS.Equiv.Padding
