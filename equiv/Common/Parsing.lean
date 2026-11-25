import equiv.Common.Chunks

/-! # Chunked parsing of aligned bit messages -/

namespace SHS.Equiv.Padding

open SHS.Equiv.Chunks

private theorem chunks_toArray_eq_ofFn {α : Type _} (items : List α) (width count : Nat)
    (positive : 0 < width) (aligned : items.length = width * count) :
    (listChunks width items).toArray =
      Array.ofFn (n := count) fun index => (items.drop (index.val * width)).take width := by
  rw [toChunks_eq_drop_take width positive items count aligned]
  ext index left right <;> simp

/-- Aligned word chunks fill the vector. Each index is in bounds for the array read. -/
private theorem wordFromChunk_eq_fromBits (bits : List Bool) (width count : Nat)
    (positive : 0 < width) (aligned : bits.length = width * count) (index : Fin count) :
    ((listChunks width bits).map (SHS.Word.fromBits (n := width))).toArray[index]?.getD 0 =
      SHS.Word.fromBits ((bits.drop (index.val * width)).take width) := by
  rw [toChunks_eq_drop_take width positive bits count aligned]
  simp only [Fin.getElem?_fin]
  rw [Array.getElem?_eq_getElem (by simp)]
  simp

/-- Parse an aligned message by slicing blocks and then slicing words within each block. -/
theorem parseChunked_eq_ofFn (bits : List Bool) (width words blocks : Nat)
    (widthPositive : 0 < width) (wordsPositive : 0 < words)
    (aligned : bits.length = (width * words) * blocks) :
    (listChunks (width * words) bits).toArray.map
        (fun block =>
          let decoded := (listChunks width block).map (SHS.Word.fromBits (n := width)) |>.toArray
          Vector.ofFn (n := words) fun index => decoded[index]?.getD 0) =
      Array.ofFn (n := blocks) fun blockIndex =>
        Vector.ofFn (n := words) fun wordIndex =>
          let block := (bits.drop (blockIndex.val * (width * words))).take (width * words)
          SHS.Word.fromBits ((block.drop (wordIndex.val * width)).take width) := by
  rw [chunks_toArray_eq_ofFn bits _ blocks (Nat.mul_pos widthPositive wordsPositive) aligned,
    Array.map_ofFn]
  refine congrArg Array.ofFn ?_
  funext blockIndex
  refine congrArg Vector.ofFn ?_
  funext wordIndex
  apply wordFromChunk_eq_fromBits _ _ _ widthPositive
  simp only [List.length_take, List.length_drop, aligned]
  apply Nat.min_eq_left
  have fits := Nat.mul_le_mul_right (width * words) (Nat.succ_le_of_lt blockIndex.isLt)
  rw [Nat.succ_mul, Nat.mul_comm blocks] at fits
  omega

end SHS.Equiv.Padding
