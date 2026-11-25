import equiv.Common.ByteArray
import equiv.Common.ArrayFold
import equiv.Common.PaddingLayout

/-! # SHA-256 padding: byte-level layout

Reifies the streaming pad inside `Impl.sha256` as `implPaddedBytes`
and its 64-byte block view `implPaddedBlocks`, then proves the
byte-by-byte layout in three cases:
- `complete`: a fully-data block (`k < data.size / 64`)
- `final<56`: one extra block holding data, `0x80`, zeros, length
- `final≥56`: two tail blocks — A holds data + `0x80` + zeros, B holds
  zeros + length. -/

open SHS.Equiv.ByteArray
open SHS.Equiv.ArrayFold

namespace SHS.Equiv.SHA256.Padding.Layout

/-! ## Byte-level definitions -/

/-- Number of zero bytes the streaming pad emits between the `0x80`
separator and the 8-byte length tag.  Lifts the inline conditional out
of every `implPaddedBytes`-related signature. -/
def zerosCount (data : ByteArray) : Nat :=
  SHS.Equiv.Padding.zeroPaddingCount data.size 64 8

theorem zerosCount_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    zerosCount data = 55 - data.size % 64 := by
  unfold zerosCount SHS.Equiv.Padding.zeroPaddingCount
  rw [ite_eq_left h]

theorem zerosCount_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    zerosCount data = 64 + 55 - data.size % 64 := by
  unfold zerosCount SHS.Equiv.Padding.zeroPaddingCount
  rw [ite_eq_right h]

/-- The 64-bit big-endian length encoding (eight bytes), matching the
inline expansion in `Impl.sha256`'s final block. -/
def lengthBE64 (bits : UInt64) : ByteArray :=
  ⟨Array.ofFn (n := 8) fun i =>
    ((bits >>> ((7 - i.val) * 8).toUInt64) &&& 0xff).toUInt8⟩

/-- Reified streaming pad of `Impl.sha256`.  Mirrors the impl's logic
without unfolding `sha256`: append `data`, then `0x80`, then enough zeros
to land at 56 mod 64, then the 64-bit big-endian bit-length. -/
def implPaddedBytes (data : ByteArray) : ByteArray :=
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  appendZeros (data.push 0x80) (zerosCount data) ++ lengthBE64 totalBits

/-- Slice the padded byte sequence into 64-byte blocks. -/
def implPaddedBlocks (data : ByteArray) : Array (Vector UInt8 64) :=
  let padded := implPaddedBytes data
  let n := padded.size / 64
  Array.ofFn (n := n) fun i =>
    Vector.ofFn fun (j : Fin 64) =>
      padded.get! (i.val * 64 + j.val)

/-! ## Easy invariants -/

@[simp] theorem size_lengthBE64 (bits : UInt64) : (lengthBE64 bits).size = 8 := by
  change (Array.ofFn _ : Array UInt8).size = 8
  exact Array.size_ofFn

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 8 := by
  unfold implPaddedBytes
  simp [ByteArray.size_append]

private theorem paddedSize_eq (data : ByteArray) :
    (implPaddedBytes data).size =
      (data.size / 64 + (if data.size % 64 < 56 then 0 else 1) + 1) * 64 := by
  rw [size_implPaddedBytes_eq]
  exact SHS.Equiv.Padding.paddedSize data.size 64 8 (by decide)

theorem size_implPaddedBytes_mod (data : ByteArray) :
    (implPaddedBytes data).size % 64 = 0 := by
  rw [paddedSize_eq, Nat.mul_mod_left]

/-! ## Byte access on `implPaddedBytes` -/

theorem get!_implPaddedBytes_data (data : ByteArray) (i : Nat) (h : i < data.size) :
    (implPaddedBytes data).get! i = data.get! i := by
  unfold implPaddedBytes
  rw [get!_append_padding, ite_eq_left h]

/-- A bounded read of the big-endian length field. -/
theorem lengthBE64_get!_eq (bits : UInt64) (i : Nat) (h : i < 8) :
    (lengthBE64 bits).get! i =
      ((bits >>> (((7 - i) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8 := by
  rw [get!_eq_getElem!, getElem!_pos _ _ (by simpa using h),
    ByteArray.getElem_eq_getElem_data]
  exact Array.getElem_ofFn h

private theorem lengthBE64_get!_atBlockOffset (bits : UInt64) (index : Fin 64)
    (inTag : 56 ≤ index.val) :
    (lengthBE64 bits).get! (index.val - 56) =
      ((bits >>> (((63 - index.val) * 8).toUInt64)) &&& 0xff).toUInt8 := by
  rw [lengthBE64_get!_eq _ _ (by omega), show 7 - (index.val - 56) = 63 - index.val by omega]

/-! ## `implPaddedBlocks` block view -/

/-- The `i`-th block of `implPaddedBlocks data` written directly via
`padded.get!`. -/
def paddedBlock (data : ByteArray) (i : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun (j : Fin 64) => (implPaddedBytes data).get! (i * 64 + j.val)

theorem implPaddedBlocks_foldl {β : Type _} (data : ByteArray)
    (f : β → Vector UInt8 64 → β) (init : β) :
    (implPaddedBlocks data).foldl f init =
      Fin.foldl ((implPaddedBytes data).size / 64)
        (fun b i => f b (paddedBlock data i.val)) init := by
  unfold implPaddedBlocks
  rw [array_foldl_ofFn_eq_fin_foldl]
  rfl

/-- Complete-block formula: for `k < data.size / 64`, the `k`-th padded block
equals the impl's `Vector.ofFn fun j => data.get! (k*64+j)`. -/
theorem paddedBlock_complete (data : ByteArray) (k : Nat) (h : k < data.size / 64) :
    paddedBlock data k = Vector.ofFn (fun j : Fin 64 => data.get! (k * 64 + j.val)) := by
  unfold paddedBlock
  congr 1
  funext j
  apply get!_implPaddedBytes_data
  omega

/-- Final block (case `remaining < 56`): one extra block holding data,
`0x80`, zeros, and the bit-length tag.  Specialisation of
`get!_append_padding` at block index `data.size / 64` and `remaining
< 56` (so the data, separator, zeros, and length tag all fit). -/
theorem paddedBlock_final_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then
          (if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
           else if i.val = data.size % 64 then 0x80
           else 0)
        else
          ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [SHS.Equiv.Padding.get!_padding_tail data _ 64 8 (by decide)]
  by_cases beforeTag : index.val < 56 <;>
    simp (discharger := omega) only [h, ↓reduceIte, Nat.zero_add, Nat.reduceSub, beforeTag, ite_eq_right,
      lengthBE64_get!_atBlockOffset]

/-- Final block A (case `remaining ≥ 56`): data bytes, then `0x80`, then
zeros (no length tag — that's in block B).  Specialisation of
`get!_append_padding` at block index `data.size / 64` when there's
no room for the length suffix. -/
theorem paddedBlock_finalA_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
        else if i.val = data.size % 64 then 0x80
        else 0) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [SHS.Equiv.Padding.get!_padding_tail data _ 64 8 (by decide)]
  simp (discharger := omega) only [h, ↓reduceIte, ite_eq_left]

/-- Final block B (case `remaining ≥ 56`): all zeros except the length
tag in the last 8 bytes.  Specialisation of `get!_append_padding`
at block index `data.size / 64 + 1`, which lies entirely past the
zero-pad cutoff. -/
theorem paddedBlock_finalB_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64 + 1) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc,
    SHS.Equiv.Padding.get!_padding_tail data _ 64 8 (by decide)]
  by_cases beforeTag : index.val < 56 <;>
    simp (discharger := omega) only [h, ↓reduceIte, Nat.reduceSub, ite_eq_right, ite_eq_left, beforeTag,
      Nat.add_sub_add_left, lengthBE64_get!_atBlockOffset]

/-! ## Total padded block count -/

theorem totalBlocks_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 1 := by
  rw [paddedSize_eq]
  simp [h]

theorem totalBlocks_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 2 := by
  rw [paddedSize_eq]
  simp only [h, ↓reduceIte, Nat.mul_div_cancel _ (by decide : 0 < 64), Nat.add_assoc]

end SHS.Equiv.SHA256.Padding.Layout
