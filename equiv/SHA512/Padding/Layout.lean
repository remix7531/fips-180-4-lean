import equiv.Common.ByteArray
import equiv.Common.ArrayFold
import equiv.Common.PaddingLayout

/-! # SHA-512 padding: byte-level layout

Parallel to `equiv/SHA256/Padding/Layout.lean` with 128-byte blocks
and a 16-byte length tag (high 8 bytes literal zero, low 8 bytes
big-endian `UInt64` bit-count).  The cutoff is `% 128 < 112` (128
minus 1 separator minus 16 length suffix).

Reifies the streaming pad inside `Impl.sha512` as `implPaddedBytes`
and its 128-byte block view `implPaddedBlocks`, then proves the
byte-by-byte layout in three cases:
- `complete`: a fully-data block (`k < data.size / 128`)
- `final<112`: one extra block holding data, `0x80`, zeros, length tag
- `final≥112`: two tail blocks — A holds data + `0x80` + zeros, B
  holds zeros + length tag. -/

open SHS.Equiv.ByteArray
open SHS.Equiv.ArrayFold

namespace SHS.Equiv.SHA512.Padding.Layout

/-! ## Byte-level definitions -/

/-- Number of zero bytes between the `0x80` separator and the 16-byte
length tag.  Mirrors the SHA-256 definition at block size 128 and length
size 16. -/
def zerosCount (data : ByteArray) : Nat :=
  SHS.Equiv.Padding.zeroPaddingCount data.size 128 16

theorem zerosCount_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    zerosCount data = 111 - data.size % 128 := by
  unfold zerosCount SHS.Equiv.Padding.zeroPaddingCount
  rw [ite_eq_left h]

theorem zerosCount_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    zerosCount data = 128 + 111 - data.size % 128 := by
  unfold zerosCount SHS.Equiv.Padding.zeroPaddingCount
  rw [ite_eq_right h]

/-- The 128-bit big-endian length encoding (sixteen bytes): high 8 bytes
literal zero, low 8 bytes big-endian `UInt64` of `bits`.  Matches the
inline expansion in `Impl.sha512`'s final block. -/
def lengthBE128 (bits : UInt64) : ByteArray :=
  ⟨Array.ofFn (n := 16) fun i =>
    if i.val < 8 then 0
    else ((bits >>> ((15 - i.val) * 8).toUInt64) &&& 0xff).toUInt8⟩

/-- Reified streaming pad of `Impl.sha512`.  Mirrors the impl's logic
without unfolding `sha512`: append `data`, then `0x80`, then enough zeros
to land at 112 mod 128, then the 16-byte big-endian bit-length tag. -/
def implPaddedBytes (data : ByteArray) : ByteArray :=
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  appendZeros (data.push 0x80) (zerosCount data) ++ lengthBE128 totalBits

/-- Slice the padded byte sequence into 128-byte blocks. -/
def implPaddedBlocks (data : ByteArray) : Array (Vector UInt8 128) :=
  let padded := implPaddedBytes data
  let n := padded.size / 128
  Array.ofFn (n := n) fun i =>
    Vector.ofFn fun (j : Fin 128) =>
      padded.get! (i.val * 128 + j.val)

/-! ## Easy invariants -/

@[simp] theorem size_lengthBE128 (bits : UInt64) : (lengthBE128 bits).size = 16 := by
  change (Array.ofFn _ : Array UInt8).size = 16
  exact Array.size_ofFn

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 16 := by
  unfold implPaddedBytes
  simp [ByteArray.size_append]

private theorem paddedSize_eq (data : ByteArray) :
    (implPaddedBytes data).size =
      (data.size / 128 + (if data.size % 128 < 112 then 0 else 1) + 1) * 128 := by
  rw [size_implPaddedBytes_eq]
  exact SHS.Equiv.Padding.paddedSize data.size 128 16 (by decide)

theorem size_implPaddedBytes_mod (data : ByteArray) :
    (implPaddedBytes data).size % 128 = 0 := by
  rw [paddedSize_eq, Nat.mul_mod_left]

/-! ## Byte access on `implPaddedBytes` -/

theorem get!_implPaddedBytes_data (data : ByteArray) (i : Nat) (h : i < data.size) :
    (implPaddedBytes data).get! i = data.get! i := by
  unfold implPaddedBytes
  rw [get!_append_padding, ite_eq_left h]

/-- A bounded read of the big-endian length field. -/
theorem lengthBE128_get! (bits : UInt64) (i : Nat) (h : i < 16) :
    (lengthBE128 bits).get! i =
      (if i < 8 then 0
       else ((bits >>> (((15 - i) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8) := by
  rw [get!_eq_getElem!, getElem!_pos _ _ (by simpa only [size_lengthBE128] using h),
    ByteArray.getElem_eq_getElem_data]
  simp only [lengthBE128, Array.getElem_ofFn]

private theorem lengthBE128_get!_atBlockOffset (bits : UInt64) (index : Fin 128)
    (inTag : 112 ≤ index.val) :
    (lengthBE128 bits).get! (index.val - 112) =
      if index.val < 120 then 0
      else ((bits >>> (((127 - index.val) * 8).toUInt64)) &&& 0xff).toUInt8 := by
  rw [lengthBE128_get! _ _ (by omega)]
  simp only [show 15 - (index.val - 112) = 127 - index.val by omega,
    show index.val - 112 < 8 ↔ index.val < 120 by omega]

/-! ## `implPaddedBlocks` block view -/

/-- The `i`-th block of `implPaddedBlocks data` written directly via
`padded.get!`. -/
def paddedBlock (data : ByteArray) (i : Nat) : Vector UInt8 128 :=
  Vector.ofFn fun (j : Fin 128) => (implPaddedBytes data).get! (i * 128 + j.val)

theorem implPaddedBlocks_foldl {β : Type _} (data : ByteArray)
    (f : β → Vector UInt8 128 → β) (init : β) :
    (implPaddedBlocks data).foldl f init =
      Fin.foldl ((implPaddedBytes data).size / 128)
        (fun b i => f b (paddedBlock data i.val)) init := by
  unfold implPaddedBlocks
  rw [array_foldl_ofFn_eq_fin_foldl]
  rfl

/-- Complete-block formula: for `k < data.size / 128`, the `k`-th
padded block equals the impl's `Vector.ofFn fun j => data.get! (k*128+j)`. -/
theorem paddedBlock_complete (data : ByteArray) (k : Nat) (h : k < data.size / 128) :
    paddedBlock data k =
      Vector.ofFn (fun j : Fin 128 => data.get! (k * 128 + j.val)) := by
  unfold paddedBlock
  congr 1
  funext j
  apply get!_implPaddedBytes_data
  omega

/-- Final block (case `remaining < 112`): one extra block holding data,
`0x80`, zeros, and the 16-byte length tag (8 zero bytes + 8-byte BE
length).  Specialisation of `get!_append_padding` at block index
`data.size / 128` and `remaining < 112` (so data, separator, zeros,
and length tag all fit in one block). -/
theorem paddedBlock_final_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    paddedBlock data (data.size / 128) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < 112 then
          (if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
           else if i.val = data.size % 128 then 0x80
           else 0)
        else if i.val < 120 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [SHS.Equiv.Padding.get!_padding_tail data _ 128 16 (by decide)]
  by_cases beforeTag : index.val < 112 <;>
    simp (discharger := omega) only [h, ↓reduceIte, Nat.zero_add, Nat.reduceSub, beforeTag, ite_eq_right,
      lengthBE128_get!_atBlockOffset]

/-- Final block A (case `remaining ≥ 112`): data bytes, then `0x80`,
then zeros (no length tag — that's in block B).  Specialisation of
`get!_append_padding` at block index `data.size / 128` when there's
no room for the 16-byte length suffix. -/
theorem paddedBlock_finalA_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    paddedBlock data (data.size / 128) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
        else if i.val = data.size % 128 then 0x80
        else 0) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [SHS.Equiv.Padding.get!_padding_tail data _ 128 16 (by decide)]
  simp (discharger := omega) only [h, ↓reduceIte, ite_eq_left]

/-- Final block B (case `remaining ≥ 112`): all zeros except the 16-byte
length tag in bytes 112..127.  Specialisation of `get!_append_padding`
at block index `data.size / 128 + 1`, which lies entirely past the
zero-pad cutoff. -/
theorem paddedBlock_finalB_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    paddedBlock data (data.size / 128 + 1) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < 120 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock implPaddedBytes zerosCount
  congr 1
  funext index
  rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc,
    SHS.Equiv.Padding.get!_padding_tail data _ 128 16 (by decide)]
  by_cases beforeTag : index.val < 112 <;>
    simp (discharger := omega) only [h, ↓reduceIte, Nat.reduceSub, ite_eq_right, ite_eq_left,
      Nat.add_sub_add_left, lengthBE128_get!_atBlockOffset]

/-! ## Total padded block count -/

theorem totalBlocks_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    (implPaddedBytes data).size / 128 = data.size / 128 + 1 := by
  rw [paddedSize_eq]
  simp [h]

theorem totalBlocks_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    (implPaddedBytes data).size / 128 = data.size / 128 + 2 := by
  rw [paddedSize_eq]
  simp only [h, ↓reduceIte, Nat.mul_div_cancel _ (by decide : 0 < 128), Nat.add_assoc]

end SHS.Equiv.SHA512.Padding.Layout
