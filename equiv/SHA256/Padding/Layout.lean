import impl.SHA256
import equiv.SHA256.Lift
import equiv.SHA256.ToU32s
import equiv.Common.ByteArray
import equiv.Common.ArrayFold

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
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.ToU32s

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Layout

open scoped SHS.SHA256

/-! ## Byte-level definitions -/

/-- Number of zero bytes the streaming pad emits between the `0x80`
separator and the 8-byte length tag.  Lifts the inline conditional out
of every `implPaddedBytes`-related signature. -/
def zerosCount (data : ByteArray) : Nat :=
  if data.size % 64 < 56 then 55 - data.size % 64 else 64 + 55 - data.size % 64

theorem zerosCount_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    zerosCount data = 55 - data.size % 64 := by
  unfold zerosCount; rw [if_pos h]

theorem zerosCount_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    zerosCount data = 64 + 55 - data.size % 64 := by
  unfold zerosCount; rw [if_neg h]

/-- The 64-bit big-endian length encoding (eight bytes), matching the
inline expansion in `Impl.sha256`'s final block. -/
def lengthBE64 (bits : UInt64) : ByteArray := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  for i in [0:8] do
    bs := bs.push ((bits >>> ((7 - i) * 8).toUInt64) &&& 0xff).toUInt8
  return bs

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
  unfold lengthBE64
  simp [Id.run]
  rfl

theorem size_implPaddedBytes_mod (data : ByteArray) :
    (implPaddedBytes data).size % 64 = 0 := by
  unfold implPaddedBytes zerosCount
  simp [ByteArray.size_append]
  by_cases h : data.size % 64 < 56
  · simp [h]; omega
  · simp [h]; omega

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 8 := by
  unfold implPaddedBytes
  simp [ByteArray.size_append]

/-! ## Byte access on `implPaddedBytes` -/

theorem get!_implPaddedBytes_data (data : ByteArray) (i : Nat) (h : i < data.size) :
    (implPaddedBytes data).get! i = data.get! i := by
  unfold implPaddedBytes
  have hsz1 : i < (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  rw [get!_appendZeros_lt _ _ _ (by rw [ByteArray.size_push]; omega)]
  rw [get!_push_lt _ _ _ h]

theorem get!_implPaddedBytes_sep (data : ByteArray) :
    (implPaddedBytes data).get! data.size = 0x80 := by
  unfold implPaddedBytes
  have hsz1 : data.size <
      (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  rw [get!_appendZeros_lt _ _ _ (by rw [ByteArray.size_push]; omega)]
  exact get!_push_eq _ _

theorem get!_implPaddedBytes_zero (data : ByteArray) (i : Nat)
    (h1 : data.size + 1 ≤ i) (h2 : i < data.size + 1 + zerosCount data) :
    (implPaddedBytes data).get! i = 0 := by
  unfold implPaddedBytes
  have hsz1 : i < (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  apply get!_appendZeros_ge
  · rw [ByteArray.size_push]; omega
  · rw [ByteArray.size_push]; omega

theorem get!_implPaddedBytes_length (data : ByteArray) (i : Nat)
    (h1 : data.size + 1 + zerosCount data ≤ i)
    (h2 : i < (implPaddedBytes data).size) :
    (implPaddedBytes data).get! i =
      (lengthBE64 (data.size.toUInt64 <<< 3)).get!
        (i - (data.size + 1 + zerosCount data)) := by
  have hsz := size_implPaddedBytes_eq data
  unfold implPaddedBytes
  have heq_size : (appendZeros (data.push 0x80) (zerosCount data)).size
        = data.size + 1 + zerosCount data := by
    rw [size_appendZeros, ByteArray.size_push]
  rw [get!_append_right]
  · congr 1
    rw [heq_size]
  · rw [heq_size]; exact h1
  · rw [heq_size, size_lengthBE64]
    rw [hsz] at h2
    omega

/-! ## `lengthBE64` byte access -/

theorem lengthBE64_get!_eq (bits : UInt64) (i : Nat) (h : i < 8) :
    (lengthBE64 bits).get! i =
      ((bits >>> (((7 - i) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8 := by
  unfold lengthBE64
  simp [Id.run]
  rcases i with _|_|_|_|_|_|_|_|_
  all_goals (first | rfl | omega)

/-! ## `implPaddedBlocks` block view -/

/-- The `i`-th block of `implPaddedBlocks data` written directly via
`padded.get!`. -/
def paddedBlock (data : ByteArray) (i : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun (j : Fin 64) => (implPaddedBytes data).get! (i * 64 + j.val)

theorem implPaddedBlocks_foldl {β : Type*} (data : ByteArray)
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
  have : k * 64 + 64 ≤ data.size := by
    have hd := Nat.div_add_mod data.size 64
    have : (k + 1) * 64 ≤ data.size / 64 * 64 := Nat.mul_le_mul_right 64 h
    omega
  omega

/-- Final block (case `remaining < 56`): one extra block holding data,
`0x80`, zeros, and the bit-length tag. -/
theorem paddedBlock_final_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then
          (if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
           else if i.val = data.size % 64 then 0x80
           else 0)
        else
          ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock
  congr 1
  funext j
  set blocks := data.size / 64
  set remaining := data.size % 64 with hr
  have hd : data.size = 64 * blocks + remaining := (Nat.div_add_mod data.size 64).symm
  have hjvalid : blocks * 64 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_lt56 _ h]
    have : j.val < 64 := j.isLt
    omega
  by_cases hj56 : j.val < 56
  · simp only [hj56, if_true]
    by_cases hjr : j.val < remaining
    · simp only [hjr, if_true]
      have hpos : blocks * 64 + j.val < data.size := by
        have : j.val < remaining := hjr
        omega
      rw [get!_implPaddedBytes_data _ _ hpos]
    · simp only [hjr, if_false]
      by_cases hjeq : j.val = remaining
      · simp only [hjeq, if_true]
        have hpos : blocks * 64 + remaining = data.size := by omega
        rw [hpos]
        exact get!_implPaddedBytes_sep data
      · simp only [hjeq, if_false]
        have hpos1 : data.size + 1 ≤ blocks * 64 + j.val := by omega
        have hpos2 : blocks * 64 + j.val <
            data.size + 1 + zerosCount data := by
          rw [zerosCount_lt56 _ h]; omega
        exact get!_implPaddedBytes_zero _ _ hpos1 hpos2
  · simp only [hj56, if_false]
    have hpos1 : data.size + 1 +
        zerosCount data ≤ blocks * 64 + j.val := by
      rw [zerosCount_lt56 _ h]; omega
    rw [get!_implPaddedBytes_length _ _ hpos1 hjvalid]
    have hidx : blocks * 64 + j.val -
        (data.size + 1 + zerosCount data)
        = j.val - 56 := by
      rw [zerosCount_lt56 _ h]; omega
    rw [hidx]
    have hk : j.val - 56 < 8 := by have := j.isLt; omega
    rw [lengthBE64_get!_eq _ _ hk]
    congr 2
    have : 7 - (j.val - 56) = 63 - j.val := by omega
    rw [this]

/-- Final block A (case `remaining ≥ 56`): data bytes, then `0x80`, then
zeros (no length tag, since the block is full). -/
theorem paddedBlock_finalA_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
        else if i.val = data.size % 64 then 0x80
        else 0) := by
  unfold paddedBlock
  congr 1
  funext j
  set blocks := data.size / 64
  set remaining := data.size % 64 with hr
  have hd : data.size = 64 * blocks + remaining := (Nat.div_add_mod data.size 64).symm
  have hr_lt : remaining < 64 := by rw [hr]; exact Nat.mod_lt _ (by decide)
  have hr_ge : 56 ≤ remaining := by omega
  have hjvalid : blocks * 64 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]
    have : j.val < 64 := j.isLt
    omega
  by_cases hjr : j.val < remaining
  · simp only [hjr, if_true]
    have hpos : blocks * 64 + j.val < data.size := by omega
    rw [get!_implPaddedBytes_data _ _ hpos]
  · simp only [hjr, if_false]
    by_cases hjeq : j.val = remaining
    · simp only [hjeq, if_true]
      have hpos : blocks * 64 + remaining = data.size := by omega
      rw [hpos]
      exact get!_implPaddedBytes_sep data
    · simp only [hjeq, if_false]
      have hjlt64 : j.val < 64 := j.isLt
      have hpos1 : data.size + 1 ≤ blocks * 64 + j.val := by omega
      have hpos2 : blocks * 64 + j.val <
          data.size + 1 + zerosCount data := by
        rw [zerosCount_ge56 _ h]; omega
      exact get!_implPaddedBytes_zero _ _ hpos1 hpos2

/-- Final block B (case `remaining ≥ 56`): all zeros except the length
tag in the last 8 bytes. -/
theorem paddedBlock_finalB_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64 + 1) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock
  congr 1
  funext j
  set blocks := data.size / 64
  set remaining := data.size % 64 with hr
  have hd : data.size = 64 * blocks + remaining := (Nat.div_add_mod data.size 64).symm
  have hr_lt : remaining < 64 := by rw [hr]; exact Nat.mod_lt _ (by decide)
  have hr_ge : 56 ≤ remaining := by omega
  have hjlt : j.val < 64 := j.isLt
  have hpsize : (implPaddedBytes data).size = (blocks + 2) * 64 := by
    rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]
    omega
  have hpos_valid : (blocks + 1) * 64 + j.val < (implPaddedBytes data).size := by
    rw [hpsize]; omega
  by_cases hj56 : j.val < 56
  · simp only [hj56, if_true]
    have hpos1 : data.size + 1 ≤ (blocks + 1) * 64 + j.val := by omega
    have hpos2 : (blocks + 1) * 64 + j.val <
        data.size + 1 + zerosCount data := by
      rw [zerosCount_ge56 _ h]; omega
    exact get!_implPaddedBytes_zero _ _ hpos1 hpos2
  · simp only [hj56, if_false]
    have hpos1 : data.size + 1 + zerosCount data
        ≤ (blocks + 1) * 64 + j.val := by
      rw [zerosCount_ge56 _ h]; omega
    rw [get!_implPaddedBytes_length _ _ hpos1 hpos_valid]
    have hidx : (blocks + 1) * 64 + j.val -
        (data.size + 1 + zerosCount data)
        = j.val - 56 := by
      rw [zerosCount_ge56 _ h]; omega
    rw [hidx]
    have hk : j.val - 56 < 8 := by omega
    rw [lengthBE64_get!_eq _ _ hk]
    congr 2
    have : 7 - (j.val - 56) = 63 - j.val := by omega
    rw [this]

/-! ## Total padded block count -/

theorem totalBlocks_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 1 := by
  rw [size_implPaddedBytes_eq, zerosCount_lt56 _ h]
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  omega

theorem totalBlocks_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 2 := by
  rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  have hr_lt : data.size % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

end SHS.Equiv.SHA256.Padding.Layout
