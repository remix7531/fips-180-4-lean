import equiv.SHA512.Padding.Layout
import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.Padding.Parsing
import equiv.SHA512.ToU64s
import equiv.Common.ArrayFold

/-! # SHA-512 padding: streaming refactor of `Impl.sha512`

Parallel to `equiv/SHA256/Padding/Equiv.lean` at 128-byte blocks. -/

open SHS.Equiv.ArrayFold
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Padding.Layout

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Equiv

open scoped SHS.SHA512

/-- IV-generic block-list re-statement of `Impl.sha512State`. -/
def implSha512StateRefactored (data : ByteArray) (H0 : Impl.State) : Impl.State :=
  (implPaddedBlocks data).foldl (fun s b => Impl.compress s (Impl.toU64s b)) H0

/-- Block-list re-statement of `Impl.sha512`. -/
def implSha512Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512

theorem implSha512Refactored_eq_foldl (data : ByteArray) :
    implSha512Refactored data =
      (implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512 := rfl

private theorem impl_sha512State_eq_extract (data : ByteArray) (H0 : Impl.State) :
    Impl.sha512State data H0 =
      let blocks := data.size / 128
      let remaining := data.size % 128
      let totalBits : UInt64 := data.size.toUInt64 <<< 3
      let state : Impl.State := Fin.foldl blocks (fun state (i : Fin blocks) =>
        let block : Vector UInt8 128 := Vector.ofFn fun j : Fin 128 =>
          data.get! (i.val * 128 + j.val)
        Impl.compress state (Impl.toU64s block)) H0
      let finalBlockA : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
        if i.val < remaining then data.get! (blocks * 128 + i.val)
        else if i.val = remaining then 0x80
        else 0
      let (state, finalBlockB) :=
        if remaining < 112 then (state, finalBlockA)
        else
          (Impl.compress state (Impl.toU64s finalBlockA),
           Vector.ofFn (fun _ : Fin 128 => (0 : UInt8)))
      let finalBlockC : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
        if i.val < 112 then finalBlockB[i]
        else if i.val < 120 then 0
        else ((totalBits >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
      Impl.compress state (Impl.toU64s finalBlockC) := by
  unfold Impl.sha512State
  simp only [SHS.Equiv.SHA512.ToU64s.toU64sFromBytes_eq_toU64s]

theorem impl_sha512State_eq_refactored (data : ByteArray) (H0 : Impl.State) :
    Impl.sha512State data H0 = implSha512StateRefactored data H0 := by
  rw [impl_sha512State_eq_extract _ H0]
  unfold implSha512StateRefactored
  rw [implPaddedBlocks_foldl]
  by_cases h : data.size % 128 < 112
  · rw [totalBlocks_lt112 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 128)
        (fun (state : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress state (Impl.toU64s
            (Vector.ofFn fun j : Fin 128 => data.get! (i.val * 128 + j.val))))
        H0
        =
      Fin.foldl (data.size / 128)
        (fun (s : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress s (Impl.toU64s (paddedBlock data i.castSucc.val)))
        H0 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.val = i.val from rfl, ← this]
    have hBlockEq :
      (Vector.ofFn fun i : Fin 128 =>
        if i.val < 112 then
          (Vector.ofFn fun i : Fin 128 =>
            if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
            else if i.val = data.size % 128 then (0x80 : UInt8)
            else 0)[i]
        else if i.val < 120 then 0
        else (data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 128)).val := by
      show _ = paddedBlock data (data.size / 128)
      rw [paddedBlock_final_lt112 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · simp [hi112]
      · simp [hi112]
    rw [hFoldEq, hBlockEq]
  · rw [totalBlocks_ge112 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    conv_rhs => rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 128)
        (fun (state : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress state (Impl.toU64s
            (Vector.ofFn fun j : Fin 128 => data.get! (i.val * 128 + j.val))))
        H0
        =
      Fin.foldl (data.size / 128)
        (fun (s : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress s (Impl.toU64s (paddedBlock data i.castSucc.castSucc.val)))
        H0 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.castSucc.val = i.val from rfl, ← this]
    have hBlockA :
      (Vector.ofFn fun i : Fin 128 =>
          if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
          else if i.val = data.size % 128 then (0x80 : UInt8)
          else 0)
        = paddedBlock data (Fin.last (data.size / 128)).castSucc.val := by
      show _ = paddedBlock data (data.size / 128)
      rw [paddedBlock_finalA_ge112 data h]
    have hBlockB :
      (Vector.ofFn fun i : Fin 128 =>
          if i.val < 112 then (Vector.ofFn (fun _ : Fin 128 => (0 : UInt8)))[i]
          else if i.val < 120 then 0
          else (data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 128 + 1)).val := by
      show _ = paddedBlock data (data.size / 128 + 1)
      rw [paddedBlock_finalB_ge112 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · have hi120 : i < 120 := by omega
        simp [hi112, hi120]
      · simp [hi112]
    rw [hFoldEq, hBlockA, hBlockB]

theorem impl_sha512_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512 data =
      let final := implSha512Refactored data
      Vector.ofFn fun i : Fin 64 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 64 => _) = _
  unfold implSha512Refactored
  rw [impl_sha512State_eq_refactored]

/-! ## SHA-384 and SHA-512/256 refactor

Same core: `Impl.sha512State data H0` for the IV and the appropriately
truncated digest emission. -/

def implSha384Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_384

theorem impl_sha384_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha384 data =
      let final := implSha384Refactored data
      Vector.ofFn fun i : Fin 48 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha384
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 48 => _) = _
  unfold implSha384Refactored
  rw [impl_sha512State_eq_refactored]

def implSha512_256Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512_256

theorem impl_sha512_256_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512_256 data =
      let final := implSha512_256Refactored data
      Vector.ofFn fun i : Fin 32 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512_256
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 32 => _) = _
  unfold implSha512_256Refactored
  rw [impl_sha512State_eq_refactored]

def implSha512_224Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512_224

theorem impl_sha512_224_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512_224 data =
      let final := implSha512_224Refactored data
      Vector.ofFn fun i : Fin 28 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512_224
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 28 => _) = _
  unfold implSha512_224Refactored
  rw [impl_sha512State_eq_refactored]

end SHS.Equiv.SHA512.Padding.Equiv
