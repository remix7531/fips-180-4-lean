import equiv.SHA256.Padding.Layout
import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.Padding.Parsing
import equiv.SHA256.Digest
import equiv.Common.ArrayFold

/-! # SHA-256 padding: streaming refactor of `Impl.sha256`

The headline equivalence between the implementation's imperative
streaming `Impl.sha256` and a clean block-list re-statement
(`implSha256Refactored`) that mirrors the spec's shape.  Both compute
the same digest by `rfl` after a final fold-peeling case-split on
`data.size % 64 < 56`.

The byte→bit decoding lemmas live in `Padding/ByteDecoding`; the
byte-level / bit-level parse bridge lives in `Padding/Parsing`. This
file only handles the streaming-vs-block-list refactor of the impl. -/

open SHS.Equiv.ArrayFold
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Digest
open SHS.Equiv.SHA256.Padding.Layout

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Equiv

open scoped SHS.SHA256

/-- A clean, block-list re-statement of `Impl.sha256` that mirrors the
spec: compress all `implPaddedBlocks data` from `H256_256`, then emit
big-endian state bytes. -/
def implSha256Refactored (data : ByteArray) : Vector UInt8 32 :=
  let blocks := implPaddedBlocks data
  let state := blocks.foldl (fun s b => Impl.compress s (Impl.toU32s b)) Impl.H256_256
  extractDigest state

/-- Definitional unfolding of `implSha256Refactored` as a chain step. -/
theorem implSha256Refactored_eq_extractDigest (data : ByteArray) :
    implSha256Refactored data =
      extractDigest ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU32s b)) Impl.H256_256) := rfl

private theorem impl_sha256_eq_extract (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha256 data = extractDigest (
      let blocks := data.size / 64
      let remaining := data.size % 64
      let totalBits : UInt64 := data.size.toUInt64 <<< 3
      let state : Impl.State := Fin.foldl blocks (fun state (i : Fin blocks) =>
        let block : Vector UInt8 64 := Vector.ofFn fun j : Fin 64 =>
          data.get! (i.val * 64 + j.val)
        Impl.compress state (Impl.toU32s block)) Impl.H256_256
      let finalBlockA : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
        if i.val < remaining then data.get! (blocks * 64 + i.val)
        else if i.val = remaining then 0x80
        else 0
      let (state, finalBlockB) :=
        if remaining < 56 then (state, finalBlockA)
        else
          (Impl.compress state (Impl.toU32s finalBlockA),
           Vector.ofFn (fun _ : Fin 64 => (0 : UInt8)))
      let finalBlockC : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
        if i.val < 56 then finalBlockB[i]
        else ((totalBits >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
      Impl.compress state (Impl.toU32s finalBlockC)) := by
  unfold Impl.sha256
  rw [if_neg (Nat.not_le.mpr hsize)]
  rfl

/-- `Impl.sha256` agrees with the cleaner block-list refactoring.
The `< 56` / `≥ 56` case-split mirrors `Impl.sha256`'s own conditional
emission of one vs two final blocks.  The `data.size < 2 ^ 61`
hypothesis discharges the runtime size guard at the top of `Impl.sha256`
(see FIPS 180-4 §5.1.1). -/
theorem impl_sha256_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha256 data = implSha256Refactored data := by
  rw [impl_sha256_eq_extract _ hsize]
  show _ = extractDigest _
  apply congrArg extractDigest
  rw [implPaddedBlocks_foldl]
  by_cases h : data.size % 64 < 56
  · rw [totalBlocks_lt56 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 64)
        (fun (state : Impl.State) (i : Fin (data.size / 64)) =>
          Impl.compress state (Impl.toU32s
            (Vector.ofFn fun j : Fin 64 => data.get! (i.val * 64 + j.val))))
        Impl.H256_256
        =
      Fin.foldl (data.size / 64)
        (fun (s : Impl.State) (i : Fin (data.size / 64)) =>
          Impl.compress s (Impl.toU32s (paddedBlock data i.castSucc.val)))
        Impl.H256_256 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.val = i.val from rfl, ← this]
    have hBlockEq :
      (Vector.ofFn fun i : Fin 64 =>
        if i.val < 56 then
          (Vector.ofFn fun i : Fin 64 =>
            if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
            else if i.val = data.size % 64 then (0x80 : UInt8)
            else 0)[i]
        else (data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 64)).val := by
      show _ = paddedBlock data (data.size / 64)
      rw [paddedBlock_final_lt56 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi56 : i < 56
      · simp [hi56]
      · simp [hi56]
    rw [hFoldEq, hBlockEq]
  · rw [totalBlocks_ge56 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    conv_rhs => rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 64)
        (fun (state : Impl.State) (i : Fin (data.size / 64)) =>
          Impl.compress state (Impl.toU32s
            (Vector.ofFn fun j : Fin 64 => data.get! (i.val * 64 + j.val))))
        Impl.H256_256
        =
      Fin.foldl (data.size / 64)
        (fun (s : Impl.State) (i : Fin (data.size / 64)) =>
          Impl.compress s (Impl.toU32s (paddedBlock data i.castSucc.castSucc.val)))
        Impl.H256_256 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.castSucc.val = i.val from rfl, ← this]
    have hBlockA :
      (Vector.ofFn fun i : Fin 64 =>
          if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
          else if i.val = data.size % 64 then (0x80 : UInt8)
          else 0)
        = paddedBlock data (Fin.last (data.size / 64)).castSucc.val := by
      show _ = paddedBlock data (data.size / 64)
      rw [paddedBlock_finalA_ge56 data h]
    have hBlockB :
      (Vector.ofFn fun i : Fin 64 =>
          if i.val < 56 then (Vector.ofFn (fun _ : Fin 64 => (0 : UInt8)))[i]
          else (data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 64 + 1)).val := by
      show _ = paddedBlock data (data.size / 64 + 1)
      rw [paddedBlock_finalB_ge56 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi56 : i < 56
      · simp [hi56]
      · simp [hi56]
    rw [hFoldEq, hBlockA, hBlockB]

end SHS.Equiv.SHA256.Padding.Equiv
