import equiv.SHA512.Padding.Layout
import equiv.SHA512.ToU64s

/-! # SHA-512 streaming padding

The complete input blocks are identical in the streaming and padded-array views.
The final one or two blocks use the byte layout laws for the padding cutoff. -/

open SHS.Equiv.SHA512.Padding.Layout
open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Equiv

open scoped SHS.SHA512

/-- Fold the implementation's compression function over the padded blocks. -/
def implSha512StateRefactored (data : ByteArray) (H0 : Impl.State) : Impl.State :=
  (implPaddedBlocks data).foldl (fun s b => Impl.compress s (Impl.toU64s b)) H0

/-- IV-generic refactor: `Impl.sha512State` (the shared SHA-2-512 core)
equals folding `Impl.compress` over `implPaddedBlocks data` from `H0`.
The `< 112` / `≥ 112` case-split mirrors `sha512State`'s own
conditional emission of one vs two final blocks. -/
theorem impl_sha512State_eq_refactored (data : ByteArray) (H0 : Impl.State) :
    Impl.sha512State data H0 = implSha512StateRefactored data H0 := by
  unfold Impl.sha512State implSha512StateRefactored
  rw [implPaddedBlocks_foldl]
  have completeBlocks :
      Fin.foldl (data.size / 128)
        (fun state i => Impl.compress state (Impl.toU64sFromBytes data (i.val * 128))) H0 =
      Fin.foldl (data.size / 128)
        (fun state i => Impl.compress state (Impl.toU64s (paddedBlock data i.val))) H0 := by
    refine congrArg (fun step => Fin.foldl (data.size / 128) step H0) ?_
    funext state i
    rw [paddedBlock_complete data i.val i.isLt, ToU64s.toU64sFromBytes_eq_toU64s]
  by_cases beforeCutoff : data.size % 128 < 112
  · rw [totalBlocks_lt112 _ beforeCutoff]
    simp only [beforeCutoff, ↓reduceIte, Fin.foldl_succ_last, Fin.val_castSucc,
      Fin.val_last, completeBlocks, paddedBlock_final_lt112 _ beforeCutoff]
    refine congrArg (fun block => Impl.compress _ (Impl.toU64s block)) ?_
    ext index bound
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  · rw [totalBlocks_ge112 _ beforeCutoff]
    simp only [beforeCutoff, ↓reduceIte, Fin.foldl_succ_last, Fin.val_castSucc,
      Fin.val_last, completeBlocks, paddedBlock_finalA_ge112 _ beforeCutoff,
      paddedBlock_finalB_ge112 _ beforeCutoff]
    refine congrArg (fun block => Impl.compress _ (Impl.toU64s block)) ?_
    ext index bound
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    by_cases beforeTag : index < 112
    · simp [beforeTag, show index < 120 by omega]
    · simp [beforeTag]

end SHS.Equiv.SHA512.Padding.Equiv
