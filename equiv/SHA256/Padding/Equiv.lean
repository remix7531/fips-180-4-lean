import equiv.SHA256.Padding.Layout
import equiv.SHA256.ToU32s

/-! # SHA-256 streaming padding

The complete input blocks are identical in the streaming and padded-array views.
The final one or two blocks use the byte layout laws for the padding cutoff. -/

open SHS.Equiv.SHA256.Padding.Layout
open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Equiv

open scoped SHS.SHA256

/-- Fold the implementation's compression function over the padded blocks. -/
def implSha256StateRefactored (data : ByteArray) (H0 : Impl.State) : Impl.State :=
  (implPaddedBlocks data).foldl (fun s b => Impl.compress s (Impl.toU32s b)) H0

/-- IV-generic refactor: `Impl.sha256State` (the shared SHA-2-256 core)
equals folding `Impl.compress` over `implPaddedBlocks data` from `H0`.
The `< 56` / `≥ 56` case-split mirrors `sha256State`'s own conditional
emission of one vs two final blocks. -/
theorem impl_sha256State_eq_refactored (data : ByteArray) (H0 : Impl.State) :
    Impl.sha256State data H0 = implSha256StateRefactored data H0 := by
  unfold Impl.sha256State implSha256StateRefactored
  rw [implPaddedBlocks_foldl]
  have completeBlocks :
      Fin.foldl (data.size / 64)
        (fun state i => Impl.compress state (Impl.toU32sFromBytes data (i.val * 64))) H0 =
      Fin.foldl (data.size / 64)
        (fun state i => Impl.compress state (Impl.toU32s (paddedBlock data i.val))) H0 := by
    refine congrArg (fun step => Fin.foldl (data.size / 64) step H0) ?_
    funext state i
    rw [paddedBlock_complete data i.val i.isLt, ToU32s.toU32sFromBytes_eq_toU32s]
  by_cases beforeCutoff : data.size % 64 < 56
  · rw [totalBlocks_lt56 _ beforeCutoff]
    simp only [beforeCutoff, ↓reduceIte, Fin.foldl_succ_last, Fin.val_castSucc,
      Fin.val_last, completeBlocks, paddedBlock_final_lt56 _ beforeCutoff]
    refine congrArg (fun block => Impl.compress _ (Impl.toU32s block)) ?_
    ext index bound
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  · rw [totalBlocks_ge56 _ beforeCutoff]
    simp only [beforeCutoff, ↓reduceIte, Fin.foldl_succ_last, Fin.val_castSucc,
      Fin.val_last, completeBlocks, paddedBlock_finalA_ge56 _ beforeCutoff,
      paddedBlock_finalB_ge56 _ beforeCutoff]
    refine congrArg (fun block => Impl.compress _ (Impl.toU32s block)) ?_
    ext index bound
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]

end SHS.Equiv.SHA256.Padding.Equiv
