import equiv.SHA512.Compress.Fused
import equiv.SHA512.Foldl.Fused

/-! # SHA-512 block compression correctness -/

open SHS.SHA512
open scoped SHS.SHA512
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Lift

namespace SHS.Equiv.SHA512

/-- `Impl.compress` agrees with the spec's per-block `SHS.SHA512.compress`
once both inputs are viewed in the spec's `BitVec 64` representation. -/
theorem compress_correct (state : Impl.State) (block : Impl.Block) :
    toSpecState (Impl.compress state block) =
      SHS.SHA512.compress (toSpecState state) (toSpecBlock block) := by
  rw [Compress.Fused.toSpecState_compress, ← spec_compress_eq_fused]

end SHS.Equiv.SHA512
