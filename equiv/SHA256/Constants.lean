import impl.SHA256
import spec.Functions

/-! # SHA-256 round constants -/

open SHS.SHA256

namespace SHS.Equiv.SHA256.Constants

private theorem constants_eq : Impl.K32.map UInt32.toBitVec = SHS.SHA256.K := by
  rw [← Vector.toList_inj, Vector.toList_map]
  rfl

/-- The round-constant lookup commutes with `toBitVec`. -/
theorem K32_toBitVec_bang (round : Nat) :
    (Impl.K32[round]!).toBitVec = SHS.SHA256.K[round]! := by
  rw [← constants_eq]
  simp only [getElem!_def, Vector.getElem?_map]
  cases Impl.K32[round]? <;> rfl

end SHS.Equiv.SHA256.Constants
