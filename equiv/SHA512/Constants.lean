import impl.SHA512
import spec.Functions

/-! # SHA-512 round constants -/

open SHS.SHA512

namespace SHS.Equiv.SHA512.Constants

private theorem constants_eq : Impl.K64.map UInt64.toBitVec = SHS.SHA512.K := by
  rw [← Vector.toList_inj, Vector.toList_map]
  rfl

/-- The round-constant lookup commutes with `toBitVec`. -/
theorem K64_toBitVec_bang (round : Nat) :
    (Impl.K64[round]!).toBitVec = SHS.SHA512.K[round]! := by
  rw [← constants_eq]
  simp only [getElem!_def, Vector.getElem?_map]
  cases Impl.K64[round]? <;> rfl

end SHS.Equiv.SHA512.Constants
