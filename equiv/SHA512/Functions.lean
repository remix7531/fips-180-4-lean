import equiv.SHA512.Bridge
import spec.Functions

/-!
# Bridge lemmas for the SHA-512 round functions

Parallel to `equiv/SHA256/Functions.lean` at 64-bit width with the
SHA-512 rotation constants (FIPS 180-4 §4.1.3):

* `Σ₀` rotates by 28, 34, 39
* `Σ₁` rotates by 14, 18, 41
* `σ₀` rotates by 1, 8; shifts right by 7
* `σ₁` rotates by 19, 61; shifts right by 6

`Ch` and `Maj` are width-agnostic and follow the SHA-256 shape.

For each spec function we prove a `@[simp]` lemma rewriting a call on
*lifted* `UInt64` arguments to the lifting of the implementation's
expression. Together with the operator bridges from `Bridge.lean`,
these lemmas align the round operations in `Compress/Impl.lean` and
`Compress/Fused.lean`.

Proof shape (for all six lemmas): unfold the spec definition, then
`simp only` with the operator bridges from `Bridge.lean` to push
`toBitVec` to the leaves; what remains closes by `ac_rfl`. -/

open SHS.Equiv.SHA512.Bridge

open SHS.SHA512

namespace SHS.Equiv.SHA512.Functions

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)`, lifted. (FIPS 180-4 §4.1.3, eq. 4.8) -/
@[simp] theorem Ch_toBitVec (x y z : UInt64) :
    SHS.SHA512.Ch x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ ((~~~ x) &&& z)).toBitVec := by
  simp [SHS.SHA512.Ch]

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, lifted. (FIPS 180-4 §4.1.3, eq. 4.9) -/
@[simp] theorem Maj_toBitVec (x y z : UInt64) :
    SHS.SHA512.Maj x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)).toBitVec := by
  simp only [SHS.SHA512.Maj, UInt64.toBitVec_xor, UInt64.toBitVec_and]
  ac_rfl

/-- `Σ₀ x = ROTR²⁸ x ⊕ ROTR³⁴ x ⊕ ROTR³⁹ x`, lifted. (eq. 4.10) -/
@[simp] theorem bigSigma0_toBitVec (x : UInt64) :
    SHS.SHA512.bigSigma0 x.toBitVec =
      ((Impl.UInt64.rotr x 28) ^^^ (Impl.UInt64.rotr x 34)
        ^^^ (Impl.UInt64.rotr x 39)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA512.bigSigma0, UInt64.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, UInt64.reduceToNat]
  ac_rfl

/-- `Σ₁ x = ROTR¹⁴ x ⊕ ROTR¹⁸ x ⊕ ROTR⁴¹ x`, lifted. (eq. 4.11) -/
@[simp] theorem bigSigma1_toBitVec (x : UInt64) :
    SHS.SHA512.bigSigma1 x.toBitVec =
      ((Impl.UInt64.rotr x 14) ^^^ (Impl.UInt64.rotr x 18)
        ^^^ (Impl.UInt64.rotr x 41)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA512.bigSigma1, UInt64.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, UInt64.reduceToNat]
  ac_rfl

/-- `σ₀ x = ROTR¹ x ⊕ ROTR⁸ x ⊕ SHR⁷ x`, lifted. (eq. 4.12) -/
@[simp] theorem smallSigma0_toBitVec (x : UInt64) :
    SHS.SHA512.smallSigma0 x.toBitVec =
      ((Impl.UInt64.rotr x 1) ^^^ (Impl.UInt64.rotr x 8) ^^^ (x >>> 7)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA512.smallSigma0, UInt64.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, toBitVec_shr_of_lt, SHR_eq_shr,
    UInt64.reduceToNat]
  ac_rfl

/-- `σ₁ x = ROTR¹⁹ x ⊕ ROTR⁶¹ x ⊕ SHR⁶ x`, lifted. (eq. 4.13) -/
@[simp] theorem smallSigma1_toBitVec (x : UInt64) :
    SHS.SHA512.smallSigma1 x.toBitVec =
      ((Impl.UInt64.rotr x 19) ^^^ (Impl.UInt64.rotr x 61) ^^^ (x >>> 6)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA512.smallSigma1, UInt64.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, toBitVec_shr_of_lt, SHR_eq_shr,
    UInt64.reduceToNat]
  ac_rfl

end SHS.Equiv.SHA512.Functions
