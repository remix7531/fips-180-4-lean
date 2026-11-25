import equiv.SHA256.Bridge
import spec.Functions

/-!
# Bridge lemmas for the SHA-256 round functions

The spec (`spec/Functions.lean`) defines six auxiliary functions on
`BitVec 32` — `Ch`, `Maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`,
`smallSigma1` — that the compression function calls each round.  The
implementation inlines the same operations, but on `UInt32`.

For each spec function we prove a `@[simp]` lemma rewriting a call on
*lifted* `UInt32` arguments to the lifting of the implementation's
expression.  Together with the operator bridges from `Bridge.lean`,
this lets the round-body equivalence in `Compress.lean` reduce to
`simp`.

Core lemmas commute bitwise operations with `toBitVec`. In the sigma
proofs, `decide` discharges the bounds for the literal rotation and shift
amounts.
-/

open SHS.Equiv.SHA256.Bridge

open SHS.SHA256

namespace SHS.Equiv.SHA256.Functions

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)`, lifted. (FIPS 180-4 §4.1.2, eq. 4.2) -/
@[simp] theorem Ch_toBitVec (x y z : UInt32) :
    SHS.SHA256.Ch x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ ((~~~ x) &&& z)).toBitVec := by
  simp [SHS.SHA256.Ch]

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, lifted. (FIPS 180-4 §4.1.2, eq. 4.3) -/
@[simp] theorem Maj_toBitVec (x y z : UInt32) :
    SHS.SHA256.Maj x.toBitVec y.toBitVec z.toBitVec =
      ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)).toBitVec := by
  simp only [SHS.SHA256.Maj, UInt32.toBitVec_xor, UInt32.toBitVec_and]
  ac_rfl

/-- `Σ₀ x = ROTR² x ⊕ ROTR¹³ x ⊕ ROTR²² x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.4) -/
@[simp] theorem bigSigma0_toBitVec (x : UInt32) :
    SHS.SHA256.bigSigma0 x.toBitVec =
      ((Impl.UInt32.rotr x 2) ^^^ (Impl.UInt32.rotr x 13)
        ^^^ (Impl.UInt32.rotr x 22)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA256.bigSigma0, UInt32.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, UInt32.reduceToNat]
  ac_rfl

/-- `Σ₁ x = ROTR⁶ x ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.5) -/
@[simp] theorem bigSigma1_toBitVec (x : UInt32) :
    SHS.SHA256.bigSigma1 x.toBitVec =
      ((Impl.UInt32.rotr x 6) ^^^ (Impl.UInt32.rotr x 11)
        ^^^ (Impl.UInt32.rotr x 25)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA256.bigSigma1, UInt32.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, UInt32.reduceToNat]
  ac_rfl

/-- `σ₀ x = ROTR⁷ x ⊕ ROTR¹⁸ x ⊕ SHR³ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.6) -/
@[simp] theorem smallSigma0_toBitVec (x : UInt32) :
    SHS.SHA256.smallSigma0 x.toBitVec =
      ((Impl.UInt32.rotr x 7) ^^^ (Impl.UInt32.rotr x 18) ^^^ (x >>> 3)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA256.smallSigma0, UInt32.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, toBitVec_shr_of_lt, SHR_eq_shr,
    UInt32.reduceToNat]
  ac_rfl

/-- `σ₁ x = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x`, lifted. (FIPS 180-4 §4.1.2, eq. 4.7) -/
@[simp] theorem smallSigma1_toBitVec (x : UInt32) :
    SHS.SHA256.smallSigma1 x.toBitVec =
      ((Impl.UInt32.rotr x 17) ^^^ (Impl.UInt32.rotr x 19) ^^^ (x >>> 10)).toBitVec := by
  simp (discharger := decide) only [SHS.SHA256.smallSigma1, UInt32.toBitVec_xor,
    toBitVec_rotr, ROTR_eq_rotateRight, toBitVec_shr_of_lt, SHR_eq_shr,
    UInt32.reduceToNat]
  ac_rfl

end SHS.Equiv.SHA256.Functions
