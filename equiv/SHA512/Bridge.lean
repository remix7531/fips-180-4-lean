import impl.SHA512
import spec.Notation

/-!
# `UInt64` ↔ `BitVec 64` operator bridge

This module relates the SHA-512 implementation's shifts and rotations on
`UInt64` to the spec's `BitVec 64` operations. Lean core provides the
pointwise bitwise and arithmetic bridges through `UInt64.toBitVec`.

## Operator-notation map (spec ↔ equiv/impl)

The spec/ layer uses the mathematical Unicode operators on `BitVec 64`
(matching FIPS 180-4 notation):

  spec    ⊕   ∧   ¬     (xor, and, not on `BitVec`)

The equiv/ layer (and the underlying impl/) instead uses the ASCII
bitwise operators on `UInt64`, which is what the Lean core provides for
machine-word types:

  equiv  ^^^  &&&  ~~~
-/

open SHS.SHA512

namespace SHS.Equiv.SHA512.Bridge

open SHS

/-! ## Shift bridges

`UInt64.>>>` and `UInt64.<<<` carry an implicit `% 64` on the shift
amount (because the amount is itself a `UInt64`), so each bridge to
`BitVec.>>>` / `BitVec.<<<` requires proving the amount is in range. -/

/-- For an in-range shift amount, `UInt64.>>>` agrees with `BitVec.>>>`
on the underlying bitvector. -/
theorem toBitVec_shr_of_lt (x : UInt64) (n : UInt64) (h : n.toNat < 64) :
    (x >>> n).toBitVec = x.toBitVec >>> n.toNat := by
  rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  simp [Nat.mod_eq_of_lt h]

/-- For an in-range shift amount, `UInt64.<<<` agrees with `BitVec.<<<`
on the underlying bitvector.  Companion to `toBitVec_shr_of_lt`. -/
theorem toBitVec_shl_of_lt (x : UInt64) (n : UInt64) (h : n.toNat < 64) :
    (x <<< n).toBitVec = x.toBitVec <<< n.toNat := by
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]
  simp [Nat.mod_eq_of_lt h]

/-! ## Rotation bridges

The rotation proof uses `BitVec.rotateRight_def`. Both shift amounts must
be in range to remove the implicit reduction modulo 64. -/

/-- A positive rotation below 64 agrees with `BitVec.rotateRight`. -/
theorem toBitVec_rotr (x : UInt64) (n : UInt64) (h0 : 0 < n.toNat) (h : n.toNat < 64) :
    (Impl.UInt64.rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  unfold Impl.UInt64.rotr
  have hn_le : n ≤ (64 : UInt64) := by
    rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt h
  have h64n : ((64 : UInt64) - n).toNat = 64 - n.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hn_le]; rfl
  have h64n_lt : ((64 : UInt64) - n).toNat < 64 := by rw [h64n]; omega
  rw [UInt64.toBitVec_or, toBitVec_shr_of_lt _ _ h, toBitVec_shl_of_lt _ _ h64n_lt,
      h64n, BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- For `n < 64`, the spec's `SHS.ROTR n` matches `BitVec.rotateRight n`. -/
theorem ROTR_eq_rotateRight (n : Nat) (x : BitVec 64) (h : n < 64) :
    SHS.ROTR n x = x.rotateRight n := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  rfl

/-! ## SHR bridge -/

theorem SHR_eq_shr (n : Nat) (x : BitVec 64) :
    SHS.SHR n x = x >>> n := rfl

end SHS.Equiv.SHA512.Bridge
