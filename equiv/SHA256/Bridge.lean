import impl.SHA256
import spec.Notation

/-!
# `UInt32` ↔ `BitVec 32` operator bridge

This module relates the SHA-256 implementation's shifts and rotations on
`UInt32` to the spec's `BitVec 32` operations. Lean core provides the
pointwise bitwise and arithmetic bridges through `UInt32.toBitVec`.

## Contents

* `toBitVec_shr_of_lt` — shift bridge (needs `n.toNat < 32` because of
  the implicit `% 32` baked into `UInt32.>>>`).
* `toBitVec_rotr` / `ROTR_eq_rotateRight` — rotation bridges; the
  bigSigma/smallSigma proofs in `Functions.lean` chain them.
* `SHR_eq_shr` — spec `SHR n` is just `>>> n` on `BitVec`.

## Operator-notation map (spec ↔ equiv/impl)

The spec/ layer uses the mathematical Unicode operators on `BitVec 32`
(matching FIPS 180-4 notation):

  spec    ⊕   ∧   ¬     (xor, and, not on `BitVec`)

The equiv/ layer (and the underlying impl/) instead uses the ASCII
bitwise operators on `UInt32`, which is what the Lean core provides for
machine-word types:

  equiv  ^^^  &&&  ~~~
-/

open SHS.SHA256

namespace SHS.Equiv.SHA256.Bridge

open SHS

/-! ## Shift bridge

`UInt32.>>>` carries an implicit `% 32` on the shift amount (because the
amount is itself a `UInt32`), so the bridge to `BitVec.>>>` requires
proving the amount is in range. -/

/-- For an in-range shift amount, `UInt32.>>>` agrees with `BitVec.>>>`
on the underlying bitvector. -/
theorem toBitVec_shr_of_lt (x : UInt32) (n : UInt32) (h : n.toNat < 32) :
    (x >>> n).toBitVec = x.toBitVec >>> n.toNat := by
  rw [UInt32.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  simp [Nat.mod_eq_of_lt h]

/-! ## Shift-left bridge

Companion to `toBitVec_shr_of_lt`: needed because the new fast `rotr`
implementation uses `<<<` and `>>>` directly. -/

/-- For an in-range shift amount, `UInt32.<<<` agrees with `BitVec.<<<`
on the underlying bitvector. -/
theorem toBitVec_shl_of_lt (x : UInt32) (n : UInt32) (h : n.toNat < 32) :
    (x <<< n).toBitVec = x.toBitVec <<< n.toNat := by
  rw [UInt32.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]
  simp [Nat.mod_eq_of_lt h]

/-! ## Rotation bridges

The rotation proof uses `BitVec.rotateRight_def`. Both shift amounts must
be in range to remove the implicit reduction modulo 32. -/

/-- A positive rotation below 32 agrees with `BitVec.rotateRight`. -/
theorem toBitVec_rotr (x : UInt32) (n : UInt32) (h0 : 0 < n.toNat) (h : n.toNat < 32) :
    (Impl.UInt32.rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  unfold Impl.UInt32.rotr
  have hn_le : n ≤ (32 : UInt32) := by
    rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt h
  have h32n : ((32 : UInt32) - n).toNat = 32 - n.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ hn_le]; rfl
  have h32n_lt : ((32 : UInt32) - n).toNat < 32 := by rw [h32n]; omega
  rw [UInt32.toBitVec_or, toBitVec_shr_of_lt _ _ h, toBitVec_shl_of_lt _ _ h32n_lt,
      h32n, BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- For `n < 32`, the spec's `SHS.ROTR n` matches `BitVec.rotateRight n`. -/
theorem ROTR_eq_rotateRight (n : Nat) (x : BitVec 32) (h : n < 32) :
    SHS.ROTR n x = x.rotateRight n := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  rfl

/-! ## SHR bridge -/

/-- The spec's `SHR n` is `BitVec`'s `>>> n` on the nose. -/
theorem SHR_eq_shr (n : Nat) (x : BitVec 32) :
    SHS.SHR n x = x >>> n := rfl

end SHS.Equiv.SHA256.Bridge
