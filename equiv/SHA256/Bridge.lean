import impl.SHA256
import spec.HashAlgorithms

/-!
# `UInt32` ↔ `BitVec 32` operator bridge

The intermediate implementation (`impl/Sha256.lean`) operates over
`UInt32`; the NIST-style spec (`spec/`) operates over `BitVec 32`.
`UInt32` is a one-field structure wrapping `BitVec 32`, so all bitwise
operations are *definitionally* equal to their `BitVec 32` counterparts
modulo the projection `UInt32.toBitVec`.

This module collects those bridge lemmas and tags them `@[simp]` where
appropriate, so that downstream proofs (`Functions.lean`, `Compress.lean`)
can reduce mixed `UInt32`/`BitVec 32` expressions by `simp` alone.

## Contents

* `toBitVec_{xor,and,not,add}` — pointwise `rfl` bridges (always defeq).
* `toBitVec_shr_of_lt` — shift bridge (needs `n.toNat < 32` because of
  the implicit `% 32` baked into `UInt32.>>>`).
* `toBitVec_rotr` / `ROTR_eq_rotateRight` / `ROTR_eq_u32_rotr` —
  rotation bridges, in three flavors used at different proof sites.
* `SHR_eq_shr` — spec `SHR n` is just `>>> n` on `BitVec`.

## Operator-notation map (spec ↔ equiv/impl)

The spec/ layer uses the mathematical Unicode operators on `BitVec 32`
(matching FIPS 180-4 notation):

  spec    ⊕   ∧   ¬     (xor, and, not on `BitVec`)

The equiv/ layer (and the underlying impl/) instead uses the ASCII
bitwise operators on `UInt32`, which is what the Lean core provides for
machine-word types:

  equiv  ^^^  &&&  ~~~

Both denote the same bit operations; the `toBitVec_{xor,and,not}`
lemmas in this file (and the `_toBitVec` family in `Functions.lean`)
are the bridges that line them up. -/

open SHS.SHA256

namespace SHS.Equiv.SHA256.Bridge

open SHS

/-! ## Pointwise bitwise / arithmetic bridges

All four are `rfl` because `UInt32` is a one-field structure over
`BitVec 32` and the corresponding instances forward through that field. -/

@[simp] theorem toBitVec_xor (x y : UInt32) :
    (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl

@[simp] theorem toBitVec_and (x y : UInt32) :
    (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := rfl

@[simp] theorem toBitVec_not (x : UInt32) :
    (~~~ x).toBitVec = ~~~ x.toBitVec := rfl

@[simp] theorem toBitVec_add (x y : UInt32) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

/-! ## Shift bridge

`UInt32.>>>` carries an implicit `% 32` on the shift amount (because the
amount is itself a `UInt32`), so the bridge to `BitVec.>>>` requires
proving the amount is in range. -/

/-- For an in-range shift amount, `UInt32.>>>` agrees with `BitVec.>>>`
on the underlying bitvector. -/
theorem toBitVec_shr_of_lt (x : UInt32) (n : UInt32) (h : n.toNat < 32) :
    (x >>> n).toBitVec = x.toBitVec >>> n.toNat := by
  rw [UInt32.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  congr 1
  simp [Nat.mod_eq_of_lt h]

/-! ## Rotation bridges

The spec defines `ROTR n` recursively via `BitVec.rotateRightAux`; for
`n < 32` it coincides with `BitVec.rotateRight`, which in turn matches
`Impl.UInt32.rotr` definitionally. -/

/-- Definitional bridge: `Impl.UInt32.rotr` is `BitVec.rotateRight` on
the underlying bitvector. -/
@[simp] theorem toBitVec_rotr (x : UInt32) (n : UInt32) :
    (Impl.UInt32.rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := rfl

/-- For `n < 32`, the spec's `SHS.ROTR n` matches `BitVec.rotateRight n`. -/
theorem ROTR_eq_rotateRight (n : Nat) (x : BitVec 32) (h : n < 32) :
    SHS.ROTR n x = x.rotateRight n := by
  unfold SHS.ROTR
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  unfold BitVec.rotateRightAux
  rfl

/-- End-to-end bridge: spec `ROTR n.toNat` on a lifted `UInt32` equals
the lifted impl `Impl.UInt32.rotr x n`.  This is the form needed by the
`bigSigma`/`smallSigma` bridge proofs. -/
theorem ROTR_eq_u32_rotr (n : UInt32) (x : UInt32) (h : n.toNat < 32) :
    SHS.ROTR n.toNat x.toBitVec = (Impl.UInt32.rotr x n).toBitVec := by
  rw [toBitVec_rotr, ROTR_eq_rotateRight _ _ h]

/-! ## SHR bridge -/

/-- The spec's `SHR n` is `BitVec`'s `>>> n` on the nose. -/
theorem SHR_eq_shr (n : Nat) (x : BitVec 32) :
    SHS.SHR n x = x >>> n := rfl

end SHS.Equiv.SHA256.Bridge
