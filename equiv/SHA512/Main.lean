import equiv.SHA512.Pipeline
import equiv.SHA512.Digest
import spec.SHA512tHash

/-! # SHA-512 hash correctness

Each digest proof specializes final-state equivalence to its initial
hash value, then applies the relevant digest emission theorem. -/

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Digest
open SHS.Equiv.SHA512.Padding.ByteDecoding
open SHS.Equiv.SHA512.Pipeline

open SHS.SHA512

namespace SHS.Equiv.SHA512

open scoped SHS.SHA512

/-- `Impl.sha512` agrees with the spec's bitwise `sha512`, viewing the
64-byte digest as a 512-bit big-endian BitVec. -/
theorem sha512_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512 (Impl.sha512 data) =
      SHS.SHA512.sha512 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha512
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec512 (extractDigest512 (Impl.sha512State data Impl.H0_512)) = _
  rw [digestBitVec512_extract,
    sha512State_correct data h, toSpecState_H0_512]
  simp (discharger := decide) only [SHS.SHA512.sha512, getElem!_pos]

/-! ## SHA-384 and SHA-512/256 -/

/-- `Impl.sha384` agrees with the spec's `sha384`, viewing the 48-byte
digest as a 384-bit big-endian BitVec. -/
theorem sha384_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec384 (Impl.sha384 data) =
      SHS.SHA512.sha384 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha384
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec384 (extractDigest384 (Impl.sha512State data Impl.H0_384)) = _
  rw [digestBitVec384_extract,
    sha512State_correct data h, toSpecState_H0_384]
  simp (discharger := decide) only [SHS.SHA512.sha384, getElem!_pos]

/-- `Impl.sha512_256` agrees with the spec's `sha512_256`. -/
theorem sha512_256_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512_256 (Impl.sha512_256 data) =
      SHS.SHA512.sha512_256 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha512_256
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec512_256 (extractDigest512_256 (Impl.sha512State data Impl.H0_512_256)) = _
  rw [digestBitVec512_256_extract,
    sha512State_correct data h, toSpecState_H0_512_256]
  simp (discharger := decide) only [SHS.SHA512.sha512_256, getElem!_pos]

/-! ## SHA-512/224

The 28-byte digest crosses a 64-bit word boundary: the spec emits
`(H[0] ++ H[1] ++ H[2] ++ H[3]).leftmost 224`, keeping 3 full words plus
the high 32 bits of the fourth.  We route through SHA-512/256's 32-byte
emission and apply `leftmost 224` via the universal
`fromBits_leftmost` identity in `equiv/Common/FromBits.lean`. -/

theorem sha512_224_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512_224 (Impl.sha512_224 data) =
      SHS.SHA512.sha512_224 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha512_224
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec512_224 (extractDigest512_224 (Impl.sha512State data Impl.H0_512_224)) = _
  rw [digestBitVec512_224_extract, digestBitVec512_256_extract,
    sha512State_correct data h, toSpecState_H0_512_224]
  simp (discharger := decide) only [SHS.SHA512.sha512_224, getElem!_pos]

end SHS.Equiv.SHA512
