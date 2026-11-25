import equiv.SHA256.Pipeline
import equiv.SHA256.Digest

/-! # SHA-256 hash correctness

Each digest proof specializes final-state equivalence to its initial
hash value, then applies the relevant digest emission theorem. -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Digest
open SHS.Equiv.SHA256.Padding.ByteDecoding
open SHS.Equiv.SHA256.Pipeline

open SHS.SHA256

namespace SHS.Equiv.SHA256

open scoped SHS.SHA256

/-- The bytewise `Impl.sha256` agrees with the spec's bitwise `sha256`,
viewing the 32-byte digest as a 256-bit big-endian BitVec.

The hypothesis `data.size < 2 ^ 61` ensures `8 * data.size < 2 ^ 64` so
that the FIPS 180-4 §5.1.1 bit-length encoding fits in a single
`UInt64` (the 64-bit-length suffix appended during padding).
-/
theorem sha256_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec (Impl.sha256 data) =
      SHS.SHA256.sha256 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha256
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec (extractDigest (Impl.sha256State data Impl.H256_256)) = _
  rw [digestBitVec_extract, sha256State_correct data h, toSpecState_H256_256]
  simp (discharger := decide) only [SHS.SHA256.sha256, getElem!_pos]

/-- The bytewise `Impl.sha224` agrees with the spec's bitwise `sha224`,
viewing the 28-byte digest as a 224-bit big-endian BitVec.

The size hypothesis is identical to SHA-256: SHA-224 uses the same
64-bit length encoding as SHA-256. -/
theorem sha224_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec224 (Impl.sha224 data) =
      SHS.SHA256.sha224 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  unfold Impl.sha224
  rw [ite_eq_right (Nat.not_le.mpr h)]
  change digestBitVec224 (extractDigest224 (Impl.sha256State data Impl.H256_224)) = _
  rw [digestBitVec224_extract, sha256State_correct data h, toSpecState_H256_224]
  simp (discharger := decide) only [SHS.SHA256.sha224, getElem!_pos]

end SHS.Equiv.SHA256
