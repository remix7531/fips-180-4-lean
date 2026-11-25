import equiv.SHA256.Padding.Layout
import equiv.Common.Padding
import spec.Preprocessing

/-! # SHA-256 padding: byte → bit decoding

The shared byte decoder connects the streaming pad to the specification.
SHA-256 appends the bit length in a 64-bit big-endian field. -/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA256.Padding.Layout

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.ByteDecoding

open scoped SHS.SHA256

/-- Decode bytes in the message bit order used by SHA-256. -/
abbrev bytesToBitMessage : ByteArray → SHS.Message := SHS.Equiv.Padding.bytesToBitMessage

/-- `lengthBE64` decodes to the 64-bit big-endian bit list of `bits`. -/
theorem bytesToBitMessage_lengthBE64 (bits : UInt64) :
    bytesToBitMessage (lengthBE64 bits) =
      (List.range 64).reverse.map bits.toNat.testBit := by
  simp [lengthBE64, bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage, byteToBits,
    List.ofFn_succ, List.range, List.range.loop]
  simp +arith only [show (256 : Nat) = 2 ^ 8 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.reduceAdd]
  simp +decide

/-- Streaming pad ↔ spec `pad`.  Combine the four distributivity steps
plus a case-split on `data.size % 64 < 56`.

The bound `data.size < 2^61` ensures `8 * data.size < 2^64` so the
FIPS 180-4 §5.1.1 64-bit bit-length suffix fits in a `UInt64`. -/
theorem bytesToBitMessage_implPaddedBytes
    (data : ByteArray) (h : data.size < 2 ^ 61) :
    bytesToBitMessage (implPaddedBytes data) =
      SHS.SHA1.pad (bytesToBitMessage data) := by
  unfold implPaddedBytes SHS.SHA1.pad SHS.SHA256.pad
  simp only [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_append,
    SHS.Equiv.Padding.bytesToBitMessage_appendZeros, SHS.Equiv.Padding.bytesToBitMessage_push_0x80,
    SHS.Equiv.Padding.bytesToBitMessage_length, bytesToBitMessage_lengthBE64,
    SHS.Equiv.Padding.totalBits_toNat data h]
  simp only [List.append_assoc, List.replicate_append_replicate]
  rw [SHS.Equiv.Padding.find_bit_padding data.size 64 8 (by decide)]
  rfl

end SHS.Equiv.SHA256.Padding.ByteDecoding
