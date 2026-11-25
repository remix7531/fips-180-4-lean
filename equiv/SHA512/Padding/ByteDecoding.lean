import equiv.SHA512.Padding.Layout
import equiv.Common.Padding
import spec.Preprocessing

/-! # SHA-512 padding: byte → bit decoding

The shared byte decoder connects the streaming pad to the specification.
The SHA-512 implementation emits zeros in the high half of the 128-bit
length field. -/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA512.Padding.Layout

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.ByteDecoding

open scoped SHS.SHA512

/-- Decode bytes in the message bit order used by SHA-512. -/
abbrev bytesToBitMessage : ByteArray → SHS.Message := SHS.Equiv.Padding.bytesToBitMessage

/-- `lengthBE128` decodes to a 128-bit MSB-first bit list: 64 zero bits
followed by the 64-bit BE encoding of `bits`. -/
theorem bytesToBitMessage_lengthBE128 (bits : UInt64) :
    bytesToBitMessage (lengthBE128 bits) =
      List.replicate 64 false ++ (List.range 64).reverse.map bits.toNat.testBit := by
  simp [lengthBE128, bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage, byteToBits,
    List.ofFn_succ, List.range, List.range.loop]
  simp +arith only [show (256 : Nat) = 2 ^ 8 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.reduceAdd]
  simp +decide

/-- Streaming pad ↔ SHA-512 spec `pad`. -/
theorem bytesToBitMessage_implPaddedBytes
    (data : ByteArray) (h : data.size < 2 ^ 61) :
    bytesToBitMessage (implPaddedBytes data) =
      SHS.SHA512.pad (bytesToBitMessage data) := by
  unfold implPaddedBytes SHS.SHA512.pad
  simp only [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_append,
    SHS.Equiv.Padding.bytesToBitMessage_appendZeros, SHS.Equiv.Padding.bytesToBitMessage_push_0x80,
    SHS.Equiv.Padding.bytesToBitMessage_length, bytesToBitMessage_lengthBE128,
    SHS.Equiv.Padding.totalBits_toNat data h]
  simp only [List.append_assoc, List.replicate_append_replicate]
  have hHigh : (List.range 128).reverse.map (8 * data.size).testBit =
      List.replicate 64 false ++ (List.range 64).reverse.map (8 * data.size).testBit := by
    rw [show (128 : Nat) = 64 + 64 by decide, List.range_add, List.reverse_append,
      ← List.map_reverse, List.map_append, List.map_map]
    congr 1
    calc
      _ = List.replicate (List.range 64).reverse.length false := by
        apply List.map_eq_replicate_iff.mpr
        intro index _
        have fits : 8 * data.size < 2 ^ 64 := by omega
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (by simp)))
      _ = _ := by simp
  rw [hHigh]
  rw [SHS.Equiv.Padding.find_bit_padding data.size 128 16 (by decide)]
  rfl

end SHS.Equiv.SHA512.Padding.ByteDecoding
