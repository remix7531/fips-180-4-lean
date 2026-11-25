import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.ToU64s
import equiv.Common.Parsing

/-! # SHA-512 padding: byte-level vs bit-level parse

Parallel to `equiv/SHA256/Padding/Parsing.lean` at 128-byte blocks,
1024-bit blocks, 64-bit words, 8 bytes per word.

Bridges the implementation's byte-level `implPaddedBlocks` with the
spec's bit-level `parse ∘ pad`.  The intermediate device is
`parseBytes` (below): a byte-aligned parse that bypasses
`listChunks` and shows the impl's block-wise slicing matches the
spec's chunked-bit parse.

Follows FIPS 180-4 §5.2.2 (parsing the padded message into 16 × 64-bit
words per 1024-bit block). -/

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.ToU64s
open SHS.Equiv.SHA512.Padding.Layout
open SHS.Equiv.SHA512.Padding.ByteDecoding

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Parsing

open scoped SHS.SHA512

/-- Byte-level alternative to `SHS.SHA512.parse`: parse a 128-aligned
`ByteArray` directly into 16-word blocks, bypassing bit-level `toChunks`. -/
private def parseBytes (bs : ByteArray) : Array Block :=
  Array.ofFn (n := bs.size / 128) fun i =>
    toSpecBlock (Impl.toU64s (Vector.ofFn fun j : Fin 128 =>
      bs.get! (i.val * 128 + j.val)))

/-- The lifted byte-block view of the streaming pad equals the
byte-level `parseBytes` of the padded bytes.  Both unfold to the same
`Array.ofFn` indexing the same `implPaddedBytes`. -/
private theorem implPaddedBlocks_eq_parseBytes (data : ByteArray) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b)) =
      parseBytes (implPaddedBytes data) := by
  unfold implPaddedBlocks parseBytes
  rw [Array.map_ofFn]
  rfl

/-- Byte-level `parseBytes` of a 128-aligned `ByteArray` equals the
spec's bit-level `parse` of its `bytesToBitMessage`. -/
private theorem parseBytes_eq_parse (bs : ByteArray) (hMod : bs.size % 128 = 0) :
    parseBytes bs = SHS.SHA512.parse (bytesToBitMessage bs) := by
  have aligned : (bytesToBitMessage bs).length = (64 * 16) * (bs.size / 128) := by
    simp only [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_length]
    omega
  have specParse := SHS.Equiv.Padding.parseChunked_eq_ofFn
    (bytesToBitMessage bs) 64 16 (bs.size / 128) (by decide) (by decide) aligned
  change SHS.SHA512.parse (bytesToBitMessage bs) = _ at specParse
  rw [specParse]
  unfold parseBytes
  refine congrArg Array.ofFn ?_
  funext blockIndex
  apply Vector.ext
  intro wordIndex wordBound
  simp only [Vector.getElem_ofFn]
  rw [← getElem!_pos _ wordIndex wordBound, toSpecBlock_toU64s_slice _ ⟨wordIndex, wordBound⟩]
  have blockBound : blockIndex.val < bs.size / 128 := blockIndex.isLt
  have blockFits : blockIndex.val * 128 + 128 ≤ bs.size := by omega
  rw [blockToBits, SHS.Equiv.Padding.byteWindow_toBits bs _ _ blockFits]
  rw [show 8 * (blockIndex.val * 128) = blockIndex.val * 1024 by omega]

/-- The headline of this file: lifting `implPaddedBlocks` through
`toSpecBlock ∘ Impl.toU64s` equals the spec's `parse (pad msg)` of the
input bit-message.  Routes through `parseBytes` as the intermediate
byte-level form.  Consumed by `Pipeline.lean`'s `implPaddedBlocks_lift`
rewrite. -/
theorem implPaddedBlocks_lift_eq_parsePad (data : ByteArray)
    (h : data.size < 2 ^ 61) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b)) =
      SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data)) := by
  rw [← bytesToBitMessage_implPaddedBytes data h]
  rw [implPaddedBlocks_eq_parseBytes]
  exact parseBytes_eq_parse _ (size_implPaddedBytes_mod data)

end SHS.Equiv.SHA512.Padding.Parsing
