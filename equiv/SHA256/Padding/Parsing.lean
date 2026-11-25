import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.ToU32s
import equiv.Common.Parsing

/-! # SHA-256 padding: byte-level vs bit-level parse

Bridges the implementation's byte-level `implPaddedBlocks` with the
spec's bit-level `parse ∘ pad`.  The intermediate device is `parseBytes`
(below): a byte-aligned parse that bypasses `listChunks` and shows
the impl's block-wise slicing matches the spec's chunked-bit parse.

Follows FIPS 180-4 §5.2.1 (parsing the padded message into 16 × 32-bit
words per 512-bit block). -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.ToU32s
open SHS.Equiv.SHA256.Padding.Layout
open SHS.Equiv.SHA256.Padding.ByteDecoding

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Parsing

open scoped SHS.SHA256

/-- Byte-level alternative to `SHS.SHA256.parse`: parse a 64-aligned
`ByteArray` directly into 16-word blocks, bypassing bit-level `toChunks`. -/
private def parseBytes (bs : ByteArray) : Array Block :=
  Array.ofFn (n := bs.size / 64) fun i =>
    toSpecBlock (Impl.toU32s (Vector.ofFn fun j : Fin 64 =>
      bs.get! (i.val * 64 + j.val)))

/-- The lifted byte-block view of the streaming pad equals the
byte-level `parseBytes` of the padded bytes.  Both unfold to the same
`Array.ofFn` indexing the same `implPaddedBytes`. -/
private theorem implPaddedBlocks_eq_parseBytes (data : ByteArray) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      parseBytes (implPaddedBytes data) := by
  unfold implPaddedBlocks parseBytes
  rw [Array.map_ofFn]
  rfl

/-- Byte-level parse equals bit-level parse over `bytesToBitMessage`,
for any 64-aligned `ByteArray`. -/
private theorem parseBytes_eq_parse (bs : ByteArray) (hMod : bs.size % 64 = 0) :
    parseBytes bs = SHS.SHA256.parse (bytesToBitMessage bs) := by
  have aligned : (bytesToBitMessage bs).length = (32 * 16) * (bs.size / 64) := by
    simp only [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_length]
    omega
  have specParse := SHS.Equiv.Padding.parseChunked_eq_ofFn
    (bytesToBitMessage bs) 32 16 (bs.size / 64) (by decide) (by decide) aligned
  change SHS.SHA256.parse (bytesToBitMessage bs) = _ at specParse
  rw [specParse]
  unfold parseBytes
  refine congrArg Array.ofFn ?_
  funext blockIndex
  apply Vector.ext
  intro wordIndex wordBound
  simp only [Vector.getElem_ofFn]
  rw [← getElem!_pos _ wordIndex wordBound, toSpecBlock_toU32s_slice _ ⟨wordIndex, wordBound⟩]
  have blockBound : blockIndex.val < bs.size / 64 := blockIndex.isLt
  have blockFits : blockIndex.val * 64 + 64 ≤ bs.size := by omega
  rw [blockToBits, SHS.Equiv.Padding.byteWindow_toBits bs _ _ blockFits]
  rw [show 8 * (blockIndex.val * 64) = blockIndex.val * 512 by omega]

/-- The headline of this file: lifting `implPaddedBlocks` through
`toSpecBlock ∘ Impl.toU32s` equals the spec's `parse (pad msg)` of the
input bit-message.  Routes through `parseBytes` as the intermediate
byte-level form.  Consumed by `Pipeline.lean`'s `implPaddedBlocks_lift`
rewrite. -/
theorem implPaddedBlocks_lift_eq_parsePad (data : ByteArray)
    (h : data.size < 2 ^ 61) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      SHS.SHA256.parse (SHS.SHA1.pad (bytesToBitMessage data)) := by
  rw [← bytesToBitMessage_implPaddedBytes data h]
  rw [implPaddedBlocks_eq_parseBytes]
  exact parseBytes_eq_parse _ (size_implPaddedBytes_mod data)

end SHS.Equiv.SHA256.Padding.Parsing
