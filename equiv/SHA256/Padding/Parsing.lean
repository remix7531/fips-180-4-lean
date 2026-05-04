import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.ToU32s
import equiv.Common.Chunks
import Mathlib.Tactic.IntervalCases

/-! # SHA-256 padding: byte-level vs bit-level parse

Bridges the implementation's byte-level `implPaddedBlocks` with the
spec's bit-level `parse ∘ pad`.  The intermediate device is `parseBytes`
(below): a byte-aligned parse that bypasses `List.toChunks` and shows
the impl's block-wise slicing matches the spec's chunked-bit parse.

Follows FIPS 180-4 §5.2.1 (parsing the padded message into 16 × 32-bit
words per 512-bit block). -/

open SHS.Equiv.Bytes
open SHS.Equiv.ByteArray
open SHS.Equiv.Chunks
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

private theorem implPaddedBlocks_eq_parseBytes (data : ByteArray) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      parseBytes (implPaddedBytes data) := by
  unfold implPaddedBlocks parseBytes
  apply Array.ext
  · simp
  · intro i h₁ _
    simp only [Array.getElem_map, Array.getElem_ofFn]

/-- Byte-level parse equals bit-level parse over `bytesToBitMessage`,
for any 64-aligned `ByteArray`. -/
private theorem parseBytes_eq_parse (bs : ByteArray) (hMod : bs.size % 64 = 0) :
    parseBytes bs = SHS.SHA256.parse (bytesToBitMessage bs) := by
  unfold parseBytes SHS.SHA256.parse
  have hData : bs.data.size = bs.size := rfl
  have hLen : (bytesToBitMessage bs).length = 512 * (bs.size / 64) := by
    show (bs.data.toList.flatMap byteToBits).length = _
    rw [List.length_flatMap]
    rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
      funext fun _ => byteToBits_length _]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
      List.map_const, List.sum_replicate_nat]
    rw [Array.length_toList, hData]
    omega
  rw [toChunks_eq_drop_take 512 (by omega) _ (bs.size / 64) hLen]
  apply Array.ext
  · simp [Array.size_ofFn, List.toArray, List.length_map,
      List.length_range]
  · intro i hi1 hi2
    simp only [Array.getElem_ofFn, Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_range]
    show toSpecBlock _ = _
    unfold bytesToBitMessage
    rw [show i * 512 = 8 * (i * 64) from by omega,
        show (512 : Nat) = 8 * 64 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    have hSize64 : i < bs.size / 64 := by
      simp [Array.size_ofFn] at hi1; exact hi1
    have hTakeLen : ((bs.data.toList.drop (i * 64)).take 64).length = 64 := by
      simp [List.length_take, List.length_drop, hData]
      omega
    have hFlatLen : (((bs.data.toList.drop (i * 64)).take 64).flatMap byteToBits).length =
        32 * 16 := by
      rw [List.length_flatMap]
      rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
        funext fun _ => byteToBits_length _]
      rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
        List.map_const, List.sum_replicate_nat, hTakeLen]
    rw [toChunks_eq_drop_take 32 (by omega) _ 16 hFlatLen]
    apply Vector.ext
    intro j hjLt
    have hLHS := toSpecBlock_toU32s_index
      (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val)) ⟨j, hjLt⟩
    have hSizeLHS : j < 16 := hjLt
    rw [show (toSpecBlock (Impl.toU32s
            (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val))))[j]'hjLt =
          (toSpecBlock (Impl.toU32s
            (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val))))[j]! from
        (getElem!_pos _ j hSizeLHS).symm]
    rw [hLHS]
    -- RHS is `(Vector.ofFn ...)[j]`; reduce.
    rw [show ((Vector.ofFn (fun i_1 : Fin 16 =>
            ((List.map Word.fromBits
              (List.map (fun i_2 => List.take 32 (List.drop (i_2 * 32)
                (List.flatMap byteToBits (List.take 64 (List.drop (i * 64) bs.data.toList)))))
                (List.range 16))).toArray)[i_1.val]?.getD 0))[j]'hjLt) =
          ((List.map Word.fromBits
            (List.map (fun i_2 => List.take 32 (List.drop (i_2 * 32)
              (List.flatMap byteToBits (List.take 64 (List.drop (i * 64) bs.data.toList)))))
              (List.range 16))).toArray)[j]?.getD 0 from by
        rw [Vector.getElem_ofFn]]
    rw [show (((List.map Word.fromBits
            (List.map (fun i_2 => List.take 32 (List.drop (i_2 * 32)
              (List.flatMap byteToBits (List.take 64 (List.drop (i * 64) bs.data.toList)))))
              (List.range 16))).toArray)[j]?).getD 0 =
          (List.map Word.fromBits
            (List.map (fun i_2 => List.take 32 (List.drop (i_2 * 32)
              (List.flatMap byteToBits (List.take 64 (List.drop (i * 64) bs.data.toList)))))
              (List.range 16))).toArray[j]'(by
                simp [List.length_map, List.length_range]; exact hjLt) from by
        rw [Array.getElem?_eq_getElem (h := by
          simp [List.length_map, List.length_range]; exact hjLt)]
        rfl]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    congr 1
    rw [show j * 32 = 8 * (4 * j) from by grind,
        show (32 : Nat) = 8 * 4 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    unfold fourBytesBits
    have hSizeBs : i * 64 + 4 * j + 4 ≤ bs.size := by
      have hMod' : bs.size = 64 * (bs.size / 64) := by grind
      have h1 : i + 1 ≤ bs.size / 64 := hSize64
      have h2 : 64 * (i + 1) ≤ 64 * (bs.size / 64) := Nat.mul_le_mul_left 64 h1
      grind
    have hRhsList :
        List.take 4 (List.drop (4 * j)
          (List.take 64 (List.drop (i * 64) bs.data.toList))) =
        [bs.data.toList[i * 64 + 4 * j]'(by rw [Array.length_toList, hData]; grind),
         bs.data.toList[i * 64 + 4 * j + 1]'(by rw [Array.length_toList, hData]; grind),
         bs.data.toList[i * 64 + 4 * j + 2]'(by rw [Array.length_toList, hData]; grind),
         bs.data.toList[i * 64 + 4 * j + 3]'(by rw [Array.length_toList, hData]; grind)] := by
      rw [List.drop_take, List.take_take]
      rw [Nat.min_eq_left (by grind : 4 ≤ 64 - 4 * j)]
      rw [List.drop_drop]
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, Array.length_toList, hData]
        grind
      · intro k hk1 hk2
        simp only [List.length_cons, List.length_nil] at hk2
        interval_cases k <;>
          simp [List.getElem_take, List.getElem_drop, Nat.add_assoc]
    rw [hRhsList]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [Vector.getElem_ofFn]
    have h0 : i * 64 + (4 * j + 0) < bs.size := by grind
    have h1 : i * 64 + (4 * j + 1) < bs.size := by grind
    have h2 : i * 64 + (4 * j + 2) < bs.size := by grind
    have h3 : i * 64 + (4 * j + 3) < bs.size := by grind
    rw [get!_eq_toList_getElem bs (i * 64 + 4 * j) (by grind),
        show i * 64 + (4 * j + 1) = i * 64 + 4 * j + 1 from by grind,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 1) (by grind),
        show i * 64 + (4 * j + 2) = i * 64 + 4 * j + 2 from by grind,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 2) (by grind),
        show i * 64 + (4 * j + 3) = i * 64 + 4 * j + 3 from by grind,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 3) (by grind)]
    simp [List.append_assoc]

theorem implPaddedBlocks_lift_eq_parsePad (data : ByteArray)
    (h : data.size < 2 ^ 61) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      SHS.SHA256.parse (SHS.SHA1.pad (bytesToBitMessage data)) := by
  rw [← bytesToBitMessage_implPaddedBytes data h]
  rw [implPaddedBlocks_eq_parseBytes]
  exact parseBytes_eq_parse _ (size_implPaddedBytes_mod data)

end SHS.Equiv.SHA256.Padding.Parsing
