import equiv.SHA256.Lift
import equiv.Common.Bytes
import equiv.Common.FromBits

/-! # SHA-256 digest emission

Turn an 8-word `Impl.State` into a 32-byte big-endian digest, and prove
that this byte stream — read back into a `BitVec 256` via
`Word.fromBits` — equals the spec's `H[0]! ++ … ++ H[7]!`. -/

open SHS.Equiv.Bytes
open SHS.Equiv.FromBits
open SHS.Equiv.SHA256.Lift

open SHS.SHA256

namespace SHS.Equiv.SHA256.Digest

open scoped SHS.SHA256

/-- 32-byte digest viewed as a 256-bit MSB-first big-endian `BitVec`,
matching how the spec's `H[0]! ++ … ++ H[7]!` is laid out. -/
def digestBitVec (d : Vector UInt8 32) : BitVec 256 :=
  SHS.Word.fromBits (n := 256)
    (d.toList.flatMap fun b => byteToBits b)

/-- Common state-to-bytes extractor used by both `Impl.sha256` and
`implSha256Refactored`: each of the eight `UInt32` words emits four
big-endian bytes. -/
def extractDigest (state : Impl.State) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- 4-byte big-endian decomposition of `w : UInt32`, MSB-first bits, fed
to `Word.fromBits` at width 256, equals `w.toBitVec.zeroExtend 256`.
Same shape as `ToU32s.fromBits_byteToBits` at width 256. -/
private theorem fromBits_4bytes_BE_256 (w : UInt32) :
    SHS.Word.fromBits (n := 256)
      (((List.range 4).map fun b =>
        ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 256 := by
  unfold byteToBits SHS.Word.fromBits
  simp only [show UInt32.ofNat ((3 - 0) * 8) = 24 from rfl,
    show UInt32.ofNat ((3 - 1) * 8) = 16 from rfl,
    show UInt32.ofNat ((3 - 2) * 8) = 8 from rfl,
    show UInt32.ofNat ((3 - 3) * 8) = 0 from rfl,
    List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.foldl,
    UInt8.toNat_testBit_eq_getLsbD]
  bv_decide

private theorem flatMap_byteToBits_length (l : List UInt8) :
    (l.flatMap byteToBits).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.length_append, byteToBits_length, ih,
      List.length_cons]
    omega

-- The RHS lists eight parallel `(List.range 4).map …` chunks, one per word
-- index 0..7; the per-word lines are intentionally aligned for visual symmetry
-- and breaking each across multiple lines hurts more than it helps.
set_option linter.style.longLine false in
/-- The 32-byte BE digest list, restated as 8 four-byte chunks. -/
private theorem digest_list_eq_8chunks (state : Impl.State) :
    (Vector.ofFn (n := 32) fun i : Fin 32 =>
        let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
        let byteIdx := i.val % 4
        ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 4).map fun b => ((state[(0 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(1 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(2 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(3 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(4 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(5 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(6 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(7 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

/-- Final byte-extraction emission matches the spec's `H[0]! ++ … ++ H[7]!`. -/
theorem digestBitVec_extract (state : Impl.State) :
    digestBitVec (extractDigest state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := by
  unfold digestBitVec extractDigest
  rw [digest_list_eq_8chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width]
  rw [fromBits_4bytes_BE_256, fromBits_4bytes_BE_256, fromBits_4bytes_BE_256,
      fromBits_4bytes_BE_256, fromBits_4bytes_BE_256, fromBits_4bytes_BE_256,
      fromBits_4bytes_BE_256, fromBits_4bytes_BE_256]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 4 = 32 from rfl]
  simp only [show (0 : Nat) = (0 : Fin 8).val from rfl,
             show (1 : Nat) = (1 : Fin 8).val from rfl,
             show (2 : Nat) = (2 : Fin 8).val from rfl,
             show (3 : Nat) = (3 : Fin 8).val from rfl,
             show (4 : Nat) = (4 : Fin 8).val from rfl,
             show (5 : Nat) = (5 : Fin 8).val from rfl,
             show (6 : Nat) = (6 : Fin 8).val from rfl,
             show (7 : Nat) = (7 : Fin 8).val from rfl,
             getElem!_toSpecState]
  generalize state[(0 : Fin 8)].toBitVec = w0
  generalize state[(1 : Fin 8)].toBitVec = w1
  generalize state[(2 : Fin 8)].toBitVec = w2
  generalize state[(3 : Fin 8)].toBitVec = w3
  generalize state[(4 : Fin 8)].toBitVec = w4
  generalize state[(5 : Fin 8)].toBitVec = w5
  generalize state[(6 : Fin 8)].toBitVec = w6
  generalize state[(7 : Fin 8)].toBitVec = w7
  rw [show (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7
            : BitVec (32+32+32+32+32+32+32+32))
       = (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7).setWidth 256 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

end SHS.Equiv.SHA256.Digest
