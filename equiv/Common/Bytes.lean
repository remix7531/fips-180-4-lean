import equiv.Common.FromBits

/-! # Common: byte ↔ bit utilities

Defines `byteToBits` and proves its packing, length, and slicing laws. -/

namespace SHS.Equiv.Bytes

/-- Convert one byte to its eight MSB-first bits.  Mirrors the spec's
`bytesToBits` (used in `tests/Parser.lean`) but lives in `equiv/` so the
proof stack does not depend on the test directory. -/
def byteToBits (b : UInt8) : List Bool :=
  (List.range 8).reverse.map b.toNat.testBit

/-- Each byte produces exactly eight bits. -/
theorem byteToBits_length (b : UInt8) : (byteToBits b).length = 8 := by
  simp [byteToBits]

theorem flatMap_byteToBits_length (l : List UInt8) :
    (l.flatMap byteToBits).length = 8 * l.length := by
  simp only [List.length_flatMap, byteToBits_length]
  change (l.map (Function.const UInt8 8)).sum = _
  rw [List.map_const, List.sum_replicate_nat, Nat.mul_comm]

/-- Bridge between `UInt8.toNat.testBit` (used by `byteToBits`) and
`BitVec.getLsbD` (the form `bv_decide` understands).  Lets every
`Word.fromBits ∘ byteToBits` proof translate the bit-list goal into
pure-`BitVec` arithmetic via a single `simp only [...]` step.  Not
attributed `@[simp]` because it interacts badly with `simp` calls in
contexts that prefer to keep `Nat.testBit` as the canonical form. -/
theorem UInt8.toNat_testBit_eq_getLsbD (b : UInt8) (i : Nat) :
    b.toNat.testBit i = b.toBitVec.getLsbD i := by
  rw [show b.toNat = b.toBitVec.toNat from rfl, BitVec.testBit_toNat]

/-- Packing a byte's bits gives its bit vector resized to the requested width. -/
theorem fromBits_byteToBits {width : Nat} (byte : UInt8) :
    SHS.Word.fromBits (n := width) (byteToBits byte) = byte.toBitVec.setWidth width := by
  rw [FromBits.fromBits_eq_ofBoolListBE]
  congr 1
  apply BitVec.eq_of_getMsbD_eq
  intro index hIndex
  rw [BitVec.getMsbD_ofBoolListBE]
  change (byteToBits byte).getD index false = byte.toBitVec.getMsbD index
  have hByteIndex : index < 8 := by simpa only [byteToBits_length] using hIndex
  rw [BitVec.getMsbD_eq_getLsbD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIndex]
  simp only [hByteIndex, decide_true, Bool.true_and, byteToBits, Option.getD_some,
    List.getElem_map, List.getElem_reverse, List.length_range, List.getElem_range,
    UInt8.toNat_testBit_eq_getLsbD]

/-- Dropping `8 * k` bits from `l.flatMap byteToBits` is the same as
dropping `k` bytes from `l` first.  Used to slice the bit-list view of a
padded message at byte boundaries. -/
theorem flatMap_byteToBits_drop_8 (l : List UInt8) (k : Nat) :
    (l.flatMap byteToBits).drop (8 * k) = (l.drop k).flatMap byteToBits := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rcases l with _ | ⟨b, bs⟩
    · simp
    · simp only [List.flatMap_cons]
      have hsplit : 8 * (k + 1) = (byteToBits b).length + 8 * k := by
        rw [byteToBits_length]; omega
      rw [hsplit, List.drop_length_add_append, ih, List.drop_succ_cons]

/-- Taking `8 * m` bits from `l.flatMap byteToBits` is the same as
taking `m` bytes from `l` first. -/
theorem flatMap_byteToBits_take_8 (l : List UInt8) (m : Nat) :
    (l.flatMap byteToBits).take (8 * m) = (l.take m).flatMap byteToBits := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    rcases l with _ | ⟨b, bs⟩
    · simp
    · simp only [List.flatMap_cons]
      have hsplit : 8 * (m + 1) = (byteToBits b).length + 8 * m := by
        rw [byteToBits_length]; omega
      rw [hsplit, List.take_length_add_append, ih, List.take_succ_cons,
        List.flatMap_cons]

end SHS.Equiv.Bytes
