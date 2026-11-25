import spec.Setup

/-! # Common: `Word.fromBits` structural lemmas -/

namespace SHS.Equiv.FromBits

/-- `Word.fromBits` foldl with an arbitrary initial accumulator. -/
theorem fromBits_foldl_init {N : Nat} (x : BitVec N) (r : List Bool) :
    r.foldl (fun (acc : BitVec N) b => acc <<< 1 ||| (if b then 1 else 0)) x =
      (x <<< r.length) ||| SHS.Word.fromBits (n := N) r := by
  induction r generalizing x with
  | nil => simp [SHS.Word.fromBits]
  | cons bit tail ih =>
    change (bit :: tail).foldl _ x = _ ||| (bit :: tail).foldl _ 0
    rw [List.foldl_cons, List.foldl_cons, ih, ih]
    simp only [List.length_cons, BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add,
      Nat.add_comm 1, BitVec.or_assoc]
    have zeroShift : (0 : BitVec N) <<< (tail.length + 1) = 0 := BitVec.zero_shiftLeft _
    have zeroOr (a : BitVec N) : (0 : BitVec N) ||| a = a := BitVec.zero_or
    simp only [zeroShift, zeroOr]

/-- `Word.fromBits` of an append at the same width. -/
theorem fromBits_append_same_width {N : Nat} (l r : List Bool) :
    SHS.Word.fromBits (n := N) (l ++ r) =
      (SHS.Word.fromBits (n := N) l) <<< r.length ||| SHS.Word.fromBits (n := N) r := by
  show (l ++ r).foldl _ 0 = _
  rw [List.foldl_append, fromBits_foldl_init]; rfl

/-- `Word.fromBits` packs the bits in big-endian order at the requested width. -/
theorem fromBits_eq_ofBoolListBE {N : Nat} (bits : List Bool) :
    SHS.Word.fromBits (n := N) bits = (BitVec.ofBoolListBE bits).setWidth N := by
  induction bits with
  | nil => simp [SHS.Word.fromBits, BitVec.ofBoolListBE]
  | cons head tail ih =>
    change SHS.Word.fromBits (n := N) ([head] ++ tail) = _
    rw [fromBits_append_same_width, ih]
    simp only [BitVec.ofBoolListBE, BitVec.cons, BitVec.setWidth_cast,
      BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    congr 2
    cases head <;> simp [SHS.Word.fromBits,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)]

/-- The leftmost bits of a full-width packing come from the corresponding list prefix. -/
theorem fromBits_leftmost {M N : Nat} (bits : List Bool)
    (hLen : bits.length = M) (hN : N ≤ M) :
    (SHS.Word.fromBits (n := M) bits).leftmost N =
      SHS.Word.fromBits (n := N) (bits.take N) := by
  rw [fromBits_eq_ofBoolListBE, fromBits_eq_ofBoolListBE]
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have takeLength : (bits.take N).length = N := by simp [List.length_take, hLen, hN]
  rw [BitVec.leftmost, BitVec.getMsbD_extractLsb', Nat.sub_add_cancel hN,
    show M - (M - i) = i by omega]
  simp only [hi, Nat.sub_le, decide_true, Bool.true_and, BitVec.getMsbD_setWidth, hLen,
    takeLength, Nat.sub_self, Nat.zero_le, Nat.add_sub_cancel, BitVec.getMsbD_ofBoolListBE,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

end SHS.Equiv.FromBits
