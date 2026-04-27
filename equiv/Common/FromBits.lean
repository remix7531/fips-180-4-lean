import spec.Setup
import Mathlib.Data.List.Induction

/-! # Common: `Word.fromBits` structural lemmas

`fromBits_foldl_init` (folding from a non-zero accumulator) and
`fromBits_append_same_width` (distribution over `++`).  Stated at
arbitrary `N` so SHA-512 (`N = 64`) reuses them unchanged. -/

namespace SHS.Equiv.FromBits

/-- `Word.fromBits` foldl with an arbitrary initial accumulator. -/
theorem fromBits_foldl_init {N : Nat} (x : BitVec N) (r : List Bool) :
    r.foldl (fun (acc : BitVec N) b => acc <<< 1 ||| (if b then 1 else 0)) x =
      (x <<< r.length) ||| SHS.Word.fromBits (n := N) r := by
  induction r using List.reverseRecOn generalizing x with
  | nil => simp [SHS.Word.fromBits]
  | append_singleton xs y ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
      List.length_nil]
    rw [ih]
    unfold SHS.Word.fromBits
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (0 : BitVec N)]
    rw [show xs.length + (0 + 1) = xs.length + 1 from by omega]
    rw [BitVec.shiftLeft_add x xs.length 1, BitVec.shiftLeft_or_distrib, BitVec.or_assoc]

/-- `Word.fromBits` of an append at the same width. -/
theorem fromBits_append_same_width {N : Nat} (l r : List Bool) :
    SHS.Word.fromBits (n := N) (l ++ r) =
      (SHS.Word.fromBits (n := N) l) <<< r.length ||| SHS.Word.fromBits (n := N) r := by
  show (l ++ r).foldl _ 0 = _
  rw [List.foldl_append, fromBits_foldl_init]
  rfl

end SHS.Equiv.FromBits
