/-! # Common: `Array.foldl ∘ Array.ofFn` ↔ `Fin.foldl`

Both folds enumerate the same finite range in order. -/

namespace SHS.Equiv.ArrayFold

/-- Folding over an `Array.ofFn` is the same as `Fin.foldl` over the
generating function. -/
theorem array_foldl_ofFn_eq_fin_foldl {α : Type _} {β : Type _} (n : Nat) (g : Fin n → α)
    (f : β → α → β) (init : β) :
    (Array.ofFn g).foldl f init = Fin.foldl n (fun b i => f b (g i)) init := by
  rw [← Array.foldl_toList, Array.toList_ofFn, Fin.foldl_eq_finRange_foldl,
    ← List.foldl_map (f := g) (g := f)]
  simp only [List.finRange, List.map_ofFn, Function.comp_def]

end SHS.Equiv.ArrayFold
