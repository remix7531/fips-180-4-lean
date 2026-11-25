/-!
# Generic loop infrastructure for the spec ↔ implementation equivalence

The SHA-256 / SHA-512 specs are written in `do`-notation:
```
Id.run do
  for t in [0:n] do
    …
```
which makes induction over the loop body awkward.  This module provides
the generic plumbing that lets the equivalence proofs treat such loops
as `Fin.foldl` instead, and that lets us fuse / split / transport folds
as needed.

## Contents (`SHS.Equiv.Loop`)

* `forIn_id_eq_Fin_foldl_offset` converts a loop over `[a:b]` to a finite fold.
* `forIn_id_eq_Fin_foldl` specializes this to `[0:n]`.
* `forIn'_split_eq_Fin_foldl` joins consecutive loops that apply the same step.
* `fin_foldl_transport` — push a state map `φ` through a fold,
  provided each step commutes with `φ`.

The shared `SHS.Equiv.VecBridge.set_bang_eq_set` lemma converts an
in-bounds `Vector.set!` to `Vector.set`.
-/

namespace SHS.Equiv.Loop

/-! ## `forIn` ↔ `Fin.foldl` -/

/-- Convert a pure-yield loop over `[a:b]` to a fold over its finite index range. -/
theorem forIn_id_eq_Fin_foldl_offset {β : Type _} (a b : Nat) (init : β) (f : Nat → β → β) :
    Id.run (forIn [a:b] init (fun t s => pure (ForInStep.yield (f t s)))) =
      Fin.foldl (b - a) (fun s t => f (t.val + a) s) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Fin.foldl_eq_finRange_foldl]
  have indices : List.range' a [a:b].size 1 =
      (List.finRange (b - a)).map (fun i => i.val + a) := by
    apply List.ext_getElem <;> simp [Std.Legacy.Range.size, Nat.add_comm]
  rw [indices, List.foldl_map]
  rfl

/-- Pure-yield `forIn` over `[0:n]` in the identity monad equals `Fin.foldl n`. -/
theorem forIn_id_eq_Fin_foldl {β : Type _} (n : Nat) (init : β) (f : Nat → β → β) :
    Id.run (forIn [0:n] init (fun t s => pure (ForInStep.yield (f t s)))) =
      Fin.foldl n (fun s t => f t.val s) init := by
  simpa using forIn_id_eq_Fin_foldl_offset 0 n init f

/-- Consecutive pure-yield loops that apply the same step form a single finite fold. -/
theorem forIn'_split_eq_Fin_foldl {State : Type _} (prefixLength total : Nat)
    (ordered : prefixLength ≤ total) (initial : State) (step : Nat → State → State)
    (first : (t : Nat) → t ∈ [0:prefixLength] → State → State)
    (second : (t : Nat) → t ∈ [prefixLength:total] → State → State)
    (first_agrees : ∀ t member state, first t member state = step t state)
    (second_agrees : ∀ t member state, second t member state = step t state) :
    Id.run (forIn' [prefixLength:total]
      (Id.run (forIn' [0:prefixLength] initial
        (fun t member state => pure (ForInStep.yield (first t member state)))))
      (fun t member state => pure (ForInStep.yield (second t member state)))) =
      Fin.foldl total (fun state i => step i.val state) initial := by
  simp only [first_agrees, second_agrees, forIn'_eq_forIn]
  rw [forIn_id_eq_Fin_foldl, forIn_id_eq_Fin_foldl_offset]
  have size : total = prefixLength + (total - prefixLength) := (Nat.add_sub_cancel' ordered).symm
  conv => rhs; rw [size, Fin.foldl_add]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.add_comm prefixLength]

/-- Transport a `Fin.foldl` along a state map `φ`: if `φ` commutes
with each step (`φ (f a i) = g (φ a) i`), then it commutes with the
whole fold.

This is how we cross the impl/spec divide: the inner loop on the impl
side folds `Impl.State`, the inner loop on the spec side folds
`HashValue`, and `φ = toSpecState` carries one to the other.  The
per-step commutation hypothesis `h` is discharged by the round-body
bridges in `Functions.lean`. -/
theorem fin_foldl_transport {α β : Type _} (n : Nat)
    (f : α → Fin n → α) (g : β → Fin n → β) (φ : α → β) (init : α)
    (h : ∀ (a : α) (i : Fin n), φ (f a i) = g (φ a) i) :
    φ (Fin.foldl n f init) = Fin.foldl n g (φ init) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  exact (List.foldl_hom φ (fun a i => (h a i).symm)).symm

end SHS.Equiv.Loop

namespace SHS.Equiv.VecBridge

/-- In-bounds `Vector.set!` reduces to the bounds-checked `Vector.set`. -/
theorem set_bang_eq_set {α : Type _} {n : Nat} (xs : Vector α n) (i : Nat)
    (h : i < n) (x : α) : xs.set! i x = xs.set i x := by
  ext j hj
  simp only [Vector.set!_eq_setIfInBounds, Vector.getElem_setIfInBounds, Vector.getElem_set]

end SHS.Equiv.VecBridge
