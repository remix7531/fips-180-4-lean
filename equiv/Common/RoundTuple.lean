import equiv.Common.Loop

namespace SHS.Equiv

/-- Lean elaborates the eight mutable round variables as a right-associated product. -/
abbrev RoundTuple (α : Type _) := α × α × α × α × α × α × α × α

namespace RoundTuple

/-- Pack the working vector in the order used by the elaborated loop. -/
def ofVector {α : Type _} (words : Vector α 8) : RoundTuple α :=
  ⟨words[0], words[1], words[2], words[3], words[4], words[5], words[6], words[7]⟩

/-- Read the elaborated loop state as a working vector. -/
def toVector {α : Type _} (words : RoundTuple α) : Vector α 8 :=
  #v[words.1, words.2.1, words.2.2.1, words.2.2.2.1, words.2.2.2.2.1,
     words.2.2.2.2.2.1, words.2.2.2.2.2.2.1, words.2.2.2.2.2.2.2]

theorem toVector_ofVector {α : Type _} (words : Vector α 8) :
    (ofVector words).toVector = words :=
  Vector.ofFn_getElem (xs := words)

/-- Recover the vector fold when each elaborated iteration applies the vector round step. -/
theorem forIn'_toVector_eq_foldl {α : Type _} (n : Nat) (initial : RoundTuple α)
    (body : (t : Nat) → t ∈ [0:n] → RoundTuple α → Id (ForInStep (RoundTuple α)))
    (step : Nat → Vector α 8 → Vector α 8)
    (agrees : ∀ t member working,
      body t member working = pure (ForInStep.yield (ofVector (step t working.toVector)))) :
    (Id.run (forIn' [0:n] initial body)).toVector =
      Fin.foldl n (fun state t => step t.val state) initial.toVector := by
  let round (t : Nat) (working : RoundTuple α) := ofVector (step t working.toVector)
  rw [forIn'_eq_forIn _ _ body (fun t working => pure (ForInStep.yield (round t working))) agrees,
    Loop.forIn_id_eq_Fin_foldl n initial round]
  exact Loop.fin_foldl_transport n (fun working t => round t.val working)
    (fun state t => step t.val state) toVector initial (fun _ _ => toVector_ofVector _)

end RoundTuple
end SHS.Equiv
