import equiv.Common.RoundTuple
import equiv.SHA512.Foldl.Model
import spec.HashAlgorithms.SHA512

/-! # Sequential fold for the SHA-512 specification

The proof keeps the precomputed schedule fixed and converts the
elaborated loop state to a vector before transporting the round fold. -/

open SHS.Equiv

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Sequential

open scoped SHS.SHA512

/-- Spec `compress` in **sequential** pure-foldl form: precompute the
full 80-word schedule, then fold the round body over the 80 rounds. -/
def specCompressSeq (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 80
    (fun s (t : Fin 80) => specRoundStep (SHS.SHA512.schedule M) t.val s) (initVars H))

/-- The spec compression computes its schedule before folding the rounds. -/
theorem spec_compress_eq_seq (H : HashValue) (M : Block) :
    SHS.SHA512.compress H M = specCompressSeq H M := by
  unfold specCompressSeq SHS.SHA512.compress
  let initial := RoundTuple.ofVector H
  change (Id.run (forIn' [0:80] initial _) |> RoundTuple.toVector |> addH H) = _
  rw [RoundTuple.forIn'_toVector_eq_foldl 80 initial _ (specRoundStep (SHS.SHA512.schedule M))
    (fun t member _ => by
      simp only [specRoundStep, getElem!_pos SHS.SHA512.K t member.upper,
        getElem!_pos (SHS.SHA512.schedule M) t member.upper]
      rfl)]
  congr 2

end SHS.Equiv.SHA512.Foldl.Sequential
