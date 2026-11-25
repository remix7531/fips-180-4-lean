import equiv.Common.RoundTuple
import equiv.SHA256.Foldl.Model
import spec.HashAlgorithms.SHA256

/-! # Sequential fold for the SHA-256 specification

The proof keeps the precomputed schedule fixed and converts the
elaborated loop state to a vector before transporting the round fold. -/

open SHS.Equiv

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Sequential

open scoped SHS.SHA256

/-- Spec `compress` in **sequential** pure-foldl form: precompute the
full schedule, then fold the round body over the 64 rounds. -/
def specCompressSeq (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64
    (fun s (t : Fin 64) => specRoundStep (SHS.SHA256.schedule M) t.val s) (initVars H))

/-- The spec compression computes its schedule before folding the rounds. -/
theorem spec_compress_eq_seq (H : HashValue) (M : Block) :
    SHS.SHA256.compress H M = specCompressSeq H M := by
  unfold specCompressSeq SHS.SHA256.compress
  let initial := RoundTuple.ofVector H
  change (Id.run (forIn' [0:64] initial _) |> RoundTuple.toVector |> addH H) = _
  rw [RoundTuple.forIn'_toVector_eq_foldl 64 initial _ (specRoundStep (SHS.SHA256.schedule M))
    (fun t member _ => by
      simp only [specRoundStep, getElem!_pos SHS.SHA256.K t member.upper,
        getElem!_pos (SHS.SHA256.schedule M) t member.upper]
      rfl)]
  congr 2

end SHS.Equiv.SHA256.Foldl.Sequential
