import equiv.Common.Loop
import equiv.SHA512.Foldl.Model
import spec.HashAlgorithms.SHA512

/-! # Pure-foldl form of the SHA-512 message schedule

The fold combines the spec's 16-word copy and 64-word extension loops. -/

open SHS.Equiv.Loop

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Schedule

open scoped SHS.SHA512

/-- The spec's `schedule` is `Fin.foldl 80 specScheduleStep` over a
zero-initialized 80-word vector.

This rephrases spec's two-`for`-loop schedule as a single
`Fin.foldl 80`, which is the shape we need to match the implementation
and to drive the fused-form argument below. -/
theorem schedule_eq_foldl (M : Block) :
    SHS.SHA512.schedule M =
      Fin.foldl 80 (fun W (t : Fin 80) => specScheduleStep M t.val W)
        (Vector.replicate 80 default) := by
  unfold SHS.SHA512.schedule
  change (forIn' [16:80]
    (Id.run (forIn' [0:16] (Vector.replicate 80 default) _)) _ : Id Schedule).run = _
  refine forIn'_split_eq_Fin_foldl 16 80 (by decide) _ (specScheduleStep M) _ _ ?_ ?_
  · intro t member words
    have inBlock : t < 16 := member.upper
    simp (discharger := omega) only [specScheduleStep, ite_eq_left inBlock, getElem!_pos,
      SHS.Equiv.VecBridge.set_bang_eq_set]
  · intro t member words
    have afterBlock : 16 ≤ t := member.lower
    have inSchedule : t < 80 := member.upper
    simp (discharger := omega) only [specScheduleStep, ite_eq_right, getElem!_pos,
      SHS.Equiv.VecBridge.set_bang_eq_set]

end SHS.Equiv.SHA512.Foldl.Schedule
