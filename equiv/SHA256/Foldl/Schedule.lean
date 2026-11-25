import equiv.Common.Loop
import equiv.SHA256.Foldl.Model
import spec.HashAlgorithms.SHA256

/-! # Pure-foldl form of the spec message schedule

The spec's copy and extension loops become one fold over `specScheduleStep`. -/

open SHS.Equiv.Loop

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Schedule

open scoped SHS.SHA256

/-- The spec's `schedule` is `Fin.foldl 64 specScheduleStep` over a
zero-initialized 64-word vector.

This rephrases spec's two-`for`-loop schedule as a single
`Fin.foldl 64`, which is the shape we need to match the implementation
and to drive the fused-form argument below. -/
theorem schedule_eq_foldl (M : Block) :
    SHS.SHA256.schedule M =
      Fin.foldl 64 (fun W (t : Fin 64) => specScheduleStep M t.val W)
        (Vector.replicate 64 default) := by
  unfold SHS.SHA256.schedule
  change (forIn' [16:64]
    (Id.run (forIn' [0:16] (Vector.replicate 64 default) _)) _ : Id Schedule).run = _
  refine forIn'_split_eq_Fin_foldl 16 64 (by decide) _ (specScheduleStep M) _ _ ?_ ?_
  · intro t member words
    have inBlock : t < 16 := member.upper
    simp (discharger := omega) only [specScheduleStep, ite_eq_left inBlock, getElem!_pos,
      SHS.Equiv.VecBridge.set_bang_eq_set]
  · intro t member words
    have afterBlock : 16 ≤ t := member.lower
    have inSchedule : t < 64 := member.upper
    simp (discharger := omega) only [specScheduleStep, ite_eq_right, getElem!_pos,
      SHS.Equiv.VecBridge.set_bang_eq_set]

end SHS.Equiv.SHA256.Foldl.Schedule
