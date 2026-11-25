import equiv.Common.FusedFold
import equiv.SHA256.Foldl.Schedule
import equiv.SHA256.Foldl.Sequential

/-! # Pure-foldl form of the spec compression — fused

Restates `SHS.SHA256.compress` as a single `Fin.foldl 64` over
`(Schedule, SpecVars)` whose step interleaves one schedule update with
one round-body iteration.  This is the shape that meets the
implementation's compress in `Compress/Match.lean`.

The fused form agrees with the sequential form because `specRoundStep`
at index `t` only reads `W[t]!`, which is exactly the entry written by
`specScheduleStep` at that step. The write leaves all earlier round
inputs intact. -/

open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential
open SHS.Equiv.FusedFold

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Fused

open scoped SHS.SHA256

/-- The spec's `compress` equals its fused pure-foldl form
(`specCompressFused`).  This is the shape needed to match the
implementation, which fuses the schedule and round body into a single
64-iteration loop. -/
theorem spec_compress_eq_fused (H : HashValue) (M : Block) :
    SHS.SHA256.compress H M = specCompressFused H M := by
  unfold specCompressFused
  rw [spec_compress_eq_seq H M]
  unfold specCompressSeq specFusedStep
  apply congrArg (addH H)
  rw [foldl_update_then_round (specScheduleStep M) specRoundStep]
  · rw [← schedule_eq_foldl M]
  · intro W written read state earlier
    unfold specRoundStep
    rw [getElem!_specScheduleStep_lt M written W read earlier]

end SHS.Equiv.SHA256.Foldl.Fused
