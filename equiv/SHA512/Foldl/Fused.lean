import equiv.Common.FusedFold
import equiv.SHA512.Foldl.Schedule
import equiv.SHA512.Foldl.Sequential

/-! # Pure-foldl form of the SHA-512 spec compression — fused

Parallel to `equiv/SHA256/Foldl/Fused.lean` at 80 rounds, 64-bit words.

Restates `SHS.SHA512.compress` as a single `Fin.foldl 80` over
`(Schedule, SpecVars)` whose step interleaves one schedule update with
one round-body iteration.

The fused form agrees with the sequential form because `specRoundStep`
at index `t` only reads `W[t]!`, which is exactly the entry written by
`specScheduleStep` at that step. The write leaves all earlier round
inputs intact. -/

open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.FusedFold

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Fused

open scoped SHS.SHA512

/-- The spec's `compress` equals its fused pure-foldl form
(`specCompressFused`), which interleaves schedule updates and rounds. -/
theorem spec_compress_eq_fused (H : HashValue) (M : Block) :
    SHS.SHA512.compress H M = specCompressFused H M := by
  unfold specCompressFused
  rw [spec_compress_eq_seq H M]
  unfold specCompressSeq specFusedStep
  apply congrArg (addH H)
  rw [foldl_update_then_round (specScheduleStep M) specRoundStep]
  · rw [← schedule_eq_foldl M]
  · intro W written read state earlier
    unfold specRoundStep
    rw [getElem!_specScheduleStep_lt M written W read earlier]

end SHS.Equiv.SHA512.Foldl.Fused
