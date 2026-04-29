import equiv.Common.Loop
import impl.SHA256
import spec.HashAlgorithms

/-! # Pure-foldl form of the spec message schedule

The spec writes `SHS.SHA256.schedule` as `Id.run do { mut … for … }`
across two `for` loops.  This module restates it as a single
`Fin.foldl 64` over a pure step function (`specScheduleStep`), which
is the shape everything downstream wants.

Nothing in this file references the round body or the working
variables; that lives in `Foldl/Sequential.lean` and `Foldl/Fused.lean`. -/

open SHS.Equiv.Loop

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Schedule

open scoped SHS.SHA256

/-- One step of the spec's message schedule, as a pure function.

For `t < 16`, copy block word `t`; otherwise, mix four prior words via
`smallSigma0`/`smallSigma1`.  This is exactly the body of the two
`for` loops in `SHS.SHA256.schedule`.

Indexed by `Nat` rather than `Fin 64`: out-of-range `t` panics through
`Array.set!`, but every call site has `t < 64`.  The `Nat` index keeps
the `Fused.lean` proof free of `Fin.castSucc`-handling. -/
def specScheduleStep (M : Block) (t : Nat) (W : Schedule) : Schedule :=
  if t < 16 then
    W.set! t M[t]!
  else
    W.set! t
      (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
        SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!)

/-- The spec's `schedule` is `Fin.foldl 64 specScheduleStep` over a
zero-initialized 64-word array.

This rephrases spec's two-`for`-loop schedule as a single
`Fin.foldl 64`, which is the shape we need to match the implementation
and to drive the fused-form argument below. -/
theorem schedule_eq_foldl (M : Block) :
    SHS.SHA256.schedule M =
      Fin.foldl 64 (fun W (t : Fin 64) => specScheduleStep M t.val W)
        (Array.replicate 64 default) := by
  -- Split the foldl at t = 16, matching the two `for` loops of `SHS.SHA256.schedule`.
  have hsplit :
      Fin.foldl 64 (fun W t => specScheduleStep M t W) (Array.replicate 64 default) =
        Fin.foldl 48
          (fun W (i : Fin 48) =>
            W.set! (i.val + 16)
              (SHS.SHA256.smallSigma1 W[i.val + 16 - 2]! + W[i.val + 16 - 7]! +
                SHS.SHA256.smallSigma0 W[i.val + 16 - 15]! + W[i.val + 16 - 16]!))
          (Fin.foldl 16 (fun W (i : Fin 16) => W.set! i.val M[i.val]!)
            (Array.replicate 64 default)) := by
    unfold specScheduleStep
    rw [fin_foldl_split 16 64 (by decide)
          (fun n (W : Schedule) => W.set! n M[n]!)
          (fun n (W : Schedule) => W.set! n
            (SHS.SHA256.smallSigma1 W[n - 2]! + W[n - 7]! +
              SHS.SHA256.smallSigma0 W[n - 15]! + W[n - 16]!))]
  rw [hsplit]
  -- Re-fuse the two halves back into the `forIn`-form spec actually uses.
  rw [← forIn_id_eq_Fin_foldl 16
        (Array.replicate 64 default)
        (fun n W => W.set! n M[n]!)]
  rw [← forIn_id_eq_Fin_foldl_offset 16 64
        (Id.run (forIn [0:16] (Array.replicate 64 default)
          (fun t W => pure (ForInStep.yield (W.set! t M[t]!)))))
        (fun n W => W.set! n
          (SHS.SHA256.smallSigma1 W[n - 2]! + W[n - 7]! +
            SHS.SHA256.smallSigma0 W[n - 15]! + W[n - 16]!))]
  rfl

end SHS.Equiv.SHA256.Foldl.Schedule
