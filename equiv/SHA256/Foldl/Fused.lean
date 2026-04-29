import equiv.SHA256.Foldl.Schedule
import equiv.SHA256.Foldl.Sequential

/-! # Pure-foldl form of the spec compression — fused

Restates `SHS.SHA256.compress` as a single `Fin.foldl 64` over
`(Schedule, SpecVars)` whose step interleaves one schedule update with
one round-body iteration.  This is the shape that meets the
implementation's compress in `Compress.lean`.

The fused form agrees with the sequential form because `specRoundStep`
at index `t` only reads `W[t]!`, which is exactly the entry written by
`specScheduleStep` at the same step.  Equivalently: writes at index
`t` and reads at indices `≤ t` commute past one another. -/

open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Fused

open scoped SHS.SHA256

/-- One full step in fused form: update the schedule at index `t`, then
mix the freshly-known `W[t]!` into the working variables.  Indexed by
`Nat`, like `specScheduleStep` and `specRoundStep`. -/
def specFusedStep (M : Block) (t : Nat) (acc : Schedule × SpecVars) :
    Schedule × SpecVars :=
  let W' := specScheduleStep M t acc.1
  (W', specRoundStep W' t acc.2)

/-! ## Helper lemmas for the write-then-read commutation

These four private lemmas isolate the local frame property of the
schedule update: a step at index `t` only touches `W[t]!`, so any
read at an index `≠ t` sees the old value.  This is the engine that
lets us slide the schedule fold across the round-body fold. -/

/-- `specScheduleStep M t` only modifies index `t`; entries at other
indices stay equal. -/
theorem getElem!_specScheduleStep_ne (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j ≠ t) :
    (specScheduleStep M t W)[j]! = W[j]! := by
  unfold specScheduleStep
  split <;> · simp [Array.getElem!_eq_getD, Ne.symm hj]

/-- The strictly-below specialisation of `getElem!_specScheduleStep_ne`.

This is the form we actually need: in the inductive step we know
`j < k` while the schedule write happens at `k`, so the `≠` is automatic. -/
theorem getElem!_specScheduleStep_lt (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j < t) :
    (specScheduleStep M t W)[j]! = W[j]! :=
  getElem!_specScheduleStep_ne M t W j (Nat.ne_of_lt hj)

/-- Round step depends on the schedule only through `W[t]!`. -/
private theorem specRoundStep_congr_W (W W' : Schedule) (t : Nat) (s : SpecVars)
    (h : W[t]! = W'[t]!) :
    specRoundStep W t s = specRoundStep W' t s := by
  unfold specRoundStep
  rw [h]

/-- Pointwise lift of `specRoundStep_congr_W` to the round-body fold:
if two schedules agree on indices `< n`, folding `specRoundStep` over
`Fin n` against either yields the same result. -/
private theorem foldl_specRoundStep_congr_W : ∀ (n : Nat)
    (W W' : Schedule) (s₀ : SpecVars)
    (_hWW' : ∀ i, i < n → W[i]! = W'[i]!),
    Fin.foldl n (fun s (i : Fin n) => specRoundStep W i.val s) s₀ =
      Fin.foldl n (fun s (i : Fin n) => specRoundStep W' i.val s) s₀
  | 0, _, _, _, _ => by simp [Fin.foldl_zero]
  | k + 1, W, W', s₀, hWW' => by
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    show specRoundStep W _ (Fin.foldl k (fun s (i : Fin k) => specRoundStep W i.val s) s₀)
       = specRoundStep W' _ (Fin.foldl k (fun s (i : Fin k) => specRoundStep W' i.val s) s₀)
    rw [foldl_specRoundStep_congr_W k W W' s₀
        (fun i hi => hWW' i (Nat.lt_succ_of_lt hi))]
    apply specRoundStep_congr_W
    exact hWW' k (Nat.lt_succ_self k)

/-- The joint inductive invariant for the fused fold: after `n` steps,
the result splits componentwise into (1) the schedule fold alone and
(2) the round fold against the *partial* schedule we just built.

**Why:** This is the heart of the fused-vs-sequential equivalence.
At `n = 64` the partial schedule is the full one, so the round fold
in the second component is exactly `specCompressSeq`'s round fold.

**How:** Induction on `n`.  The `succ k` step uses
`Fin.foldl_succ_last` to peel the last iteration off all three folds,
applies the IH to the inner fused fold, then uses
`getElem!_specScheduleStep_lt` together with
`foldl_specRoundStep_congr_W` to swap the partial schedule `W_k` for
its one-step extension `W_{k+1}` inside the inner round fold (legal
because they agree on indices `< k`).

The `Nat`-indexed step functions (`specScheduleStep`, `specRoundStep`,
`specFusedStep`) eliminate the `Fin.castSucc` plumbing that would
otherwise dominate this proof. -/
private theorem fused_aux (M : Block) (s₀ : SpecVars) :
    ∀ (n : Nat) (W₀ : Schedule),
      Fin.foldl n (fun acc (i : Fin n) => specFusedStep M i.val acc) (W₀, s₀) =
        (Fin.foldl n (fun W (i : Fin n) => specScheduleStep M i.val W) W₀,
         Fin.foldl n (fun s (i : Fin n) =>
            specRoundStep
              (Fin.foldl n (fun W (j : Fin n) => specScheduleStep M j.val W) W₀)
              i.val s) s₀) := by
  intro n W₀
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, Fin.foldl_succ_last]
    -- Strip the `i.castSucc.val ↦ i.val` reindexing on every inner fold;
    -- both forms are `rfl`-equal because `(i : Fin k).castSucc.val = i.val`.
    show specFusedStep M _
        (Fin.foldl k (fun acc (i : Fin k) => specFusedStep M i.val acc) (W₀, s₀)) =
      (specScheduleStep M _
          (Fin.foldl k (fun W (i : Fin k) => specScheduleStep M i.val W) W₀),
       specRoundStep
          (specScheduleStep M _
            (Fin.foldl k (fun W (i : Fin k) => specScheduleStep M i.val W) W₀))
          _
          (Fin.foldl k (fun s (i : Fin k) =>
              specRoundStep
                (specScheduleStep M (Fin.last k).val
                  (Fin.foldl k (fun W (j : Fin k) => specScheduleStep M j.val W) W₀))
                i.val s) s₀))
    rw [ih]
    unfold specFusedStep
    set Wk : Schedule := Fin.foldl k
        (fun W (i : Fin k) => specScheduleStep M i.val W) W₀ with hWk
    set Wk1 : Schedule := specScheduleStep M (Fin.last k).val Wk with hWk1
    -- Inside the inner round fold, swap `Wk` for `Wk1` (they agree on `< k`).
    have hagree : ∀ i, i < k → Wk[i]! = Wk1[i]! := fun i hi =>
      (getElem!_specScheduleStep_lt M (Fin.last k).val Wk i (by simpa using hi)).symm
    rw [foldl_specRoundStep_congr_W k Wk Wk1 s₀ hagree]

/-- Spec `compress` in **fused** pure-foldl form: schedule and round
body interleaved in a single fold over `(Schedule, SpecVars)`. -/
def specCompressFused (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64 (fun acc (t : Fin 64) => specFusedStep M t.val acc)
    (Array.replicate 64 default, initVars H)).2

/-- The spec's `compress` equals its fused pure-foldl form
(`specCompressFused`).  This is the shape needed to match the
implementation, which fuses the schedule and round body into a single
64-iteration loop. -/
theorem spec_compress_eq_fused (H : HashValue) (M : Block) :
    SHS.SHA256.compress H M = specCompressFused H M := by
  unfold specCompressFused
  rw [spec_compress_eq_seq H M]
  unfold specCompressSeq
  congr 1
  rw [fused_aux M (initVars H) 64 (Array.replicate 64 default)]
  rw [← schedule_eq_foldl M]

end SHS.Equiv.SHA256.Foldl.Fused
