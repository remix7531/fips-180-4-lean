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
mix the freshly-known `W[t]!` into the working variables. -/
def specFusedStep (M : Block) (t : Fin 64) (acc : Schedule × SpecVars) :
    Schedule × SpecVars :=
  let W' := specScheduleStep M t acc.1
  (W', specRoundStep W' t acc.2)

/-! ## Helper lemmas for the write-then-read commutation

These six private lemmas isolate the local frame property of the
schedule update: a step at index `t` only touches `W[t]!`, so any
read at an index `≠ t` sees the old value.  This is the engine that
lets us slide the schedule fold across the round-body fold. -/

/-- Schedule step preserves array size. -/
private theorem size_specScheduleStep (M : Block) (t : Fin 64) (W : Schedule) :
    (specScheduleStep M t W).size = W.size := by
  unfold specScheduleStep
  split <;> simp

/-- `specScheduleStep M t` only modifies index `t.val`; entries at other
indices stay equal. -/
private theorem getElem!_specScheduleStep_ne (M : Block) (t : Fin 64) (W : Schedule)
    (j : Nat) (hj : j ≠ t.val) :
    (specScheduleStep M t W)[j]! = W[j]! := by
  unfold specScheduleStep
  split <;> · simp [Array.getElem!_eq_getD, Ne.symm hj]

/-- The strictly-below specialisation of `getElem!_specScheduleStep_ne`.

This is the form we actually need: in the inductive step we know
`j < k` while the schedule write happens at `k`, so the `≠` is automatic. -/
private theorem getElem!_specScheduleStep_lt (M : Block) (t : Fin 64) (W : Schedule)
    (j : Nat) (hj : j < t.val) :
    (specScheduleStep M t W)[j]! = W[j]! :=
  getElem!_specScheduleStep_ne M t W j (Nat.ne_of_lt hj)

/-- Round step depends on the schedule only through `W[t.val]!`. -/
private theorem specRoundStep_congr_W (W W' : Schedule) (t : Fin 64) (s : SpecVars)
    (h : W[t.val]! = W'[t.val]!) :
    specRoundStep W t s = specRoundStep W' t s := by
  unfold specRoundStep
  rw [h]

/-- Pointwise lift of `specRoundStep_congr_W` to the round-body fold:
if two schedules agree on indices `< n`, folding `specRoundStep` over
`Fin n` against either yields the same result.

This is the inductive engine for `fused_aux`: after `k` fused steps
the partial schedule already agrees with any future extension on
indices `< k`, so the round-body fold over the partial matches the
one over the extended schedule. -/
private theorem foldl_specRoundStep_congr_W (n : Nat) (hn : n ≤ 64)
    (W W' : Schedule) (s₀ : SpecVars)
    (hWW' : ∀ i, i < n → W[i]! = W'[i]!) :
    Fin.foldl n (fun s (i : Fin n) =>
        specRoundStep W ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ s) s₀ =
      Fin.foldl n (fun s (i : Fin n) =>
        specRoundStep W' ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ s) s₀ := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    simp only [Fin.foldl_succ_last]
    have hk : k ≤ 64 := Nat.le_of_succ_le hn
    have hWW'_k : ∀ i, i < k → W[i]! = W'[i]! := fun i hi =>
      hWW' i (Nat.lt_succ_of_lt hi)
    have h_inner :
        Fin.foldl k (fun s (i : Fin k) =>
            specRoundStep W
              ⟨(i.castSucc : Fin (k+1)).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hn⟩ s) s₀ =
          Fin.foldl k (fun s (i : Fin k) =>
            specRoundStep W'
              ⟨(i.castSucc : Fin (k+1)).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hn⟩ s) s₀ :=
      ih hk hWW'_k
    rw [h_inner]
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
because they agree on indices `< k`). -/
private theorem fused_aux (M : Block) (s₀ : SpecVars) :
    ∀ (n : Nat) (hn : n ≤ 64) (W₀ : Schedule),
      Fin.foldl n (fun acc (i : Fin n) =>
          specFusedStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ acc) (W₀, s₀) =
        (Fin.foldl n (fun W (i : Fin n) =>
            specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ W) W₀,
         Fin.foldl n (fun s (i : Fin n) =>
            specRoundStep
              (Fin.foldl n (fun W (j : Fin n) =>
                specScheduleStep M ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ W) W₀)
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ s) s₀) := by
  intro n hn W₀
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    have hk : k ≤ 64 := Nat.le_of_succ_le hn
    -- Peel the last fused step off the LHS.
    rw [show
        Fin.foldl (k+1) (fun acc (i : Fin (k+1)) =>
            specFusedStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ acc) (W₀, s₀)
          = specFusedStep M ⟨(Fin.last k).val,
              Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
              (Fin.foldl k (fun acc (i : Fin k) =>
                specFusedStep M
                  ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ acc)
                (W₀, s₀))
        from Fin.foldl_succ_last _ _]
    -- The three `hcast_*` rewrites collapse the `castSucc` reindexing
    -- (used by `Fin.foldl_succ_last` to expose the inner length-k fold)
    -- back to the plain `Fin k` form expected by the IH.
    have hcast_fused :
        (fun acc (i : Fin k) =>
            specFusedStep M
              ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ acc) =
          (fun acc (i : Fin k) =>
            specFusedStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ acc) := rfl
    rw [hcast_fused]
    rw [ih hk]
    -- Unfold `specFusedStep` on the LHS, exposing `(W', specRoundStep W' …)`.
    show (let W' := specScheduleStep M ⟨(Fin.last k).val,
              Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
            (Fin.foldl k (fun W (i : Fin k) =>
                specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ W) W₀);
          (W', specRoundStep W' ⟨(Fin.last k).val,
                Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
              (Fin.foldl k (fun s (i : Fin k) =>
                  specRoundStep
                    (Fin.foldl k (fun W (j : Fin k) =>
                      specScheduleStep M ⟨j.val,
                        Nat.lt_of_lt_of_le j.isLt hk⟩ W) W₀)
                    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ s) s₀))) = _
    -- Peel the last step off the RHS's outer schedule fold.
    rw [show
        Fin.foldl (k+1) (fun W (i : Fin (k+1)) =>
            specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ W) W₀ =
          specScheduleStep M ⟨(Fin.last k).val,
              Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
              (Fin.foldl k (fun W (i : Fin k) =>
                specScheduleStep M
                  ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ W) W₀)
        from Fin.foldl_succ_last _ _]
    have hcast_sched :
        (fun W (i : Fin k) =>
            specScheduleStep M
              ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ W) =
          (fun W (i : Fin k) =>
            specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ W) := rfl
    rw [hcast_sched]
    -- Peel the last step off the RHS's outer round fold.
    rw [show
        Fin.foldl (k+1) (fun s (i : Fin (k+1)) =>
            specRoundStep
              (specScheduleStep M ⟨(Fin.last k).val, _⟩
                (Fin.foldl k (fun W (j : Fin k) =>
                  specScheduleStep M ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ W) W₀))
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ s) s₀ =
          specRoundStep
            (specScheduleStep M ⟨(Fin.last k).val, Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
              (Fin.foldl k (fun W (j : Fin k) =>
                specScheduleStep M ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ W) W₀))
            ⟨(Fin.last k).val, Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
            (Fin.foldl k (fun s (i : Fin k) =>
              specRoundStep
                (specScheduleStep M ⟨(Fin.last k).val, Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
                  (Fin.foldl k (fun W (j : Fin k) =>
                    specScheduleStep M ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ W) W₀))
                ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ s) s₀)
        from Fin.foldl_succ_last _ _]
    -- Name `Wk` (the k-step partial schedule) and `Wk1` (its one-step extension).
    set Wk : Schedule := Fin.foldl k (fun W (i : Fin k) =>
        specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ W) W₀ with hWk
    set Wk1 : Schedule := specScheduleStep M
        ⟨(Fin.last k).val, Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩ Wk with hWk1
    show (Wk1, specRoundStep Wk1
              ⟨(Fin.last k).val, Nat.lt_of_lt_of_le (Fin.last k).isLt hn⟩
              (Fin.foldl k (fun s (i : Fin k) =>
                  specRoundStep Wk
                    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ s) s₀)) = _
    have hcast_round :
        (fun s (i : Fin k) =>
            specRoundStep Wk1
              ⟨i.castSucc.val, Nat.lt_of_lt_of_le i.castSucc.isLt hn⟩ s) =
          (fun s (i : Fin k) =>
            specRoundStep Wk1 ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ s) := rfl
    rw [hcast_round]
    -- Swap `Wk` for `Wk1` inside the inner round fold (they agree on indices `< k`).
    have hagree : ∀ i, i < k → Wk[i]! = Wk1[i]! := by
      intro i hi
      rw [hWk1]
      exact (getElem!_specScheduleStep_lt M ⟨k, hn⟩ Wk i hi).symm
    rw [foldl_specRoundStep_congr_W k hk Wk Wk1 s₀ hagree]

/-- Spec `compress` in **fused** pure-foldl form: schedule and round
body interleaved in a single fold over `(Schedule, SpecVars)`. -/
def specCompressFused (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64 (fun acc t => specFusedStep M t acc)
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
  -- `fused_aux` at n = 64 wraps each index as `⟨i.val, _⟩`; the `eq_*`
  -- equations strip that wrapping back to bare `Fin 64`.
  have key := fused_aux M (initVars H) 64 (Nat.le_refl 64) (Array.replicate 64 default)
  have eq_fused :
      (fun acc (i : Fin 64) =>
          specFusedStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_refl 64)⟩ acc) =
        (fun acc (t : Fin 64) => specFusedStep M t acc) := by
    funext acc i; congr 1
  have eq_sched :
      (fun W (i : Fin 64) =>
          specScheduleStep M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_refl 64)⟩ W) =
        (fun W (t : Fin 64) => specScheduleStep M t W) := by
    funext W i; congr 1
  rw [eq_fused, eq_sched] at key
  rw [key]
  rw [← schedule_eq_foldl M]

end SHS.Equiv.SHA256.Foldl.Fused
