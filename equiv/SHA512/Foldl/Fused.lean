import equiv.SHA512.Foldl.Schedule
import equiv.SHA512.Foldl.Sequential

/-! # Pure-foldl form of the SHA-512 spec compression — fused

Parallel to `equiv/SHA256/Foldl/Fused.lean` at 80 rounds, 64-bit words. -/

open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Fused

open scoped SHS.SHA512

def specFusedStep (M : Block) (t : Nat) (acc : Schedule × SpecVars) :
    Schedule × SpecVars :=
  let W' := specScheduleStep M t acc.1
  (W', specRoundStep W' t acc.2)

theorem getElem!_specScheduleStep_ne (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j ≠ t) :
    (specScheduleStep M t W)[j]! = W[j]! := by
  have key : ∀ (v : BitVec 64), (W.set! t v)[j]! = W[j]! := by
    intro v
    by_cases hj' : j < 80
    · rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ hj',
          SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ hj']
      by_cases ht : t < 80
      · rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ ht, Vector.getElem_set,
            if_neg (Ne.symm hj)]
      · have hwid : W.set! t v = W := by
          apply Vector.toArray_inj.mp
          simp [Vector.toArray_set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          intro h; grind
        rw [hwid]
    · simp [getElem!_neg, hj']
  unfold specScheduleStep
  split <;> apply key

theorem getElem!_specScheduleStep_lt (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j < t) :
    (specScheduleStep M t W)[j]! = W[j]! :=
  getElem!_specScheduleStep_ne M t W j (Nat.ne_of_lt hj)

private theorem specRoundStep_congr_W (W W' : Schedule) (t : Nat) (s : SpecVars)
    (h : W[t]! = W'[t]!) :
    specRoundStep W t s = specRoundStep W' t s := by
  unfold specRoundStep
  rw [h]

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
    have hagree : ∀ i, i < k → Wk[i]! = Wk1[i]! := fun i hi =>
      (getElem!_specScheduleStep_lt M (Fin.last k).val Wk i (by simpa using hi)).symm
    rw [foldl_specRoundStep_congr_W k Wk Wk1 s₀ hagree]

def specCompressFused (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 80 (fun acc (t : Fin 80) => specFusedStep M t.val acc)
    (Vector.replicate 80 default, initVars H)).2

theorem spec_compress_eq_fused (H : HashValue) (M : Block) :
    SHS.SHA512.compress H M = specCompressFused H M := by
  unfold specCompressFused
  rw [spec_compress_eq_seq H M]
  unfold specCompressSeq
  congr 1
  rw [fused_aux M (initVars H) 80 (Vector.replicate 80 default)]
  rw [← schedule_eq_foldl M]

end SHS.Equiv.SHA512.Foldl.Fused
