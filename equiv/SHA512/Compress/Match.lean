import equiv.SHA512.Compress.Impl
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 compression equivalence — `MatchAfter` invariant + cross-side meet

Parallel to `equiv/SHA256/Compress/Match.lean` at 80 rounds, 64-bit words. -/

open SHS.Equiv.SHA512.Bridge
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Functions
open SHS.Equiv.SHA512.Constants
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Compress.Impl

open SHS.SHA512

namespace SHS.Equiv.SHA512.Compress.Match

open scoped SHS.SHA512

structure MatchAfter
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) : Prop where
  wsize : W.size = 80
  vars : ∀ k : Fin 8, impl_state[k].toBitVec = vars[k]
  ring : ∀ k : Nat, k < n → n ≤ k + 16 →
    (impl_block[k % 16]'(mod16_lt _)).toBitVec
      = W[k]!
  untouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k]

theorem MatchAfter_zero
    (state : Impl.State) (block : Impl.Block) :
    MatchAfter block block state (Vector.replicate 80 default)
      (initVars (toSpecState state)) 0 where
  wsize := by simp
  vars k := by rw [initVars_toSpecState_getElem]
  ring k hk _ := by omega
  untouched k _ := rfl

theorem MatchAfter_step
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) (hn : n < 80)
    (h : MatchAfter block₀ impl_block impl_state W vars n) :
    let i : Fin 80 := ⟨n, hn⟩
    let next_impl := implFusedStep i (impl_block, impl_state)
    let next_spec := specFusedStep (toSpecBlock block₀) i (W, vars)
    MatchAfter block₀ next_impl.1 next_impl.2 next_spec.1 next_spec.2 (n + 1) := by
  have hWsize := h.wsize
  have hstate := h.vars
  have hring := h.ring
  have huntouched := h.untouched
  simp only [implFusedStep, specFusedStep]
  refine ⟨?sched_size, ?vars_match, ?ring_match, ?untouched⟩
  case sched_size =>
    unfold specScheduleStep; split <;> simp [hWsize]
  case vars_match =>
    have hw := implScheduleStep_value_match block₀ impl_block W n hn huntouched hring
    have h0 : impl_state[(0 : Nat)].toBitVec = vars[(0 : Nat)] := hstate 0
    have h1 : impl_state[(1 : Nat)].toBitVec = vars[(1 : Nat)] := hstate 1
    have h2 : impl_state[(2 : Nat)].toBitVec = vars[(2 : Nat)] := hstate 2
    have h3 : impl_state[(3 : Nat)].toBitVec = vars[(3 : Nat)] := hstate 3
    have h4 : impl_state[(4 : Nat)].toBitVec = vars[(4 : Nat)] := hstate 4
    have h5 : impl_state[(5 : Nat)].toBitVec = vars[(5 : Nat)] := hstate 5
    have h6 : impl_state[(6 : Nat)].toBitVec = vars[(6 : Nat)] := hstate 6
    have h7 : impl_state[(7 : Nat)].toBitVec = vars[(7 : Nat)] := hstate 7
    have hK := K64_toBitVec_nat n hn
    intro k
    have ⟨k_val, _k_lt⟩ := k
    interval_cases k_val <;>
      (unfold implRoundBody specRoundStep
       simp only [Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
         List.getElem_cons_zero, List.getElem_cons_succ,
         toBitVec_add, ← bigSigma1_toBitVec, ← bigSigma0_toBitVec,
         ← Ch_toBitVec, ← Maj_toBitVec, hw, hK]
       try assumption
       try (simp only [h0, h1, h2, h3, h4, h5, h6, h7]; ac_rfl))
  case ring_match =>
    intro k hk1 hk2
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk1) with hk_lt | hk_eq
    · have hkn : k ≠ n := Nat.ne_of_lt hk_lt
      have hold := hring k hk_lt (by omega)
      have hkW : k < W.size := by simp only [hWsize]; omega
      have hk80 : k < 80 := by simp at hkW; exact hkW
      have hn80 : n < 80 := hn
      have hspec_k : (specScheduleStep (toSpecBlock block₀) n W)[k]! = W[k]! := by
        unfold specScheduleStep
        have hsize_post : ∀ v : Word, k < (W.set! n v).toArray.size := by
          intro v; simp; exact hk80
        rw [getElem!_pos _ k hkW]
        split
        · rw [getElem!_pos _ k hk80]
          rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn80,
              Vector.getElem_set_ne hn80 hk80 hkn.symm]
        · rw [getElem!_pos _ k hk80]
          rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn80,
              Vector.getElem_set_ne hn80 hk80 hkn.symm]
      rw [hspec_k]
      by_cases hn16 : n < 16
      · unfold implScheduleStep
        rw [dif_pos hn16]
        exact hold
      · push Not at hn16
        unfold implScheduleStep
        rw [dif_neg (show ¬ (⟨n, hn⟩ : Fin 80).val < 16 by simpa using hn16)]
        have hk_mod : k % 16 ≠ n % 16 := by omega
        rw [Vector.getElem_set_ne (by omega) (by omega) (Ne.symm hk_mod)]
        exact hold
    · cases hk_eq
      have hself := implScheduleStep_fst_at_self ⟨n, hn⟩ impl_block
      have hval := implScheduleStep_value_match block₀ impl_block W n hn
                     huntouched hring
      rw [hself]
      exact hval
  case untouched =>
    intro k hk
    have hn16 : n < 16 := by have := k.isLt; omega
    unfold implScheduleStep
    rw [dif_pos hn16]
    exact huntouched k (by omega)

theorem MatchAfter_iter
    (state : Impl.State) (block : Impl.Block)
    (n : Nat) (hn : n ≤ 80) :
    let impl_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        implFusedStep ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ acc) (block, state)
    let spec_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        specFusedStep (toSpecBlock block) i.val acc)
        (Vector.replicate 80 default, initVars (toSpecState state))
    MatchAfter block impl_acc.1 impl_acc.2 spec_acc.1 spec_acc.2 n := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero]
    exact MatchAfter_zero state block
  | succ k ih =>
    have hk : k ≤ 80 := by omega
    have hk_lt : k < 80 := by omega
    have ih' := ih hk
    simp only [Fin.foldl_succ_last] at *
    convert MatchAfter_step block _ _ _ _ k hk_lt ih' using 1

theorem toSpecState_implCompressFoldl
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  have hvars := (MatchAfter_iter state block 80 (le_refl 80)).vars
  have hvars' : ∀ (k : Nat) (hk : k < 8),
      ((Fin.foldl 80 (fun acc (i : Fin 80) => implFusedStep i acc)
        (block, state)).2[k]'hk).toBitVec =
      ((Fin.foldl 80
          (fun acc (t : Fin 80) => specFusedStep (toSpecBlock block) t.val acc)
        (Vector.replicate 80 default, initVars (toSpecState state))).2[k]'hk) := by
    intro k hk
    have := hvars ⟨k, hk⟩
    convert this using 2
  have getElem!_lit : ∀ (k : Nat) (h : k < 8),
      (state.map UInt64.toBitVec)[k]! = (state[k]'h).toBitVec := by
    intro k h
    have := getElem!_toSpecState state ⟨k, h⟩
    simpa [toSpecState] using this
  apply Vector.ext
  intro k hk
  unfold implCompressFoldl specCompressFused addH toSpecState
  rw [Vector.getElem_map, Vector.getElem_zipWith, toBitVec_add]
  rw [hvars' k hk]
  interval_cases k <;> (simp; ac_rfl)

end SHS.Equiv.SHA512.Compress.Match
