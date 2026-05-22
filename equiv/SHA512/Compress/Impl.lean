import equiv.SHA512.Lift
import equiv.SHA512.Functions
import equiv.SHA512.Constants
import equiv.SHA512.Foldl.Fused
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 compression equivalence — implementation-side factoring

Parallel to `equiv/SHA256/Compress/Impl.lean` at 80 rounds, 64-bit words. -/

open SHS.Equiv.SHA512.Bridge
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Functions
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential

open SHS.SHA512

namespace SHS.Equiv.SHA512.Compress.Impl

open scoped SHS.SHA512

/-- The ring-buffer index bound used at every schedule-step site. -/
theorem mod16_lt (k : Nat) : k % 16 < 16 := Nat.mod_lt _ (by decide)

/-! ## Implementation-side factoring -/

def implScheduleStep (i : Fin 80) (block : Impl.Block) : Impl.Block × UInt64 :=
  if hi : i.val < 16 then
    (block, block[i.val]'hi)
  else
    let w15 := block[(i.val - 15) % 16]'(by omega)
    let s0  := (Impl.UInt64.rotr w15 1) ^^^ (Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
    let w2  := block[(i.val - 2) % 16]'(by omega)
    let s1  := (Impl.UInt64.rotr w2 19) ^^^ (Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
    let w16 := block[(i.val - 16) % 16]'(by omega)
    let w7  := block[(i.val - 7) % 16]'(by omega)
    let new := w16 + s0 + w7 + s1
    (block.set ((i.val) % 16) new (by omega), new)

def implRoundBody (i : Fin 80) (w : UInt64) (s : Impl.State) : Impl.State :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let s1 := (Impl.UInt64.rotr e 14) ^^^ (Impl.UInt64.rotr e 18) ^^^ (Impl.UInt64.rotr e 41)
  let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
  let t1 := s1 + ch + Impl.K64[i] + w + h
  let s0 := (Impl.UInt64.rotr a 28) ^^^ (Impl.UInt64.rotr a 34) ^^^ (Impl.UInt64.rotr a 39)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let t2 := s0 + mj
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

def implFusedStep (i : Fin 80) (acc : Impl.Block × Impl.State) :
    Impl.Block × Impl.State :=
  let (block', w) := implScheduleStep i acc.1
  (block', implRoundBody i w acc.2)

def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let (_, s') := Fin.foldl 80 (fun acc i => implFusedStep i acc) (block, state)
  Vector.zipWith (· + ·) state s'

private theorem zipWith_add_eq_mk (state s' : Impl.State) :
    Vector.zipWith (· + ·) state s' =
      #v[ state[0] + s'[0], state[1] + s'[1], state[2] + s'[2], state[3] + s'[3],
          state[4] + s'[4], state[5] + s'[5], state[6] + s'[6], state[7] + s'[7] ] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp

private def roundStateToPair (rs : Impl.RoundState) : Impl.Block × Impl.State :=
  (rs.schedule, #v[rs.a, rs.b, rs.c, rs.d, rs.e, rs.f, rs.g, rs.h])

private theorem fin_foldl_hom {α β : Type _} : ∀ {n : Nat}
    (f : α → β) (g : α → Fin n → α) (h : β → Fin n → β),
    (∀ a i, f (g a i) = h (f a) i) → ∀ (init : α),
    f (Fin.foldl n g init) = Fin.foldl n h (f init)
  | 0, _, _, _, _, _ => by simp [Fin.foldl_zero]
  | m + 1, f, g, h, step_eq, init => by
    rw [Fin.foldl_succ, Fin.foldl_succ]
    rw [fin_foldl_hom f (fun x (j : Fin m) => g x j.succ)
                       (fun x (j : Fin m) => h x j.succ)
          (fun a j => step_eq a j.succ) (g init 0)]
    rw [step_eq init 0]

private theorem roundStep_corresponds (rs : Impl.RoundState) (i : Fin 80) :
    roundStateToPair (Impl.roundStep rs i) = implFusedStep i (roundStateToPair rs) := by
  unfold roundStateToPair Impl.roundStep implFusedStep implScheduleStep implRoundBody
  apply Prod.ext
  · rfl
  · apply Vector.ext
    intro k hk
    interval_cases k <;> rfl

private theorem impl_compress_eq_foldl_form (state : Impl.State) (block : Impl.Block) :
    Impl.compress state block =
      let final := Fin.foldl 80 Impl.roundStep (Impl.RoundState.ofState state block)
      #v[ state[0] + final.a, state[1] + final.b, state[2] + final.c, state[3] + final.d,
          state[4] + final.e, state[5] + final.f, state[6] + final.g, state[7] + final.h ] := by
  unfold Impl.compress
  simp only [SHS.Impl.Unroll.unroll80_eq_foldl]

theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := by
  rw [impl_compress_eq_foldl_form]
  unfold implCompressFoldl
  have h_fold := fin_foldl_hom (n := 80) roundStateToPair
    Impl.roundStep (fun acc i => implFusedStep i acc)
    roundStep_corresponds (Impl.RoundState.ofState state block)
  have h_init : roundStateToPair (Impl.RoundState.ofState state block) = (block, state) := by
    unfold roundStateToPair Impl.RoundState.ofState
    apply Prod.ext
    · rfl
    · apply Vector.ext
      intro k hk
      interval_cases k <;> rfl
  rw [h_init] at h_fold
  set final_rs := Fin.foldl 80 Impl.roundStep
    (Impl.RoundState.ofState state block)
  set final_pair := Fin.foldl 80 (fun acc i => implFusedStep i acc) (block, state)
  show Vector.zipWith (fun x1 x2 => x1 + x2) state final_pair.2 =
    #v[ state[0] + final_rs.a, state[1] + final_rs.b, state[2] + final_rs.c, state[3] + final_rs.d,
        state[4] + final_rs.e, state[5] + final_rs.f, state[6] + final_rs.g, state[7] + final_rs.h ]
  have h_pair_eq : final_pair.2 =
      #v[final_rs.a, final_rs.b, final_rs.c, final_rs.d,
         final_rs.e, final_rs.f, final_rs.g, final_rs.h] := by
    have h := h_fold
    unfold roundStateToPair at h
    exact congrArg Prod.snd h.symm
  rw [h_pair_eq, zipWith_add_eq_mk]
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-! ## Per-step bridges -/

theorem initVars_toSpecState_getElem (state : Impl.State) (k : Fin 8) :
    (initVars (toSpecState state))[k] = state[k].toBitVec := by
  simp [initVars, toSpecState, getElem!_pos]

theorem implScheduleStep_value_ge_16
    (i : Fin 80) (impl_block : Impl.Block) (W : Schedule) (hi : 16 ≤ i.val)
    (h2 : (impl_block[(i.val - 2) % 16]'(by omega)).toBitVec = W[i.val - 2]!)
    (h7 : (impl_block[(i.val - 7) % 16]'(by omega)).toBitVec = W[i.val - 7]!)
    (h15 : (impl_block[(i.val - 15) % 16]'(by omega)).toBitVec = W[i.val - 15]!)
    (h16 : (impl_block[(i.val - 16) % 16]'(by omega)).toBitVec = W[i.val - 16]!) :
    (implScheduleStep i impl_block).2.toBitVec =
      SHS.SHA512.smallSigma1 W[i.val - 2]! + W[i.val - 7]! +
        SHS.SHA512.smallSigma0 W[i.val - 15]! + W[i.val - 16]! := by
  unfold implScheduleStep
  rw [dif_neg (by omega : ¬ i.val < 16)]
  simp only [toBitVec_add,
    ← smallSigma1_toBitVec, ← smallSigma0_toBitVec,
    h2, h7, h15, h16]
  ac_rfl

theorem implScheduleStep_fst_at_self
    (i : Fin 80) (impl_block : Impl.Block) :
    ((implScheduleStep i impl_block).1[i.val % 16]'(mod16_lt _)) =
      (implScheduleStep i impl_block).2 := by
  unfold implScheduleStep
  by_cases hi : i.val < 16
  · simp only [dif_pos hi]; simp [Nat.mod_eq_of_lt hi]
  · simp only [dif_neg hi]; simp

theorem implScheduleStep_value_match
    (block₀ impl_block : Impl.Block) (W : Schedule) (n : Nat) (hn : n < 80)
    (huntouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k])
    (hring : ∀ k < n, n ≤ k + 16 →
      (impl_block[k % 16]'(by
        have := Nat.mod_lt k (show 0 < 16 by decide); omega)).toBitVec = W[k]!) :
    ((implScheduleStep ⟨n, hn⟩ impl_block).2).toBitVec =
      (specScheduleStep (toSpecBlock block₀) n W)[n]! := by
  by_cases hn16 : n < 16
  · unfold implScheduleStep specScheduleStep
    simp only [dif_pos hn16, if_pos hn16]
    rw [show impl_block[n] = block₀[n] from huntouched ⟨n, hn16⟩ (le_refl n)]
    rw [show (toSpecBlock block₀)[n]! = block₀[n].toBitVec from
        getElem!_toSpecBlock block₀ ⟨n, hn16⟩]
    rw [getElem!_pos _ n hn]
    rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn, Vector.getElem_set_self]
  · push Not at hn16
    have h2 := hring (n - 2) (by omega) (by omega)
    have h7 := hring (n - 7) (by omega) (by omega)
    have h15 := hring (n - 15) (by omega) (by omega)
    have h16 := hring (n - 16) (by omega) (by omega)
    rw [implScheduleStep_value_ge_16 ⟨n, hn⟩ impl_block W hn16 h2 h7 h15 h16]
    unfold specScheduleStep
    simp only [if_neg (Nat.not_lt.mpr hn16)]
    rw [getElem!_pos _ n hn]
    rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn, Vector.getElem_set_self]

end SHS.Equiv.SHA512.Compress.Impl
