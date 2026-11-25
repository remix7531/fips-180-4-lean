import equiv.SHA256.Compress.Impl
import equiv.SHA256.Constants
import equiv.SHA256.Foldl.Fused

/-! # Compression equivalence — `MatchAfter` invariant + cross-side meet

The intellectual core of the compress equivalence: the named impl
factored form (`implCompressFoldl`, from `Compress/Impl`) tracks the
named spec fused form (`specCompressFused`, from `Foldl/Fused`)
round-by-round, after lifting impl values through `toSpecState` /
`toSpecBlock`.

This module defines the `MatchAfter` invariant linking the two folds'
intermediate states, proves its base case (`MatchAfter_zero`) and
inductive preservation (`MatchAfter_step`), lifts the preservation to
the full 64-round fold (`MatchAfter_iter`), and finally peels the
invariant at `n = 64` to give `toSpecState_implCompressFoldl` and the
per-block theorem `SHS.Equiv.SHA256.compress_correct`. -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Functions
open SHS.Equiv.SHA256.Constants
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential
open SHS.Equiv.SHA256.Foldl.Fused
open SHS.Equiv.SHA256.Compress.Impl

open SHS.SHA256

namespace SHS.Equiv.SHA256.Compress.Match

open scoped SHS.SHA256

/-- After `n` rounds, the working state agrees with the spec. The 16-word ring buffer
retains the schedule words that the next round can read. Before round 16, untouched
slots are still needed to copy the original block words into the spec schedule. -/
structure MatchAfter
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) : Prop where
  /-- Lifted working variables match the spec vector. -/
  vars : toSpecState impl_state = vars
  /-- Ring-buffer window: entries `n - 16 ≤ k < n` of the spec schedule
  are present at positions `k % 16` in the impl block. -/
  ring : ∀ k : Nat, k < n → n ≤ k + 16 →
    (impl_block[k % 16]'(mod16_lt _)).toBitVec
      = W[k]!
  /-- Untouched slots: entries `n ≤ k < 16` of the original block still match. -/
  untouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k]

/-- Initial-state invariant: at round 0, the impl/spec states match trivially.
Base case for `MatchAfter_iter`. -/
theorem MatchAfter_zero
    (state : Impl.State) (block : Impl.Block) :
    MatchAfter block block state (Vector.replicate 64 default)
      (initVars (toSpecState state)) 0 where
  vars := by
    ext k hk
    simp [initVars]
  ring k hk _ := by omega
  untouched k _ := rfl

/-- Lift the implementation's round after aligning its current schedule word. -/
private theorem implRoundBody_toSpec (i : Fin 64) (word : UInt32) (state : Impl.State)
    (schedule : Schedule) (wordMatches : word.toBitVec = schedule[i.val]!) :
    toSpecState (implRoundBody i word state) =
      specRoundStep schedule i.val (toSpecState state) := by
  have roundConstant := K32_toBitVec_bang i.val
  rw [getElem!_pos Impl.K32 i.val i.isLt] at roundConstant
  rw [← Vector.toList_inj]
  unfold implRoundBody specRoundStep
  simp only [toSpecState, Vector.toList_map, Vector.toList_mk,
    List.map_cons, List.map_nil, Vector.getElem_map, Fin.getElem_fin,
    UInt32.toBitVec_add, ← bigSigma1_toBitVec, ← bigSigma0_toBitVec,
    ← Ch_toBitVec, ← Maj_toBitVec, wordMatches, roundConstant]
  ac_rfl

/-- A fused round preserves agreement of the state and the live schedule slots. -/
theorem MatchAfter_step
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) (hn : n < 64)
    (h : MatchAfter block₀ impl_block impl_state W vars n) :
    let i : Fin 64 := ⟨n, hn⟩
    let next_impl := implFusedStep i (impl_block, impl_state)
    let next_spec := specFusedStep (toSpecBlock block₀) i (W, vars)
    MatchAfter block₀ next_impl.1 next_impl.2 next_spec.1 next_spec.2 (n + 1) := by
  have wordMatches := implScheduleStep_value_match block₀ impl_block W n hn h.untouched h.ring
  simp only [implFusedStep, specFusedStep]
  refine ⟨?vars_match, ?ring_match, ?untouched⟩
  case vars_match =>
    rw [← h.vars]
    exact implRoundBody_toSpec _ _ _ _ wordMatches
  case ring_match =>
    intro k hk1 hk2
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk1) with hk_lt | hk_eq
    · -- The live window excludes the slot overwritten at round n.
      have otherSlot : k % 16 ≠ n % 16 := by omega
      rw [getElem!_specScheduleStep_lt (toSpecBlock block₀) n W k hk_lt,
        implScheduleStep_preserves_other_slot ⟨n, hn⟩ impl_block _ (mod16_lt _) otherSlot]
      exact h.ring k hk_lt (by omega)
    · -- The new live entry is the word emitted by this schedule step.
      cases hk_eq
      rw [implScheduleStep_fst_at_self]
      exact wordMatches
  case untouched =>
    intro k hk
    have inBounds := k.isLt
    have otherSlot : k.val ≠ n % 16 := by omega
    change (implScheduleStep ⟨n, hn⟩ impl_block).1[k.val]'inBounds = block₀[k]
    rw [implScheduleStep_preserves_other_slot ⟨n, hn⟩ impl_block k.val inBounds otherSlot]
    exact h.untouched k (by omega)

/-- Iteration: applying both folds for `n` rounds preserves `MatchAfter`.
Lifts the per-step preservation to the full 64-round fold. -/
theorem MatchAfter_iter
    (state : Impl.State) (block : Impl.Block)
    (n : Nat) (hn : n ≤ 64) :
    let impl_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        implFusedStep ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ acc) (block, state)
    let spec_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        specFusedStep (toSpecBlock block) i.val acc)
        (Vector.replicate 64 default, initVars (toSpecState state))
    MatchAfter block impl_acc.1 impl_acc.2 spec_acc.1 spec_acc.2 n := by
  induction n with
  | zero => exact MatchAfter_zero state block
  | succ k ih =>
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    exact MatchAfter_step block _ _ _ _ k (by omega) (ih (by omega))

/-- Pointwise feed-forward addition on the state vectors. -/
private theorem addH_eq_zipWith (H : HashValue) (state : SpecVars) :
    addH H state = Vector.zipWith (· + ·) H state := by
  rw [Vector.zipWith_comm_of_comm BitVec.add_comm,
    ← Vector.ofFn_getElem (xs := Vector.zipWith (· + ·) state H)]
  simp only [Vector.getElem_zipWith]
  rfl

/-- Lifting the impl factored fold through `toSpecState` yields the spec
fused fold on the lifted block. -/
theorem toSpecState_implCompressFoldl
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  have finalState := (MatchAfter_iter state block 64 (Nat.le_refl 64)).vars
  unfold implCompressFoldl specCompressFused
  rw [addH_eq_zipWith, ← finalState]
  unfold toSpecState
  rw [Vector.map_zipWith, Vector.zipWith_map]
  simp only [UInt32.toBitVec_add]

end SHS.Equiv.SHA256.Compress.Match

namespace SHS.Equiv.SHA256

open scoped SHS.SHA256

/-- The implementation's `Impl.compress` agrees with the spec's
`SHS.SHA256.compress` once both inputs are viewed in the spec's
`BitVec 32` representation via `toSpecState` and `toSpecBlock`. -/
theorem compress_correct (state : Impl.State) (block : Impl.Block) :
    toSpecState (Impl.compress state block) =
      SHS.SHA256.compress (toSpecState state) (toSpecBlock block) := by
  rw [← impl_compress_eq_foldl, Compress.Match.toSpecState_implCompressFoldl,
    ← spec_compress_eq_fused]

end SHS.Equiv.SHA256
