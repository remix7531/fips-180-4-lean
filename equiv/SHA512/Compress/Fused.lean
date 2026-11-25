import equiv.SHA512.Constants
import equiv.SHA512.Foldl.Model
import equiv.SHA512.Functions
import equiv.SHA512.Lift

/-! # Fused SHA-512 compression

The executable round fold uses a 16-word schedule ring. The spec fold
records every schedule word. Their working variables agree after each
round, and the ring retains every word the next round can read. -/

open SHS.SHA512
open scoped SHS.SHA512
open SHS.Equiv.SHA512.Constants
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Functions
open SHS.Equiv.SHA512.Lift

namespace SHS.Equiv.SHA512.Compress.Fused

private abbrev workingState (working : Impl.RoundState) : Impl.State :=
  #v[working.a, working.b, working.c, working.d, working.e, working.f, working.g, working.h]

private theorem mod16_lt (k : Nat) : k % 16 < 16 := Nat.mod_lt _ (by decide)

private structure MatchAfter (block : Impl.Block) (working : Impl.RoundState)
    (schedule : Schedule) (vars : SpecVars) (rounds : Nat) : Prop where
  vars_match : toSpecState (workingState working) = vars
  ring : ∀ k < rounds, rounds ≤ k + 16 →
    (working.schedule[k % 16]'(mod16_lt k)).toBitVec = schedule[k]!
  untouched : ∀ k : Fin 16, rounds ≤ k.val → working.schedule[k] = block[k]

private theorem scheduleStep_word_match (block : Impl.Block) (working : Impl.RoundState)
    (schedule : Schedule) (vars : SpecVars) (i : Fin 80)
    (before : MatchAfter block working schedule vars i.val) :
    (Impl.scheduleStep working.schedule i).2.toBitVec =
      (specScheduleStep (toSpecBlock block) i.val schedule)[i.val]! := by
  have getWritten (word : BitVec 64) : (schedule.set! i.val word)[i.val]! = word := by
    rw [getElem!_pos (schedule.set! i.val word) i.val i.isLt, Vector.getElem_set!_self]
  unfold Impl.scheduleStep specScheduleStep
  by_cases early : i.val < 16
  · rw [dite_eq_left early, ite_eq_left early, getWritten]
    rw [show working.schedule[i.val] = block[i.val] from
      before.untouched ⟨i.val, early⟩ (Nat.le_refl _)]
    exact (getElem!_toSpecBlock block ⟨i.val, early⟩).symm
  · rw [dite_eq_right early, ite_eq_right early, getWritten]
    have sigma0 (word : UInt64) :
        SHS.SHA512.smallSigma0 word.toBitVec = (Impl.smallSigma0 word).toBitVec :=
      smallSigma0_toBitVec word
    have sigma1 (word : UInt64) :
        SHS.SHA512.smallSigma1 word.toBitVec = (Impl.smallSigma1 word).toBitVec :=
      smallSigma1_toBitVec word
    simp only [UInt64.toBitVec_add, ← sigma0, ← sigma1,
      before.ring (i.val - 16) (by omega) (by omega),
      before.ring (i.val - 15) (by omega) (by omega),
      before.ring (i.val - 7) (by omega) (by omega),
      before.ring (i.val - 2) (by omega) (by omega)]
    ac_rfl

private theorem scheduleStep_at_self (ring : Impl.Block) (i : Fin 80) :
    ((Impl.scheduleStep ring i).1[i.val % 16]'(mod16_lt _)) =
      (Impl.scheduleStep ring i).2 := by
  unfold Impl.scheduleStep
  by_cases early : i.val < 16
  · simp [dite_eq_left early, Nat.mod_eq_of_lt early]
  · simp [dite_eq_right early]

private theorem scheduleStep_preserves_slot (ring : Impl.Block) (i : Fin 80)
    (slot : Nat) (inBounds : slot < 16) (other : slot ≠ i.val % 16) :
    (Impl.scheduleStep ring i).1[slot]'inBounds = ring[slot] := by
  unfold Impl.scheduleStep
  split
  · rfl
  · exact Vector.getElem_set_ne (mod16_lt _) inBounds other.symm

private theorem roundStep_vars_match (working : Impl.RoundState) (i : Fin 80)
    (schedule : Schedule)
    (wordMatches : (Impl.scheduleStep working.schedule i).2.toBitVec = schedule[i.val]!) :
    toSpecState (workingState (Impl.roundStep working i)) =
      specRoundStep schedule i.val (toSpecState (workingState working)) := by
  have constantMatches := K64_toBitVec_bang i.val
  rw [getElem!_pos Impl.K64 i.val i.isLt] at constantMatches
  have sigma0 : SHS.SHA512.bigSigma0 working.a.toBitVec = (Impl.bigSigma0 working.a).toBitVec :=
    bigSigma0_toBitVec working.a
  have sigma1 : SHS.SHA512.bigSigma1 working.e.toBitVec = (Impl.bigSigma1 working.e).toBitVec :=
    bigSigma1_toBitVec working.e
  rw [← Vector.toList_inj]
  simp only [workingState, Impl.roundStep, specRoundStep, toSpecState, Vector.toList_map,
    Vector.toList_mk, List.map_cons, List.map_nil, Vector.getElem_map, Fin.getElem_fin,
    UInt64.toBitVec_add, ← sigma0, ← sigma1, Impl.Ch, Impl.Maj, ← Ch_toBitVec, ← Maj_toBitVec,
    wordMatches, constantMatches]
  ac_rfl

private theorem MatchAfter.step (block : Impl.Block) (working : Impl.RoundState)
    (schedule : Schedule) (vars : SpecVars) (i : Fin 80)
    (before : MatchAfter block working schedule vars i.val) :
    let nextSpec := specFusedStep (toSpecBlock block) i.val (schedule, vars)
    MatchAfter block (Impl.roundStep working i) nextSpec.1 nextSpec.2 (i.val + 1) := by
  have wordMatches := scheduleStep_word_match block working schedule vars i before
  simp only [specFusedStep]
  constructor
  · rw [← before.vars_match]
    exact roundStep_vars_match working i _ wordMatches
  · intro k computed live
    change ((Impl.scheduleStep working.schedule i).1[k % 16]'(mod16_lt k)).toBitVec =
      (specScheduleStep (toSpecBlock block) i.val schedule)[k]!
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp computed) with earlier | current
    · have otherSlot : k % 16 ≠ i.val % 16 := by omega
      rw [getElem!_specScheduleStep_lt _ _ _ _ earlier,
        scheduleStep_preserves_slot _ _ _ (mod16_lt k) otherSlot]
      exact before.ring k earlier (by omega)
    · subst k
      rw [scheduleStep_at_self]
      exact wordMatches
  · intro k unread
    have inBounds := k.isLt
    have otherSlot : k.val ≠ i.val % 16 := by omega
    change (Impl.scheduleStep working.schedule i).1[k.val]'inBounds = block[k]
    rw [scheduleStep_preserves_slot _ _ _ inBounds otherSlot]
    exact before.untouched k (by omega)

private theorem matchAfter_fold (state : Impl.State) (block : Impl.Block)
    (rounds : Nat) (within : rounds ≤ 80) :
    let working := Fin.foldl rounds (fun working (i : Fin rounds) =>
      Impl.roundStep working ⟨i.val, Nat.lt_of_lt_of_le i.isLt within⟩)
      (Impl.RoundState.ofState state block)
    let spec := Fin.foldl rounds (fun acc (i : Fin rounds) =>
      specFusedStep (toSpecBlock block) i.val acc)
      (Vector.replicate 80 default, initVars (toSpecState state))
    MatchAfter block working spec.1 spec.2 rounds := by
  induction rounds with
  | zero =>
    simp only [Fin.foldl_zero]
    constructor
    · rw [show workingState (Impl.RoundState.ofState state block) = state from Vector.ofFn_getElem]
      ext k hk
      simp [initVars]
    · intro k hk
      omega
    · intro k _
      rfl
  | succ rounds previous =>
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    exact MatchAfter.step block _ _ _ ⟨rounds, by omega⟩ (previous (by omega))

/-- The executable SHA-512 compressor agrees with the fused spec fold. -/
theorem toSpecState_compress (state : Impl.State) (block : Impl.Block) :
    toSpecState (Impl.compress state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  have finalMatches := (matchAfter_fold state block 80 (Nat.le_refl 80)).vars_match
  simp only [Fin.eta] at finalMatches
  simp only [Impl.compress, SHS.Impl.Unroll.unroll80_eq_foldl, specCompressFused, addH_eq_zipWith]
  rw [← finalMatches]
  let final := Fin.foldl 80 Impl.roundStep (Impl.RoundState.ofState state block)
  have feedForward (working : Impl.RoundState) :
      #v[state[0] + working.a, state[1] + working.b, state[2] + working.c, state[3] + working.d,
         state[4] + working.e, state[5] + working.f, state[6] + working.g, state[7] + working.h] =
        Vector.zipWith (· + ·) state (workingState working) := by
    rw [← Vector.ofFn_getElem (xs := Vector.zipWith (· + ·) state (workingState working))]
    simp only [Vector.getElem_zipWith]
    rfl
  rw [feedForward final]
  unfold toSpecState
  rw [Vector.map_zipWith, Vector.zipWith_map]
  simp only [UInt64.toBitVec_add, final]

end SHS.Equiv.SHA512.Compress.Fused
