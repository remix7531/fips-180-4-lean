import equiv.Common.Loop
import equiv.SHA512.Compress.Fused
import equiv.SHA512.Foldl.Fused

/-! # Sequential SHA-512 implementation model

The model expands the full schedule before folding the rounds. Both the
model and the executable compressor agree with the fused spec, which
gives the equation used by sequential compressor proofs. -/

open SHS.Equiv.Loop
open SHS.Equiv.VecBridge
open SHS.Equiv.SHA512.Constants
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Functions
open SHS.Equiv.SHA512.Lift
open SHS.SHA512
open scoped SHS.SHA512

namespace SHS.Equiv.SHA512.Compress.Impl

/-! ## Foldl form of `Impl.messageSchedule`

Same two-loop shape as the spec (`[0:16]` copy + `[16:80]` extension),
reified as a single `Fin.foldl 80`; mirrors `Foldl/Schedule.lean`. -/

/-- One step of the impl schedule, as a pure function on `Impl.Schedule`. -/
def implScheduleStep (block : Impl.Block) (t : Nat) (w : Impl.Schedule) : Impl.Schedule :=
  if t < 16 then
    w.set! t block[t]!
  else
    let w15 := w[t - 15]!
    let s0  := (Impl.UInt64.rotr w15 1) ^^^ (Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
    let w2  := w[t - 2]!
    let s1  := (Impl.UInt64.rotr w2 19) ^^^ (Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
    w.set! t (w[t - 16]! + s0 + w[t - 7]! + s1)

/-- Pure-foldl form of the impl schedule. -/
def implScheduleFoldl (block : Impl.Block) : Impl.Schedule :=
  Fin.foldl 80 (fun w (t : Fin 80) => implScheduleStep block t.val w)
    (Vector.replicate 80 0)

/-- The two schedule loops agree with one fold split at the first 16 words. -/
theorem messageSchedule_eq_foldl (block : Impl.Block) :
    Impl.messageSchedule block = implScheduleFoldl block := by
  unfold Impl.messageSchedule implScheduleFoldl
  change (forIn' [16:80]
    (Id.run (forIn' [0:16] (Vector.replicate 80 0) _)) _ : Id Impl.Schedule).run = _
  refine forIn'_split_eq_Fin_foldl 16 80 (by decide) _ (implScheduleStep block) _ _ ?_ ?_
  · intro t member words
    have inBlock : t < 16 := member.upper
    simp (discharger := omega) only [implScheduleStep, ite_eq_left inBlock, getElem!_pos,
      set_bang_eq_set]
  · intro t member words
    have afterBlock : 16 ≤ t := member.lower
    have inSchedule : t < 80 := member.upper
    simp (discharger := omega) only [implScheduleStep, ite_eq_right, getElem!_pos,
      set_bang_eq_set]

/-! ## Sequential round fold -/

/-- The impl's round mix, as a pure function on `Impl.State`. -/
def implRoundStep (w : Impl.Schedule) (t : Nat) (s : Impl.State) : Impl.State :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let s1 := (Impl.UInt64.rotr e 14) ^^^ (Impl.UInt64.rotr e 18) ^^^ (Impl.UInt64.rotr e 41)
  let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
  let t1 := s1 + ch + Impl.K64[t]! + w[t]! + h
  let s0 := (Impl.UInt64.rotr a 28) ^^^ (Impl.UInt64.rotr a 34) ^^^ (Impl.UInt64.rotr a 39)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let t2 := s0 + mj
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- Expand the full schedule, fold the rounds, and add back the input state. -/
def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let w := Impl.messageSchedule block
  let final := Fin.foldl 80 (fun s (t : Fin 80) => implRoundStep w t.val s) state
  #v[state[0] + final[0], state[1] + final[1], state[2] + final[2], state[3] + final[3],
     state[4] + final[4], state[5] + final[5], state[6] + final[6], state[7] + final[7]]

end SHS.Equiv.SHA512.Compress.Impl

namespace SHS.Equiv.SHA512.Compress.Match

open SHS.Equiv.SHA512.Compress.Impl

/-! ## Indexing bridges -/

/-- Lift `Impl.Schedule` to spec `Schedule` by mapping each word through `toBitVec`. -/
def toSpecSchedule (w : Impl.Schedule) : Schedule := w.map UInt64.toBitVec

/-- Indexing commutes with `toSpecSchedule` because the default `UInt64` maps to zero. -/
theorem toSpecSchedule_getElem! (w : Impl.Schedule) (t : Nat) :
    (toSpecSchedule w)[t]! = (w[t]!).toBitVec := by
  simp only [toSpecSchedule, getElem!_def, Vector.getElem?_map]
  cases w[t]? <;> rfl

/-- `map` commutes with `set!`. -/
theorem toSpecSchedule_set! (w : Impl.Schedule) (t : Nat) (x : UInt64) :
    toSpecSchedule (w.set! t x) = (toSpecSchedule w).set! t x.toBitVec := by
  simp only [toSpecSchedule, Vector.set!_eq_setIfInBounds, Vector.map_setIfInBounds]

/-! ## Schedule bridge -/

/-- Per-step schedule bridge.  Both branches share the
`toSpecSchedule (·.set! t ·)` rewrite; they differ only in the value written
(`block[t]` vs `σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`). -/
theorem implScheduleStep_toSpec (block : Impl.Block) (t : Nat) (w : Impl.Schedule) :
    toSpecSchedule (implScheduleStep block t w) =
      specScheduleStep (toSpecBlock block) t (toSpecSchedule w) := by
  unfold implScheduleStep specScheduleStep
  split <;> rw [toSpecSchedule_set!] <;> refine congrArg ((toSpecSchedule w).set! t) ?_
  · rename_i ht
    simp (discharger := exact ht) only [toSpecBlock, getElem!_pos, Vector.getElem_map]
  · simp only [UInt64.toBitVec_add, ← smallSigma1_toBitVec, ← smallSigma0_toBitVec,
               toSpecSchedule_getElem!]
    ac_rfl

/-- Schedule bridge: lifting `Impl.messageSchedule` matches the spec's `schedule`. -/
theorem messageSchedule_toSpec (block : Impl.Block) :
    toSpecSchedule (Impl.messageSchedule block) =
      SHS.SHA512.schedule (toSpecBlock block) := by
  have h0 : toSpecSchedule (Vector.replicate 80 (0 : UInt64))
      = Vector.replicate 80 (default : BitVec 64) := by
    rw [toSpecSchedule, Vector.map_replicate]; rfl
  rw [messageSchedule_eq_foldl, schedule_eq_foldl, ← h0, implScheduleFoldl]
  exact fin_foldl_transport 80 _ _ toSpecSchedule _
    (fun w t => implScheduleStep_toSpec block t.val w)

/-! ## Round bridge -/

/-- Lifting one round commutes with the round calculation. -/
theorem implRoundStep_toSpec
    (w : Impl.Schedule) (t : Nat) (s : Impl.State) :
    toSpecState (implRoundStep w t s) =
      specRoundStep (toSpecSchedule w) t (toSpecState s) := by
  rw [← Vector.toList_inj]
  unfold implRoundStep specRoundStep
  simp only [toSpecState, Vector.toList_map, Vector.toList_mk,
    List.map_cons, List.map_nil, Vector.getElem_map,
    UInt64.toBitVec_add, ← bigSigma0_toBitVec, ← bigSigma1_toBitVec,
    ← Ch_toBitVec, ← Maj_toBitVec, K64_toBitVec_bang, toSpecSchedule_getElem!]
  ac_rfl

/-- Foldl-form round bridge: lifting commutes with the 80-round fold. -/
theorem implRoundsFoldl_toSpec
    (block : Impl.Block) (state : Impl.State) :
    toSpecState (Fin.foldl 80 (fun s (t : Fin 80) =>
        implRoundStep (Impl.messageSchedule block) t.val s) state) =
      Fin.foldl 80 (fun s (t : Fin 80) =>
        specRoundStep (SHS.SHA512.schedule (toSpecBlock block)) t.val s)
        (toSpecState state) :=
  fin_foldl_transport 80 _ _ toSpecState state (fun s t => by
    rw [implRoundStep_toSpec]; congr 1; exact messageSchedule_toSpec block)

/-! ## Composite -/

/-- The implementation fold adds its final working variables to the input state. -/
private theorem implCompressFoldl_eq_zipWith (state : Impl.State) (block : Impl.Block) :
    let final := Fin.foldl 80 (fun s t => implRoundStep (Impl.messageSchedule block) t.val s) state
    implCompressFoldl state block = Vector.zipWith (· + ·) state final := by
  intro final
  rw [← Vector.ofFn_getElem (xs := Vector.zipWith (· + ·) state final)]
  simp only [Vector.getElem_zipWith]
  rfl

/-- The impl's compression fold matches the spec's sequential fold.
Both compute the schedule before processing the rounds. -/
theorem toSpecState_implCompressFoldl_seq
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressSeq (toSpecState state) (toSpecBlock block) := by
  -- `initVars` is the identity after lifting (`ofFn (H[i]!)`-shape).
  have hinit : initVars (toSpecState state) = toSpecState state := by
    ext i _; simp [initVars]
  unfold specCompressSeq
  rw [implCompressFoldl_eq_zipWith, addH_eq_zipWith, hinit, ← implRoundsFoldl_toSpec]
  unfold toSpecState
  rw [Vector.map_zipWith, Vector.zipWith_map]
  simp only [UInt64.toBitVec_add]

/-- The fused spec fold agrees with the sequential implementation fold. -/
theorem toSpecState_implCompressFoldl
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  rw [toSpecState_implCompressFoldl_seq, ← spec_compress_eq_seq, spec_compress_eq_fused]

end SHS.Equiv.SHA512.Compress.Match

namespace SHS.Equiv.SHA512.Compress.Impl

/-- The sequential implementation model agrees with the executable compressor. -/
theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := by
  apply (Vector.map_inj_right (fun _ _ equal => UInt64.toBitVec_inj.mp equal)).mp
  change toSpecState (implCompressFoldl state block) = toSpecState (Impl.compress state block)
  rw [Match.toSpecState_implCompressFoldl, Fused.toSpecState_compress]

end SHS.Equiv.SHA512.Compress.Impl
