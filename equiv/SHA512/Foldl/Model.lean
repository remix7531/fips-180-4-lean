import spec.Functions

/-! # SHA-512 compression fold model

The fold operations depend on the round functions and constants.
The proofs relating them to the spec's loops also need `spec.HashAlgorithms.SHA512`. -/

open SHS.SHA512
open scoped SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Schedule

/-- One schedule step copies the block word or mixes four earlier words.
The index is a `Nat` so a step has the same type in folds of different lengths. -/
def specScheduleStep (M : Block) (t : Nat) (W : Schedule) : Schedule :=
  if t < 16 then
    W.set! t M[t]!
  else
    W.set! t
      (SHS.SHA512.smallSigma1 W[t - 2]! + W[t - 7]! +
        SHS.SHA512.smallSigma0 W[t - 15]! + W[t - 16]!)

end SHS.Equiv.SHA512.Foldl.Schedule

namespace SHS.Equiv.SHA512.Foldl.Sequential

/-- The eight working variables in the spec's `BitVec 64` representation. -/
abbrev SpecVars := Vector (BitVec 64) 8

/-- Build the initial working variables from the input hash value. -/
def initVars (H : HashValue) : SpecVars :=
  Vector.ofFn (fun i : Fin 8 => H[i.val]!)

/-- One round of the compression loop with a fixed message schedule. -/
def specRoundStep (W : Schedule) (t : Nat) (s : SpecVars) : SpecVars :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let T1 := h + SHS.SHA512.bigSigma1 e + SHS.SHA512.Ch e f g + SHS.SHA512.K[t]! + W[t]!
  let T2 := SHS.SHA512.bigSigma0 a + SHS.SHA512.Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

/-- Add the post-loop working variables back into the input hash value. -/
def addH (H : HashValue) (s : SpecVars) : HashValue :=
  #v[s[0] + H[0]!, s[1] + H[1]!, s[2] + H[2]!, s[3] + H[3]!,
    s[4] + H[4]!, s[5] + H[5]!, s[6] + H[6]!, s[7] + H[7]!]

/-- Pointwise feed-forward addition on the spec vectors. -/
theorem addH_eq_zipWith (H : HashValue) (state : SpecVars) :
    addH H state = Vector.zipWith (· + ·) H state := by
  rw [Vector.zipWith_comm_of_comm BitVec.add_comm]
  rw [← Vector.ofFn_getElem (xs := Vector.zipWith (· + ·) state H)]
  simp only [Vector.getElem_zipWith]
  rfl

end SHS.Equiv.SHA512.Foldl.Sequential

namespace SHS.Equiv.SHA512.Foldl.Fused

open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential

/-- Update the schedule and mix the new word into the working variables. -/
def specFusedStep (M : Block) (t : Nat) (acc : Schedule × SpecVars) :
    Schedule × SpecVars :=
  let W' := specScheduleStep M t acc.1
  (W', specRoundStep W' t acc.2)

/-- A schedule step only modifies the word at its own index. -/
theorem getElem!_specScheduleStep_ne (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j ≠ t) :
    (specScheduleStep M t W)[j]! = W[j]! := by
  unfold specScheduleStep
  split <;> simp only [getElem!_def, Vector.getElem?_set!_ne hj.symm]

/-- A schedule step preserves the words that earlier rounds read. -/
theorem getElem!_specScheduleStep_lt (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j < t) :
    (specScheduleStep M t W)[j]! = W[j]! :=
  getElem!_specScheduleStep_ne M t W j (Nat.ne_of_lt hj)

/-- Interleave schedule updates and rounds in one fold over the schedule and working variables. -/
def specCompressFused (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 80 (fun acc (t : Fin 80) => specFusedStep M t.val acc)
    (Vector.replicate 80 default, initVars H)).2

end SHS.Equiv.SHA512.Foldl.Fused
