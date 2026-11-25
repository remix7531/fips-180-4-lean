import spec.Functions

/-! # SHA-256 fold model

The schedule and round operations depend only on the spec's round functions and
constants. Compression proofs can use the model before the spec loop proofs build. -/

open SHS.SHA256
open scoped SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Schedule

/-- One step of the spec message schedule. Copy the block word for `t < 16`,
or mix four earlier words. A natural index avoids casts in the fused fold. -/
def specScheduleStep (M : Block) (t : Nat) (W : Schedule) : Schedule :=
  if t < 16 then
    W.set! t M[t]!
  else
    W.set! t
      (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
        SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!)

end SHS.Equiv.SHA256.Foldl.Schedule

namespace SHS.Equiv.SHA256.Foldl.Sequential

/-- The eight working variables in the spec's word representation. -/
abbrev SpecVars := Vector (BitVec 32) 8

/-- Build the initial working variables from the input hash value. -/
def initVars (H : HashValue) : SpecVars :=
  Vector.ofFn (fun i : Fin 8 => H[i.val]!)

/-- One spec compression round. The natural index matches `specScheduleStep`. -/
def specRoundStep (W : Schedule) (t : Nat) (s : SpecVars) : SpecVars :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let T1 := h + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g + SHS.SHA256.K[t]! + W[t]!
  let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

/-- Add the post-loop working variables back into the input hash value. -/
def addH (H : HashValue) (s : SpecVars) : HashValue :=
  #v[s[0] + H[0]!, s[1] + H[1]!, s[2] + H[2]!, s[3] + H[3]!,
    s[4] + H[4]!, s[5] + H[5]!, s[6] + H[6]!, s[7] + H[7]!]

end SHS.Equiv.SHA256.Foldl.Sequential

namespace SHS.Equiv.SHA256.Foldl.Fused

open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential

/-- Update the schedule, then run the round with the word just written. -/
def specFusedStep (M : Block) (t : Nat) (acc : Schedule × SpecVars) :
    Schedule × SpecVars :=
  let W' := specScheduleStep M t acc.1
  (W', specRoundStep W' t acc.2)

/-- A schedule step preserves entries at every index other than the write index. -/
theorem getElem!_specScheduleStep_ne (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j ≠ t) :
    (specScheduleStep M t W)[j]! = W[j]! := by
  unfold specScheduleStep
  split <;> simp only [getElem!_def, Vector.getElem?_set!_ne hj.symm]

/-- A schedule write preserves the words that earlier rounds read. -/
theorem getElem!_specScheduleStep_lt (M : Block) (t : Nat) (W : Schedule)
    (j : Nat) (hj : j < t) :
    (specScheduleStep M t W)[j]! = W[j]! :=
  getElem!_specScheduleStep_ne M t W j (Nat.ne_of_lt hj)

/-- Spec compression interleaves schedule updates and rounds in one fold. -/
def specCompressFused (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64 (fun acc (t : Fin 64) => specFusedStep M t.val acc)
    (Vector.replicate 64 default, initVars H)).2

end SHS.Equiv.SHA256.Foldl.Fused
