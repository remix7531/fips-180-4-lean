import equiv.Common.Loop
import spec.HashAlgorithms

/-! # Pure-foldl form of the spec compression — sequential

Restates `SHS.SHA256.compress` as `addH H (Fin.foldl 64 specRoundStep
(initVars H))` after precomputing the schedule.

The desugaring of `Id.run do { mut a..h; for t in [0:64] do … }`
introduces a right-associated 8-`MProd` working tuple; this file owns
that bridge (`SpecVarsTuple`, `tupleToVec`) so consumers reason against
`SpecVars` and never touch `MProd`. -/

open SHS.Equiv.Loop

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Sequential

open scoped SHS.SHA256

/-- Eight working variables `(a, b, c, d, e, f, g, h)`, in the spec's
`BitVec 32` representation. -/
abbrev SpecVars := Vector (BitVec 32) 8

/-- Build the initial working variables from the input hash value. -/
def initVars (H : HashValue) : SpecVars :=
  Vector.ofFn (fun i : Fin 8 => H[i.val]!)

/-- One round of the spec's compression loop, as a pure function:
shifts `(a..h)` by one, with `a` and `e` updated by the standard
`T1`/`T2` mixing.  This matches the body of the `for t in [0:64]`
loop in `SHS.SHA256.compress`. -/
def specRoundStep (W : Schedule) (t : Fin 64) (s : SpecVars) : SpecVars :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let T1 := h + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g + SHS.SHA256.K[t.val]! + W[t.val]!
  let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

/-- Add the post-loop working variables back into the input hash value. -/
def addH (H : HashValue) (s : SpecVars) : HashValue :=
  #[s[0] + H[0]!, s[1] + H[1]!, s[2] + H[2]!, s[3] + H[3]!,
    s[4] + H[4]!, s[5] + H[5]!, s[6] + H[6]!, s[7] + H[7]!]

/-! ## Spec-tuple bridge

When Lean desugars `Id.run do { mut a..h; for t in [0:64] do … }`, the
eight `mut` variables become a nested right-associated `MProd`.  The
abbreviations and lemmas below pass back and forth between that
desugared 8-tuple and our `SpecVars` vector. -/

/-- The 8-tuple of `BitVec 32` carrying the spec compress's working
variables `(a, b, c, d, e, f, g, h)` while `Id.run do { mut … }` is
desugared.  Backed by nested `MProd` (Lean's anonymous-constructor type
used for desugaring multiple `mut` bindings), not `Prod`; this
`structure` is reducible to that nesting via `unfold SpecVarsTuple`. -/
structure SpecVarsTuple where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32
  e : BitVec 32
  f : BitVec 32
  g : BitVec 32
  h : BitVec 32

/-- Convert the desugared tuple state into a `SpecVars` vector. -/
def tupleToVec (t : SpecVarsTuple) : SpecVars :=
  #v[t.a, t.b, t.c, t.d, t.e, t.f, t.g, t.h]

/-- The desugared tuple round step (matching the body of spec's
`Id.run do` form, with the destructured `r.fst`/`r.snd…` pattern). -/
def tupleRoundStep (W : Schedule) (t : Nat) (r : SpecVarsTuple) : SpecVarsTuple :=
  let T1 := r.h + SHS.SHA256.bigSigma1 r.e + SHS.SHA256.Ch r.e r.f r.g
              + SHS.SHA256.K[t]! + W[t]!
  let T2 := SHS.SHA256.bigSigma0 r.a + SHS.SHA256.Maj r.a r.b r.c
  ⟨T1 + T2, r.a, r.b, r.c, r.d + T1, r.e, r.f, r.g⟩

/-- The tuple round step matches `specRoundStep` once both states are
viewed through `tupleToVec`. -/
@[simp] theorem tupleToVec_tupleRoundStep (W : Schedule) (t : Fin 64) (r : SpecVarsTuple) :
    tupleToVec (tupleRoundStep W t.val r) = specRoundStep W t (tupleToVec r) := by
  rfl

/-- The initial tuple state matches `initVars H` through `tupleToVec`. -/
@[simp] theorem tupleToVec_init (H : HashValue) :
    tupleToVec ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ = initVars H := by
  unfold initVars tupleToVec; rfl

/-- The post-loop tuple-projection array matches `addH H` through `tupleToVec`. -/
@[simp] theorem addH_tupleToVec (H : HashValue) (r : SpecVarsTuple) :
    addH H (tupleToVec r) =
      #[r.a + H[0]!, r.b + H[1]!, r.c + H[2]!, r.d + H[3]!,
        r.e + H[4]!, r.f + H[5]!, r.g + H[6]!, r.h + H[7]!] := by
  rfl

/-- Spec `compress` in **sequential** pure-foldl form: precompute the
full schedule, then fold the round body over the 64 rounds. -/
def specCompressSeq (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64 (fun s t => specRoundStep (SHS.SHA256.schedule M) t s) (initVars H))

/-- The spec's `compress` equals its sequential pure-foldl form
(`specCompressSeq`).  Downstream consumers reason against
`specCompressSeq` instead of the `Id.run do` form. -/
theorem spec_compress_eq_seq (H : HashValue) (M : Block) :
    SHS.SHA256.compress H M = specCompressSeq H M := by
  unfold specCompressSeq
  -- Spec's `Id.run do { mut a..h; for t in [0:64] do …; return #[…] }` is
  -- *definitionally* `addH H (tupleToVec (Id.run (forIn …)))`; the
  -- `pure unit; pure (yield …)` desugaring residue is absorbed by `rfl`.
  show addH H (tupleToVec
        (Id.run (forIn [0:64]
          (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
          (fun t r => pure (ForInStep.yield
            (tupleRoundStep (SHS.SHA256.schedule M) t r)))))) = _
  rw [forIn_id_eq_Fin_foldl 64]
  rw [fin_foldl_transport 64
        (fun r t => tupleRoundStep (SHS.SHA256.schedule M) t.val r)
        (fun s t => specRoundStep (SHS.SHA256.schedule M) t s)
        tupleToVec
        ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
        (fun a i => tupleToVec_tupleRoundStep _ i a)]
  rw [tupleToVec_init]

end SHS.Equiv.SHA256.Foldl.Sequential
