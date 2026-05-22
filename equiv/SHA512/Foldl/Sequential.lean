import equiv.Common.Loop
import spec.HashAlgorithms

local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)))

/-! # Pure-foldl form of the SHA-512 spec compression — sequential

Parallel to `equiv/SHA256/Foldl/Sequential.lean` at 80 rounds, 64-bit
words.  Same `SpecVarsTuple` shape: 8 nested `MProd` cells matching
the desugaring of `Id.run do { mut a..h; for ... }`. -/

open SHS.Equiv.Loop

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Sequential

open scoped SHS.SHA512

abbrev SpecVars := Vector (BitVec 64) 8

def initVars (H : HashValue) : SpecVars :=
  Vector.ofFn (fun i : Fin 8 => H[i.val]!)

def specRoundStep (W : Schedule) (t : Nat) (s : SpecVars) : SpecVars :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let T1 := h + SHS.SHA512.bigSigma1 e + SHS.SHA512.Ch e f g + SHS.SHA512.K[t]! + W[t]!
  let T2 := SHS.SHA512.bigSigma0 a + SHS.SHA512.Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

def addH (H : HashValue) (s : SpecVars) : HashValue :=
  #v[s[0] + H[0]!, s[1] + H[1]!, s[2] + H[2]!, s[3] + H[3]!,
    s[4] + H[4]!, s[5] + H[5]!, s[6] + H[6]!, s[7] + H[7]!]

abbrev SpecVarsTuple :=
  MProd (BitVec 64) (MProd (BitVec 64) (MProd (BitVec 64) (MProd (BitVec 64)
    (MProd (BitVec 64) (MProd (BitVec 64) (MProd (BitVec 64) (BitVec 64)))))))

def tupleToVec (t : SpecVarsTuple) : SpecVars :=
  #v[t.fst, t.snd.fst, t.snd.snd.fst, t.snd.snd.snd.fst,
     t.snd.snd.snd.snd.fst, t.snd.snd.snd.snd.snd.fst,
     t.snd.snd.snd.snd.snd.snd.fst, t.snd.snd.snd.snd.snd.snd.snd]

def tupleRoundStep (W : Schedule) (t : Nat) (r : SpecVarsTuple) : SpecVarsTuple :=
  let a := r.fst
  let x := r.snd
  let b := x.fst
  let x := x.snd
  let c := x.fst
  let x := x.snd
  let d := x.fst
  let x := x.snd
  let e := x.fst
  let x := x.snd
  let f := x.fst
  let x := x.snd
  let g := x.fst
  let h := x.snd
  let T1 := h + SHS.SHA512.bigSigma1 e + SHS.SHA512.Ch e f g + SHS.SHA512.K[t]! + W[t]!
  let T2 := SHS.SHA512.bigSigma0 a + SHS.SHA512.Maj a b c
  ⟨T1 + T2, a, b, c, d + T1, e, f, g⟩

@[simp] theorem tupleToVec_tupleRoundStep (W : Schedule) (t : Fin 80) (r : SpecVarsTuple) :
    tupleToVec (tupleRoundStep W t.val r) = specRoundStep W t.val (tupleToVec r) := by
  rfl

@[simp] theorem tupleToVec_init (H : HashValue) :
    tupleToVec (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple) =
      initVars H := by
  unfold initVars tupleToVec; rfl

@[simp] theorem addH_tupleToVec (H : HashValue) (r : SpecVarsTuple) :
    addH H (tupleToVec r) =
      (#v[r.fst + H[0]!, r.snd.fst + H[1]!, r.snd.snd.fst + H[2]!,
          r.snd.snd.snd.fst + H[3]!, r.snd.snd.snd.snd.fst + H[4]!,
          r.snd.snd.snd.snd.snd.fst + H[5]!, r.snd.snd.snd.snd.snd.snd.fst + H[6]!,
          r.snd.snd.snd.snd.snd.snd.snd + H[7]!] : HashValue) := by
  rfl

def specCompressSeq (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 80
    (fun s (t : Fin 80) => specRoundStep (SHS.SHA512.schedule M) t.val s) (initVars H))

theorem spec_compress_eq_seq (H : HashValue) (M : Block) :
    SHS.SHA512.compress H M = specCompressSeq H M := by
  unfold specCompressSeq SHS.SHA512.compress
  let bodyTup : (t : Nat) → t ∈ [0:80] → SpecVarsTuple → Id (ForInStep SpecVarsTuple) :=
    fun t h r =>
      have h80 : t < 80 := h.upper
      pure (ForInStep.yield (tupleRoundStep (SHS.SHA512.schedule M) t r))
  have hH (i : Nat) (hi : i < 8) : H[i]'hi = H[i]! :=
    (SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi).symm
  have hbody : (fun (t : Nat) (h : t ∈ [0:80]) (r : SpecVarsTuple) =>
        let a := r.fst; let x := r.snd; let b := x.fst; let x := x.snd
        let c := x.fst; let x := x.snd; let d := x.fst; let x := x.snd
        let e := x.fst; let x := x.snd; let f := x.fst; let x := x.snd
        let g := x.fst; let h_ := x.snd
        let T1 := h_ + SHS.SHA512.bigSigma1 e + SHS.SHA512.Ch e f g +
          (SHS.SHA512.K[t]'h.upper) + ((SHS.SHA512.schedule M)[t]'h.upper)
        let T2 := SHS.SHA512.bigSigma0 a + SHS.SHA512.Maj a b c
        pure (ForInStep.yield (⟨T1 + T2, a, b, c, d + T1, e, f, g⟩ : SpecVarsTuple))) =
      bodyTup := by
    funext t h r
    simp only [bodyTup, tupleRoundStep]
    have h80 : t < 80 := h.upper
    rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem SHS.SHA512.K t h80,
        SHS.Equiv.VecBridge.getElem_bang_eq_getElem (SHS.SHA512.schedule M) t h80]
  show Id.run (do
        let r ← forIn' [0:80]
          (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
             H[4]'(by decide), H[5]'(by decide),
             H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple)
          (fun t (h : t ∈ [0:80]) r =>
            let a := r.fst; let x := r.snd; let b := x.fst; let x := x.snd
            let c := x.fst; let x := x.snd; let d := x.fst; let x := x.snd
            let e := x.fst; let x := x.snd; let f := x.fst; let x := x.snd
            let g := x.fst; let h_ := x.snd
            let T1 := h_ + SHS.SHA512.bigSigma1 e + SHS.SHA512.Ch e f g +
              (SHS.SHA512.K[t]'h.upper) + ((SHS.SHA512.schedule M)[t]'h.upper)
            let T2 := SHS.SHA512.bigSigma0 a + SHS.SHA512.Maj a b c
            pure (ForInStep.yield (⟨T1 + T2, a, b, c, d + T1, e, f, g⟩ : SpecVarsTuple)))
        match r with
        | ⟨a, b, c, d, e, f, g, h⟩ =>
          pure (#v[a + H[0], b + H[1], c + H[2], d + H[3],
                  e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) = _
  rw [hbody]
  show (Id.run (forIn' [0:80]
          (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
             H[4]'(by decide), H[5]'(by decide),
             H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple)
          bodyTup)
        |> fun r => match r with
          | ⟨a, b, c, d, e, f, g, h⟩ =>
            (#v[a + H[0], b + H[1], c + H[2], d + H[3],
                e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) = _
  have hinit_eq :
      (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
         H[4]'(by decide), H[5]'(by decide), H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple) =
      ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ := by
    rw [hH 0, hH 1, hH 2, hH 3, hH 4, hH 5, hH 6, hH 7]
  rw [hinit_eq]
  rw [show Id.run (forIn' [0:80]
          (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
          bodyTup) =
      Id.run (forIn [0:80]
        (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
        (fun t r => pure (ForInStep.yield
          (tupleRoundStep (SHS.SHA512.schedule M) t r)))) from by
    rw [← forIn'_id_eq_forIn 0 80 _
          (fun t r => tupleRoundStep (SHS.SHA512.schedule M) t r)]]
  rw [forIn_id_eq_Fin_foldl 80
        (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
        (tupleRoundStep (SHS.SHA512.schedule M))]
  have hfinal :
      (fun r : SpecVarsTuple =>
        match r with
        | ⟨a, b, c, d, e, f, g, h⟩ =>
          (#v[a + H[0], b + H[1], c + H[2], d + H[3],
              e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) =
      (fun r : SpecVarsTuple => addH H (tupleToVec r)) := by
    funext r
    obtain ⟨a, b, c, d, e, f, g, h⟩ := r
    simp only [addH, tupleToVec]
    rw [← hH 0, ← hH 1, ← hH 2, ← hH 3, ← hH 4, ← hH 5, ← hH 6, ← hH 7]
    rfl
  show (fun r : SpecVarsTuple =>
          match r with
          | ⟨a, b, c, d, e, f, g, h⟩ =>
            (#v[a + H[0], b + H[1], c + H[2], d + H[3],
                e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue))
        (Fin.foldl 80 (fun s (t : Fin 80) =>
            tupleRoundStep (SHS.SHA512.schedule M) t.val s)
          ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩) = _
  rw [hfinal]
  beta_reduce
  rw [fin_foldl_transport 80
        (fun r t => tupleRoundStep (SHS.SHA512.schedule M) t.val r)
        (fun s (t : Fin 80) => specRoundStep (SHS.SHA512.schedule M) t.val s)
        tupleToVec
        ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
        (fun a i => tupleToVec_tupleRoundStep _ i a)]
  rw [tupleToVec_init]

end SHS.Equiv.SHA512.Foldl.Sequential
