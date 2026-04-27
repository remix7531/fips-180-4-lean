import equiv.SHA256.Lift
import equiv.SHA256.Functions
import equiv.SHA256.Constants
import equiv.SHA256.Foldl.Fused

/-! # Compression equivalence — implementation-side factoring

The implementation's `compress` is imperative; this file recasts it as
a pure `Fin.foldl 64` (`implCompressFoldl`), agreeing with the source
by `rfl`, and proves the per-step bridge lemmas that connect the impl
fold's transitions to the spec's `specScheduleStep` /
`specRoundStep` primitives.

These per-step bridges are stated as standalone lemmas (independent
of the 64-round induction) so that `MatchAfter_step` in
`Compress/Match.lean` can call them directly without case-splitting
inline. -/

open SHS.Equiv.SHA256.Bridge
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Functions
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential

open SHS.SHA256

namespace SHS.Equiv.SHA256.Compress.Impl

open scoped SHS.SHA256

/-- The ring-buffer index bound used at every schedule-step site:
`k % 16 < 16`.  Extracted to deduplicate the inline
`Nat.mod_lt _ (by decide)` proofs at the lemma sites and inside
`MatchAfter`'s `ring` field. -/
theorem mod16_lt (k : Nat) : k % 16 < 16 := Nat.mod_lt _ (by decide)

/-! ## Implementation-side factoring -/

/-- One schedule step on the impl side: read `W[i]` (for `i < 16`,
straight from the block) or compute `W[i]` from the ring buffer and
store it back. Returns the updated ring buffer and the freshly-known
`W[i]`. -/
def implScheduleStep (i : Fin 64) (block : Impl.Block) : Impl.Block × UInt32 :=
  if hi : i.val < 16 then
    (block, block[i.val]'hi)
  else
    let w15 := block[(i.val - 15) % 16]'(by omega)
    let s0  := (Impl.UInt32.rotr w15 7) ^^^ (Impl.UInt32.rotr w15 18) ^^^ (w15 >>> 3)
    let w2  := block[(i.val - 2) % 16]'(by omega)
    let s1  := (Impl.UInt32.rotr w2 17) ^^^ (Impl.UInt32.rotr w2 19) ^^^ (w2 >>> 10)
    let w16 := block[(i.val - 16) % 16]'(by omega)
    let w7  := block[(i.val - 7) % 16]'(by omega)
    let new := w16 + s0 + w7 + s1
    (block.set ((i.val) % 16) new (by omega), new)

/-- One round body on the impl side: mix the schedule word `w` into the
eight working variables. -/
def implRoundBody (i : Fin 64) (w : UInt32) (s : Impl.State) : Impl.State :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let s1 := (Impl.UInt32.rotr e 6) ^^^ (Impl.UInt32.rotr e 11) ^^^ (Impl.UInt32.rotr e 25)
  let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
  let t1 := s1 + ch + Impl.K32[i] + w + h
  let s0 := (Impl.UInt32.rotr a 2) ^^^ (Impl.UInt32.rotr a 13) ^^^ (Impl.UInt32.rotr a 22)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let t2 := s0 + mj
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- One full round step: schedule, then mix. -/
def implFusedStep (i : Fin 64) (acc : Impl.Block × Impl.State) :
    Impl.Block × Impl.State :=
  let (block', w) := implScheduleStep i acc.1
  (block', implRoundBody i w acc.2)

/-- The named factored form of the implementation's `compress`:
`Fin.foldl 64 implFusedStep` plus the final hash add. -/
def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let (_, s') := Fin.foldl 64 (fun acc i => implFusedStep i acc) (block, state)
  Vector.zipWith (· + ·) state s'

/-- The factored form agrees with the original `Impl.compress` by
definition; lets `Main.lean` rewrite `Impl.compress` to the `Fin.foldl`
form on which the cross-side meet is stated. -/
theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := rfl

/-! ## Per-step bridges

Single-round equivalences between impl primitives and their spec
counterparts.  These are reusable independently of the 64-round
induction. -/

/-- The initial working variables built from a lifted impl state agree
with the impl state pointwise.  Base case of the `MatchAfter` invariant
in `Compress/Match.lean`. -/
theorem initVars_toSpecState_getElem (state : Impl.State) (k : Fin 8) :
    (initVars (toSpecState state))[k] = state[k].toBitVec := by
  simp [initVars, toSpecState, getElem!_pos]

-- Note: a per-index round-body equivalence lemma was attempted here but
-- cannot be packaged as a `∀ k : Fin 8` because `fin_cases` /
-- `match k with ⟨0,_⟩ ... ⟨7,_⟩` substitutes `⟨k, _⟩` into the goal,
-- preventing `Vector.getElem_mk` from matching the indexing pattern.
-- The 8-way enumeration therefore lives inline inside `MatchAfter_step`
-- in `Compress/Match.lean`.

/-- Schedule-step value equivalence (extension case `i ≥ 16`).
Used by `implScheduleStep_value_match` to align the impl's freshly
computed `W[i]` with the spec's `smallSigma1 + … + smallSigma0 + …`
formula, given the four ring-buffer entries already match. -/
theorem implScheduleStep_value_ge_16
    (i : Fin 64) (impl_block : Impl.Block) (W : Schedule) (hi : 16 ≤ i.val)
    (h2 : (impl_block[(i.val - 2) % 16]'(by omega)).toBitVec = W[i.val - 2]!)
    (h7 : (impl_block[(i.val - 7) % 16]'(by omega)).toBitVec = W[i.val - 7]!)
    (h15 : (impl_block[(i.val - 15) % 16]'(by omega)).toBitVec = W[i.val - 15]!)
    (h16 : (impl_block[(i.val - 16) % 16]'(by omega)).toBitVec = W[i.val - 16]!) :
    (implScheduleStep i impl_block).2.toBitVec =
      SHS.SHA256.smallSigma1 W[i.val - 2]! + W[i.val - 7]! +
        SHS.SHA256.smallSigma0 W[i.val - 15]! + W[i.val - 16]! := by
  unfold implScheduleStep
  rw [dif_neg (by omega : ¬ i.val < 16)]
  simp only [toBitVec_add,
    ← smallSigma1_toBitVec, ← smallSigma0_toBitVec,
    h2, h7, h15, h16]
  ac_rfl

/-- The freshly-known schedule word (`(implScheduleStep i b).2`) is exactly
the entry stored at `i.val % 16` in the updated ring buffer
(`(implScheduleStep i b).1`).

Used in `MatchAfter_step`'s `ring_match` sub-case to bridge "the new
schedule entry at index `n`" with "what the impl wrote to the ring
buffer at slot `n % 16`". -/
theorem implScheduleStep_fst_at_self
    (i : Fin 64) (impl_block : Impl.Block) :
    ((implScheduleStep i impl_block).1[i.val % 16]'(mod16_lt _)) =
      (implScheduleStep i impl_block).2 := by
  unfold implScheduleStep
  by_cases hi : i.val < 16
  · simp only [dif_pos hi]; simp [Nat.mod_eq_of_lt hi]
  · simp only [dif_neg hi]; simp

/-- Schedule-step value match (both branches `i.val < 16` and `i.val ≥ 16`):
the impl's freshly-known schedule word matches the spec's just-written
`W[i.val]!`, given the previous-round invariant on the ring buffer.

The schedule half of the per-round equivalence; consumed by the
`vars_match` and `ring_match` sub-cases of `MatchAfter_step`. -/
theorem implScheduleStep_value_match
    (block₀ impl_block : Impl.Block) (W : Schedule) (n : Nat) (hn : n < 64)
    (hWsize : W.size = 64)
    (huntouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k])
    (hring : ∀ k < n, n ≤ k + 16 →
      (impl_block[k % 16]'(by
        have := Nat.mod_lt k (show 0 < 16 by decide); omega)).toBitVec = W[k]!) :
    ((implScheduleStep ⟨n, hn⟩ impl_block).2).toBitVec =
      (specScheduleStep (toSpecBlock block₀) ⟨n, hn⟩ W)[n]! := by
  by_cases hn16 : n < 16
  · -- Initial case: spec writes `M[n]!`; impl block unchanged.
    unfold implScheduleStep specScheduleStep
    simp only [dif_pos hn16, if_pos hn16]
    rw [show impl_block[n] = block₀[n] from huntouched ⟨n, hn16⟩ (le_refl n)]
    rw [show (toSpecBlock block₀)[n]! = block₀[n].toBitVec from
        getElem!_toSpecBlock block₀ ⟨n, hn16⟩]
    rw [getElem!_pos _ n (by simp [hWsize, hn])]
    simp
  · -- Extension case: both sides compute the `smallSigma1/smallSigma0` formula.
    push Not at hn16
    have h2 := hring (n - 2) (by omega) (by omega)
    have h7 := hring (n - 7) (by omega) (by omega)
    have h15 := hring (n - 15) (by omega) (by omega)
    have h16 := hring (n - 16) (by omega) (by omega)
    rw [implScheduleStep_value_ge_16 ⟨n, hn⟩ impl_block W hn16 h2 h7 h15 h16]
    unfold specScheduleStep
    simp only [if_neg (Nat.not_lt.mpr hn16)]
    rw [getElem!_pos _ n (by simp [hWsize, hn])]
    simp

end SHS.Equiv.SHA256.Compress.Impl
