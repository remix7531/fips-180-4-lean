import equiv.Common.Loop
import equiv.SHA256.Lift
import equiv.SHA256.Functions
import equiv.SHA256.Foldl.Model

/-! # Compression equivalence — implementation-side factoring

The implementation's `compress` unrolls its rounds. This file recasts it as
a pure `Fin.foldl 64` (`implCompressFoldl`), proves the agreement with
`Impl.compress` via a `RoundState ↔ (Block, State)` fold-homomorphism
(`impl_compress_eq_foldl`), and proves the per-step bridge lemmas that
connect the impl fold's transitions to the spec's `specScheduleStep` /
`specRoundStep` primitives.

These per-step bridges are stated as standalone lemmas (independent
of the 64-round induction) so that `MatchAfter_step` in
`Compress/Match.lean` can call them directly without case-splitting
inline. -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Functions
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.Loop

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
    let w15 := block[(i.val - 15) % 16]'(mod16_lt _)
    let s0  := (Impl.UInt32.rotr w15 7) ^^^ (Impl.UInt32.rotr w15 18) ^^^ (w15 >>> 3)
    let w2  := block[(i.val - 2) % 16]'(mod16_lt _)
    let s1  := (Impl.UInt32.rotr w2 17) ^^^ (Impl.UInt32.rotr w2 19) ^^^ (w2 >>> 10)
    let w16 := block[(i.val - 16) % 16]'(mod16_lt _)
    let w7  := block[(i.val - 7) % 16]'(mod16_lt _)
    let new := w16 + s0 + w7 + s1
    (block.set (i.val % 16) new (mod16_lt _), new)

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
`Fin.foldl 64 implFusedStep` plus the final hash add.

This definition plays a dual role:
1. **Pivot for the spec ↔ impl equivalence proof** — the `MatchAfter`
   induction in `Compress/Match.lean` is stated against the per-step
   primitives `implScheduleStep` / `implRoundBody` that compose into
   `implFusedStep`, and `Main.lean` rewrites `Impl.compress` to this
   form so the induction applies.
2. **Aeneas-bridge target** — the shape (8-tuple working state +
   16-word ring-buffer schedule, pure functional `Fin.foldl 64`, no
   `Id.run`/`let mut`/imperative state) is precisely what an Aeneas
   Rust→Lean extraction of SHA-256 lands in after `noncomputable`
   lifting.  A future consumer wanting to refine an extraction against
   our spec needs only to prove `aeneas_compress = implCompressFoldl`
   (mostly type-level rewrites between `Std.U32` and `UInt32`); the
   spec ↔ `implCompressFoldl` half is what this project verifies. -/
def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let (_, s') := Fin.foldl 64 (fun acc i => implFusedStep i acc) (block, state)
  Vector.zipWith (· + ·) state s'

/-- Match the pointwise hash addition used by `Impl.compress`. -/
private theorem zipWith_add_eq_mk (state s' : Impl.State) :
    Vector.zipWith (· + ·) state s' =
      #v[ state[0] + s'[0], state[1] + s'[1], state[2] + s'[2], state[3] + s'[3],
          state[4] + s'[4], state[5] + s'[5], state[6] + s'[6], state[7] + s'[7] ] := by
  rw [← Vector.ofFn_getElem (xs := Vector.zipWith (· + ·) state s')]
  simp only [Vector.getElem_zipWith]
  rfl

/-! ### Bridge to `Impl.compress`'s `RoundState`-shaped fold

`Impl.compress` unfolds to `Fin.foldl 64 Impl.roundStep` over a `RoundState`
struct; `implCompressFoldl` runs `Fin.foldl 64 implFusedStep` over a
`(Block, Vector UInt32 8)` pair.  Both share the same outer
`Fin.foldl 64` shape, so the bridge is a per-iteration `RoundState ↔
(Block, State)` correspondence carried through fold-homomorphism. -/

/-- The state correspondence: a `RoundState` on the impl side maps to
`(rs.schedule, #v[rs.a, …, rs.h])` on the equiv side. -/
private def roundStateToPair (rs : Impl.RoundState) : Impl.Block × Impl.State :=
  (rs.schedule, #v[rs.a, rs.b, rs.c, rs.d, rs.e, rs.f, rs.g, rs.h])

/-- Transport an implementation round to the paired fold state. -/
private theorem roundStep_corresponds (rs : Impl.RoundState) (i : Fin 64) :
    roundStateToPair (Impl.roundStep rs i) = implFusedStep i (roundStateToPair rs) := rfl

/-- The executable compressor folds the round step and adds the final working variables. -/
theorem compress_eq_roundState_foldl (state : Impl.State) (block : Impl.Block) :
    Impl.compress state block =
      let final := Fin.foldl 64 Impl.roundStep (Impl.RoundState.ofState state block)
      #v[state[0] + final.a, state[1] + final.b, state[2] + final.c, state[3] + final.d,
         state[4] + final.e, state[5] + final.f, state[6] + final.g, state[7] + final.h] := by
  simp only [Impl.compress, SHS.Impl.Unroll.unroll64_eq_foldl]

/-- Public bridge: the impl's `RoundState`-shaped fold equals the
equiv's `(Block, State)`-shaped fold, plus matching final hash adds. -/
theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := by
  rw [compress_eq_roundState_foldl]
  unfold implCompressFoldl
  have transported := fin_foldl_transport 64
    Impl.roundStep (fun acc i => implFusedStep i acc) roundStateToPair
    (Impl.RoundState.ofState state block) roundStep_corresponds
  have initial : roundStateToPair (Impl.RoundState.ofState state block) = (block, state) := by
    apply Prod.ext
    · rfl
    · exact Vector.ofFn_getElem (xs := state)
  rw [initial] at transported
  change Vector.zipWith (· + ·) state
    (Fin.foldl 64 (fun acc i => implFusedStep i acc) (block, state)).2 = _
  rw [← congrArg Prod.snd transported, zipWith_add_eq_mk]
  rfl

/-! ## Per-step bridges

Single-round equivalences between impl primitives and their spec
counterparts.  These are reusable independently of the 64-round
induction. -/

/-- Schedule-step value equivalence (extension case `i ≥ 16`).
Used by `implScheduleStep_value_match` to align the impl's freshly
computed `W[i]` with the spec's `smallSigma1 + … + smallSigma0 + …`
formula, given the four ring-buffer entries already match. -/
theorem implScheduleStep_value_ge_16
    (i : Fin 64) (impl_block : Impl.Block) (W : Schedule) (hi : 16 ≤ i.val)
    (h2 : (impl_block[(i.val - 2) % 16]'(mod16_lt _)).toBitVec = W[i.val - 2]!)
    (h7 : (impl_block[(i.val - 7) % 16]'(mod16_lt _)).toBitVec = W[i.val - 7]!)
    (h15 : (impl_block[(i.val - 15) % 16]'(mod16_lt _)).toBitVec = W[i.val - 15]!)
    (h16 : (impl_block[(i.val - 16) % 16]'(mod16_lt _)).toBitVec = W[i.val - 16]!) :
    (implScheduleStep i impl_block).2.toBitVec =
      SHS.SHA256.smallSigma1 W[i.val - 2]! + W[i.val - 7]! +
        SHS.SHA256.smallSigma0 W[i.val - 15]! + W[i.val - 16]! := by
  unfold implScheduleStep
  rw [dite_eq_right (Nat.not_lt_of_ge hi)]
  simp only [UInt32.toBitVec_add,
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
  · simp only [dite_eq_left hi]; simp [Nat.mod_eq_of_lt hi]
  · simp only [dite_eq_right hi]; simp

/-- A schedule step preserves every ring slot other than its write slot. -/
theorem implScheduleStep_preserves_other_slot (i : Fin 64) (block : Impl.Block)
    (slot : Nat) (inBounds : slot < 16) (other : slot ≠ i.val % 16) :
    (implScheduleStep i block).1[slot]'inBounds = block[slot]'inBounds := by
  unfold implScheduleStep
  split
  · rfl
  · exact Vector.getElem_set_ne (mod16_lt _) inBounds other.symm

/-- Schedule-step value match (both branches `i.val < 16` and `i.val ≥ 16`):
the impl's freshly-known schedule word matches the spec's just-written
`W[i.val]!`, given the previous-round invariant on the ring buffer.

The schedule half of the per-round equivalence; consumed by the
`vars_match` and `ring_match` sub-cases of `MatchAfter_step`. -/
theorem implScheduleStep_value_match
    (block₀ impl_block : Impl.Block) (W : Schedule) (n : Nat) (hn : n < 64)
    (huntouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k])
    (hring : ∀ k < n, n ≤ k + 16 →
      (impl_block[k % 16]'(mod16_lt k)).toBitVec = W[k]!) :
    ((implScheduleStep ⟨n, hn⟩ impl_block).2).toBitVec =
      (specScheduleStep (toSpecBlock block₀) n W)[n]! := by
  by_cases hn16 : n < 16
  · -- Initial case: spec writes `M[n]!`; impl block unchanged.
    unfold implScheduleStep specScheduleStep
    simp only [dite_eq_left hn16, ite_eq_left hn16]
    rw [show impl_block[n] = block₀[n] from huntouched ⟨n, hn16⟩ (Nat.le_refl n)]
    rw [show (toSpecBlock block₀)[n]! = block₀[n].toBitVec from
        getElem!_toSpecBlock block₀ ⟨n, hn16⟩]
    rw [getElem!_pos _ n hn, Vector.getElem_set!_self]
  · -- Extension case: both sides compute the `smallSigma1/smallSigma0` formula.
    have h2 := hring (n - 2) (by omega) (by omega)
    have h7 := hring (n - 7) (by omega) (by omega)
    have h15 := hring (n - 15) (by omega) (by omega)
    have h16 := hring (n - 16) (by omega) (by omega)
    rw [implScheduleStep_value_ge_16 ⟨n, hn⟩ impl_block W (Nat.le_of_not_gt hn16) h2 h7 h15 h16]
    unfold specScheduleStep
    simp only [ite_eq_right hn16]
    rw [getElem!_pos _ n hn, Vector.getElem_set!_self]

end SHS.Equiv.SHA256.Compress.Impl
