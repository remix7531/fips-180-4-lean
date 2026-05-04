import impl.SHA256
import spec.Setup
import equiv.SHA256.Bridge
import equiv.SHA256.Lift
import equiv.Common.Bytes
import Mathlib.Tactic.IntervalCases

/-!
# Per-block byte → word lift bridge

Each `UInt32` produced by `Impl.beU32` (big-endian decode of four bytes)
matches the spec's `Word.fromBits` over the 32 corresponding bits
(MSB-first within each byte).

This is the per-word building block for the full block-level bridge
between `Impl.toU32s` and `Spec.SHA256.parse` on one 512-bit block.

The byte → bit primitive `byteToBits` itself lives in
`equiv/Common/Bytes.lean` (word-size agnostic, shared with SHA-512); this
file only owns the SHA-256-specific 4-byte / 16-word assembly.
-/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA256.Bridge
open SHS.Equiv.SHA256.Lift

open SHS.SHA256

namespace SHS.Equiv.SHA256.ToU32s

open scoped SHS.SHA256

/-- Bits of `bytes[4i .. 4i+4)` as a single 32-element MSB-first list. -/
def fourBytesBits (bytes : Vector UInt8 64) (i : Fin 16) : List Bool :=
  byteToBits (bytes[4 * i.val]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 1]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 2]'(by omega)) ++
  byteToBits (bytes[4 * i.val + 3]'(by omega))

/-- `Word.fromBits` of one byte's MSB-first bit list equals the byte's
underlying `BitVec 8`.  Unfolds `byteToBits` + the 8-step foldl, then
the shared `UInt8.toNat_testBit_eq_getLsbD` simp lemma turns the goal
into pure `BitVec 8` arithmetic that `bv_decide` discharges. -/
theorem fromBits_byteToBits (b : UInt8) :
    (SHS.Word.fromBits (n := 8) (byteToBits b)) = b.toBitVec := by
  unfold byteToBits SHS.Word.fromBits
  simp only [List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.foldl,
    UInt8.toNat_testBit_eq_getLsbD]
  bv_decide

/-- Per-word bridge: the impl's `beU32` decode equals the spec's
`Word.fromBits` over the 32 MSB-first bits of the same four bytes.
Same shape as `fromBits_byteToBits` at width 32. -/
theorem beU32_eq_fromBits (bytes : Vector UInt8 64) (i : Fin 16) :
    (Impl.beU32 bytes i).toBitVec =
      SHS.Word.fromBits (n := 32) (fourBytesBits bytes i) := by
  unfold Impl.beU32 fourBytesBits byteToBits SHS.Word.fromBits
  generalize bytes[4 * i.val]'(by omega) = b0
  generalize bytes[4 * i.val + 1]'(by omega) = b1
  generalize bytes[4 * i.val + 2]'(by omega) = b2
  generalize bytes[4 * i.val + 3]'(by omega) = b3
  simp only [List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_assoc, List.map_cons, List.map_nil,
    List.foldl, UInt8.toNat_testBit_eq_getLsbD]
  bv_decide

/-! ## Block-level bridge

The 16-way assembly: `toSpecBlock (Impl.toU32s block)` matches the spec's
per-block parse (`(bits.toChunks 32).map Word.fromBits |>.toArray`) over
the corresponding 512 bits. -/

/-- Bits of a 64-byte block as a single 512-element MSB-first list. -/
def blockToBits (block : Vector UInt8 64) : List Bool :=
  block.toList.flatMap byteToBits

/-- Per-word bridge: the `i`-th word of `toSpecBlock (Impl.toU32s block)`
equals `Word.fromBits` of the `i`-th 32-bit slice of `blockToBits block`.

This is the bridging fact between the impl's `Vector.ofFn`-based
indexing and the spec's `List.toChunks 32` slicing.  Proof outline:
unfold both sides; show the 32-bit slice equals `fourBytesBits block i`
by list bookkeeping over `flatMap` chunks of 8; close with
`beU32_eq_fromBits`. -/
theorem toSpecBlock_toU32s_index (block : Vector UInt8 64) (i : Fin 16) :
    (toSpecBlock (Impl.toU32s block))[i.val]! =
      SHS.Word.fromBits (n := 32) (fourBytesBits block i) := by
  -- Unfold `Impl.toU32s` so the impl side becomes `Vector.ofFn (Impl.beU32 block ·)`.
  show (toSpecBlock (Vector.ofFn (fun i => Impl.beU32 block i)))[i.val]! = _
  -- Project the `i.val`-th word via `getElem!_toSpecBlock`.
  rw [getElem!_toSpecBlock]
  -- Reduce `(Vector.ofFn _)[i]` to `Impl.beU32 block i`.
  rw [show (Vector.ofFn (fun i => Impl.beU32 block i))[i] = Impl.beU32 block i from
    Vector.getElem_ofFn (i := i.val) i.isLt]
  -- Closing: per-word bridge.
  exact beU32_eq_fromBits block i

/-! ## Fast `ByteArray`-direct path

`Impl.sha256` no longer materializes the per-block `Vector UInt8 64`
intermediate; instead it calls `toU32sFromBytes data off` which reads
bytes straight out of the input `ByteArray`.  This lemma bridges the
fast path to the existing equivalence machinery (which is stated
against the `Vector`-shaped form). -/

/-- The direct-from-`ByteArray` path produces the same `Block` as the
old `toU32s ∘ Vector.ofFn` shape.  Both bodies are `Vector.ofFn`s
whose underlying functions agree pointwise after one `Vector.ofFn` β-reduction. -/
theorem toU32sFromBytes_eq_toU32s (data : ByteArray) (off : Nat) :
    Impl.toU32sFromBytes data off =
      Impl.toU32s (Vector.ofFn fun j : Fin 64 => data.get! (off + j.val)) := by
  apply Vector.ext
  intro i hi
  -- Both sides reduce per index `i ∈ {0..15}` to the same four-byte read
  -- expression at `data.get! (off + 4*i + k)` for k ∈ {0..3}.  The LHS is
  -- now an explicit `#v[..16..]` construction; the RHS goes through two
  -- `Vector.ofFn` β-reductions plus an associativity normalization.
  simp only [Impl.toU32sFromBytes, Impl.toU32s, Impl.beU32FromBytes, Impl.beU32,
    Vector.getElem_ofFn, ← Nat.add_assoc]
  decide

end SHS.Equiv.SHA256.ToU32s
