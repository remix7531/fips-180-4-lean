import impl.SHA512
import spec.Setup
import equiv.SHA512.Bridge
import equiv.SHA512.Lift
import equiv.Common.Bytes
import Mathlib.Tactic.IntervalCases

/-!
# Per-block byte → word lift bridge (SHA-512)

Parallel to `equiv/SHA256/ToU32s.lean` at 64-bit width with 8 bytes
per word, 128 bytes per block (16 words).  The byte → bit primitive
`byteToBits` is shared from `equiv/Common/Bytes.lean`.
-/

open SHS.Equiv.Bytes
open SHS.Equiv.SHA512.Bridge
open SHS.Equiv.SHA512.Lift

open SHS.SHA512

namespace SHS.Equiv.SHA512.ToU64s

open scoped SHS.SHA512

/-- Bits of `bytes[8i .. 8i+8)` as a single 64-element MSB-first list. -/
def eightBytesBits (bytes : Vector UInt8 128) (i : Fin 16) : List Bool :=
  byteToBits (bytes[8 * i.val]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 1]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 2]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 3]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 4]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 5]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 6]'(by omega)) ++
  byteToBits (bytes[8 * i.val + 7]'(by omega))

/-- Selector lemma at arbitrary `N`. -/
private theorem getLsbD_ifBit (N : Nat) (x : Bool) (k : Nat) :
    (if x = true then (1 : BitVec N) else 0).getLsbD k =
      (decide (0 < N) && decide (k = 0) && x) := by
  cases x <;> simp [BitVec.getLsbD_one]

/-- `Word.fromBits` of one byte's MSB-first bit list equals the byte's
underlying `BitVec 8`.  Same as SHA-256's `fromBits_byteToBits` — same
proof, the input is just one byte and is width-agnostic. -/
theorem fromBits_byteToBits (b : UInt8) :
    (SHS.Word.fromBits (n := 8) (byteToBits b)) = b.toBitVec := by
  unfold byteToBits SHS.Word.fromBits
  simp only [List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.foldl,
    UInt8.toNat_testBit_eq_getLsbD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_ifBit]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- Per-word bridge: impl `beU64` decode equals spec `Word.fromBits`
over the 64 MSB-first bits of the same eight bytes. -/
theorem beU64_eq_fromBits (bytes : Vector UInt8 128) (i : Fin 16) :
    (Impl.beU64 bytes i).toBitVec =
      SHS.Word.fromBits (n := 64) (eightBytesBits bytes i) := by
  unfold Impl.beU64 eightBytesBits byteToBits SHS.Word.fromBits
  generalize bytes[8 * i.val]'(by omega) = b0
  generalize bytes[8 * i.val + 1]'(by omega) = b1
  generalize bytes[8 * i.val + 2]'(by omega) = b2
  generalize bytes[8 * i.val + 3]'(by omega) = b3
  generalize bytes[8 * i.val + 4]'(by omega) = b4
  generalize bytes[8 * i.val + 5]'(by omega) = b5
  generalize bytes[8 * i.val + 6]'(by omega) = b6
  generalize bytes[8 * i.val + 7]'(by omega) = b7
  simp only [List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    List.foldl, UInt8.toNat_testBit_eq_getLsbD]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_ifBit]
  interval_cases k <;> simp

/-! ## Block-level bridge -/

/-- Bits of a 128-byte block as a single 1024-element MSB-first list. -/
def blockToBits (block : Vector UInt8 128) : List Bool :=
  block.toList.flatMap byteToBits

theorem toSpecBlock_toU64s_index (block : Vector UInt8 128) (i : Fin 16) :
    (toSpecBlock (Impl.toU64s block))[i.val]! =
      SHS.Word.fromBits (n := 64) (eightBytesBits block i) := by
  show (toSpecBlock (Vector.ofFn (fun i => Impl.beU64 block i)))[i.val]! = _
  rw [getElem!_toSpecBlock]
  rw [show (Vector.ofFn (fun i => Impl.beU64 block i))[i] = Impl.beU64 block i from
    Vector.getElem_ofFn (i := i.val) i.isLt]
  exact beU64_eq_fromBits block i

/-! ## Fast `ByteArray`-direct path -/

theorem toU64sFromBytes_eq_toU64s (data : ByteArray) (off : Nat) :
    Impl.toU64sFromBytes data off =
      Impl.toU64s (Vector.ofFn fun j : Fin 128 => data.get! (off + j.val)) := by
  apply Vector.ext
  intro i hi
  simp only [Impl.toU64sFromBytes, Impl.toU64s, Impl.beU64FromBytes, Impl.beU64,
    Vector.getElem_ofFn, ← Nat.add_assoc]
  interval_cases i <;> rfl

end SHS.Equiv.SHA512.ToU64s
