import equiv.SHA512.Compress.Match
import equiv.SHA512.Padding.Equiv
import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.Padding.Parsing
import spec.SHA512t

/-! # SHA-512 final-state equivalence

The streaming implementation and the spec agree on the final state for
any initial value. The entry points specialize this result to their IVs
and apply the digest emission proofs.
-/

open SHS.SHA512
open scoped SHS.SHA512

namespace SHS.Equiv.SHA512.Lift

/-! ## Initial-state bridge -/

/-- The impl's initial hash value `H0_512` lifts to the spec's `H0_512`. -/
@[simp] theorem toSpecState_H0_512 :
    toSpecState Impl.H0_512 = SHS.SHA512.H0_512 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

/-- SHA-384 IV lift. -/
@[simp] theorem toSpecState_H0_384 :
    toSpecState Impl.H0_384 = SHS.SHA512.H0_384 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

/-- SHA-512/256 IV lift. -/
@[simp] theorem toSpecState_H0_512_256 :
    toSpecState Impl.H0_512_256 = SHS.SHA512.H0_512_256 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

/-- SHA-512/224 IV lift. -/
@[simp] theorem toSpecState_H0_512_224 :
    toSpecState Impl.H0_512_224 = SHS.SHA512.H0_512_224 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

end SHS.Equiv.SHA512.Lift

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Padding.Layout
open SHS.Equiv.SHA512.Padding.Equiv
open SHS.Equiv.SHA512.Padding.ByteDecoding
open SHS.Equiv.SHA512.Padding.Parsing

namespace SHS.Equiv.SHA512.Pipeline

/-- The bit-length precondition derived from the byte-length one:
`data.size < 2^61` implies `(bytesToBitMessage data).length < 2^128`,
the bound consumed by `SHS.SHA512.sha512`. -/
theorem bitLen_lt_of_size_lt (data : ByteArray) (h : data.size < 2 ^ 61) :
    (bytesToBitMessage data).length < 2 ^ 128 := by
  rw [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_length]
  omega

/-- Starting from any impl state, folding `Impl.compress` over impl
blocks lifts to folding `SHS.SHA512.compress` over the lifted blocks. -/
theorem foldl_compress_lift_gen (blocks : Array (Vector UInt8 128))
    (s : Impl.State) :
    toSpecState (blocks.foldl (fun s b => Impl.compress s (Impl.toU64s b)) s) =
      (blocks.map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress (toSpecState s) := by
  rw [Array.foldl_map]
  exact (Array.foldl_hom toSpecState (fun state block =>
    (compress_correct state (Impl.toU64s block)).symm)).symm

/-- Align the final state after streaming compression for any initial state. -/
theorem sha512State_correct (data : ByteArray) (fits : data.size < 2 ^ 61) (initial : Impl.State) :
    toSpecState (Impl.sha512State data initial) =
      (SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data))).foldl
        SHS.SHA512.compress (toSpecState initial) := by
  rw [impl_sha512State_eq_refactored]
  unfold implSha512StateRefactored
  rw [foldl_compress_lift_gen, implPaddedBlocks_lift_eq_parsePad data fits]

end SHS.Equiv.SHA512.Pipeline
