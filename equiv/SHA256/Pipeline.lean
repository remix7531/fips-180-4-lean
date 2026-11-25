import equiv.SHA256.Compress.Match
import equiv.SHA256.Padding.Equiv
import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.Padding.Parsing
import spec.Preprocessing

/-! # SHA-256 final-state equivalence

The streaming implementation and the spec agree on the final state for
any initial value. The entry points specialize this result to their IVs
and apply the digest emission proofs.
-/

open SHS.SHA256
open scoped SHS.SHA256

namespace SHS.Equiv.SHA256.Lift

/-! ## Initial-state bridge -/

/-- The impl's initial hash value `H256_256` lifts to the spec's `H0_256`. -/
@[simp] theorem toSpecState_H256_256 :
    toSpecState Impl.H256_256 = SHS.SHA256.H0_256 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

/-- The impl's SHA-224 IV `H256_224` lifts to the spec's `H0_224`. -/
@[simp] theorem toSpecState_H256_224 :
    toSpecState Impl.H256_224 = SHS.SHA256.H0_224 := by
  rw [← Vector.toList_inj, toSpecState, Vector.toList_map]
  rfl

end SHS.Equiv.SHA256.Lift

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Padding.Layout
open SHS.Equiv.SHA256.Padding.Equiv
open SHS.Equiv.SHA256.Padding.ByteDecoding
open SHS.Equiv.SHA256.Padding.Parsing

namespace SHS.Equiv.SHA256.Pipeline

/-- The bit-length precondition derived from the byte-length one:
`data.size < 2^61` implies `(bytesToBitMessage data).length < 2^64`. -/
theorem bitLen_lt_of_size_lt (data : ByteArray) (h : data.size < 2 ^ 61) :
    (bytesToBitMessage data).length < 2 ^ 64 := by
  rw [bytesToBitMessage, SHS.Equiv.Padding.bytesToBitMessage_length]
  omega

/-- Starting from any impl state, folding `Impl.compress` over impl
blocks lifts to folding `SHS.SHA256.compress` over the lifted blocks. -/
theorem foldl_compress_lift_gen (blocks : Array (Vector UInt8 64))
    (s : Impl.State) :
    toSpecState (blocks.foldl (fun s b => Impl.compress s (Impl.toU32s b)) s) =
      (blocks.map (fun b => toSpecBlock (Impl.toU32s b))).foldl
        SHS.SHA256.compress (toSpecState s) := by
  rw [Array.foldl_map]
  exact (Array.foldl_hom toSpecState (fun state block =>
    (compress_correct state (Impl.toU32s block)).symm)).symm

/-- Align the final state after streaming compression for any initial state. -/
theorem sha256State_correct (data : ByteArray) (fits : data.size < 2 ^ 61) (initial : Impl.State) :
    toSpecState (Impl.sha256State data initial) =
      (SHS.SHA256.parse (SHS.SHA256.pad (bytesToBitMessage data))).foldl
        SHS.SHA256.compress (toSpecState initial) := by
  rw [impl_sha256State_eq_refactored]
  unfold implSha256StateRefactored
  rw [foldl_compress_lift_gen, implPaddedBlocks_lift_eq_parsePad data fits, SHS.SHA1.pad]

end SHS.Equiv.SHA256.Pipeline
