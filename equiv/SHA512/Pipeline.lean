import equiv.SHA512.Compress.Impl
import equiv.SHA512.Compress.Match
import equiv.SHA512.Padding.Equiv
import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.Padding.Parsing
import equiv.SHA512.Digest
import spec.SHA512tHash

/-! # SHA-512 pipeline composition helpers

Parallel to `equiv/SHA256/Pipeline.lean` at 80 rounds. -/

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Compress.Impl
open SHS.Equiv.SHA512.Compress.Match
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Padding.Layout
open SHS.Equiv.SHA512.Padding.Equiv
open SHS.Equiv.SHA512.Padding.ByteDecoding
open SHS.Equiv.SHA512.Padding.Parsing
open SHS.Equiv.SHA512.Digest
open SHS.Equiv.Bytes

open SHS.SHA512

namespace SHS.Equiv.SHA512.Pipeline

open scoped SHS.SHA512

/-- The bit-length precondition derived from the byte-length one. -/
theorem bitLen_lt_of_size_lt (data : ByteArray) (h : data.size < 2 ^ 61) :
    (bytesToBitMessage data).length < 2 ^ 128 := by
  have hLen : (bytesToBitMessage data).length = 8 * data.size := by
    simp only [bytesToBitMessage, byteToBits, List.length_flatMap, List.length_map,
      List.length_reverse, List.length_range]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl]
    rw [List.map_const, List.sum_replicate_nat]
    show data.data.toList.length * 8 = 8 * data.size
    rw [Array.length_toList, Nat.mul_comm]; rfl
  have h2128 : (8 : Nat) * 2 ^ 61 < 2 ^ 128 := by decide
  omega

/-- Generalised fold-lift. -/
theorem foldl_compress_lift_gen (blocks : Array (Vector UInt8 128))
    (s : Impl.State) :
    toSpecState (blocks.foldl (fun s b => Impl.compress s (Impl.toU64s b)) s) =
      (blocks.map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress (toSpecState s) := by
  rw [Array.foldl_map]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction blocks.toList generalizing s with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [spec_compress_eq_fused]
    rw [← toSpecState_implCompressFoldl]
    rw [impl_compress_eq_foldl]
    exact ih _

theorem foldl_compress_lift (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512 := by
  rw [← toSpecState_H0_512]
  exact foldl_compress_lift_gen _ _

/-! ## SHA-384 and SHA-512/256 fold-lift -/

theorem foldl_compress_lift_384 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_384) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_384 := by
  rw [← toSpecState_H0_384]
  exact foldl_compress_lift_gen _ _

theorem foldl_compress_lift_512_256 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512_256) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512_256 := by
  rw [← toSpecState_H0_512_256]
  exact foldl_compress_lift_gen _ _

theorem foldl_compress_lift_512_224 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512_224) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512_224 := by
  rw [← toSpecState_H0_512_224]
  exact foldl_compress_lift_gen _ _

end SHS.Equiv.SHA512.Pipeline
