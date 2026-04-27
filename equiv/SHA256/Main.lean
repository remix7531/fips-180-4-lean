import equiv.SHA256.Pipeline

/-! # SHA-256 spec ↔ implementation — main user-facing theorems

This file contains exactly the two headline equivalences:

* `compress_correct` — per-block: `Impl.compress` ↔ `SHS.SHA256.compress`.
* `sha256_correct`   — top-level: `Impl.sha256` ↔ `SHS.SHA256.sha256`.

Both are proved as pure `_eq_`-rewrite chains over the bridges defined
in the sibling modules. -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Compress.Impl
open SHS.Equiv.SHA256.Compress.Match
open SHS.Equiv.SHA256.Foldl.Fused
open SHS.Equiv.SHA256.Digest
open SHS.Equiv.SHA256.Padding.Equiv
open SHS.Equiv.SHA256.Padding.ByteDecoding
open SHS.Equiv.SHA256.Padding.Parsing
open SHS.Equiv.SHA256.Pipeline

open SHS.SHA256

namespace SHS.Equiv.SHA256

open scoped SHS.SHA256

/-- The implementation's `Impl.compress` agrees with the spec's
`SHS.SHA256.compress` once both inputs are viewed in the spec's
`BitVec 32` representation via `toSpecState` / `toSpecBlock`.

Proof: a chain of three `_eq_` rewrites along the compress ladder
(impl source → impl factored fold → fused spec → spec source). -/
theorem compress_correct (state : Impl.State) (block : Impl.Block) :
    toSpecState (Impl.compress state block) =
      SHS.SHA256.compress (toSpecState state) (toSpecBlock block) := by
  rw [← impl_compress_eq_foldl,
      toSpecState_implCompressFoldl,
      ← spec_compress_eq_fused]

/-- The bytewise `Impl.sha256` agrees with the spec's bitwise `sha256`,
viewing the 32-byte digest as a 256-bit big-endian BitVec.

The hypothesis `data.size < 2 ^ 61` ensures `8 * data.size < 2 ^ 64` so
that the FIPS 180-4 §5.1.1 bit-length encoding fits in a single
`UInt64` (the 64-bit-length suffix appended during padding).

Proof: a chain of six `_eq_` rewrites — unfold `Impl.sha256` to its
refactored block-list form, unfold to `extractDigest ∘ foldl`, push
`digestBitVec` through `extractDigest` into `toSpecState`, lift the
fold to the spec side, replace impl-blocks with `parse ∘ pad`, then
fold the spec definition back. -/
theorem sha256_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec (Impl.sha256 data) =
      SHS.SHA256.sha256 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  rw [impl_sha256_eq_refactored,
      implSha256Refactored_eq_extractDigest,
      digestBitVec_extract,
      foldl_compress_lift,
      implPaddedBlocks_lift_eq_parsePad data h,
      ← SHA256_sha256_eq_concat]

end SHS.Equiv.SHA256
