# Equivalence proofs

The proofs relate the byte-oriented SHA-2 implementation in `impl/` to
the bit-oriented specification in `spec/`. State and block lifts map
each implementation word to its `BitVec` view.

## Public correctness theorems

| Namespace | Per-block theorem | Hash theorems |
| --- | --- | --- |
| `SHS.Equiv.SHA256` | `compress_correct` | `sha256_correct`, `sha224_correct` |
| `SHS.Equiv.SHA512` | `compress_correct` | `sha512_correct`, `sha384_correct`, `sha512_256_correct`, `sha512_224_correct` |

Both per-block statements are in `Compress/Match.lean`. The hash
statements are in `Main.lean`. Their byte bound is `data.size < 2 ^ 61`
because the implementation shifts the byte count into a `UInt64` bit
count. The separate SHA-512/t IV checks in the specification use native
computation. The hash proofs use the published IV constants directly.

## Proof boundaries

- **Padding layout.** `Padding/Layout.lean` describes the byte array
  after the separator, zeros, and length field have been added. It
  proves the complete-block and final-block layouts independently of
  the compressor and the word decoder.
- **Streaming and parsing.** `Padding/Equiv.lean` rewrites the
  streaming loop as a fold over those byte blocks.
  `Padding/ByteDecoding.lean` relates the byte layout to the spec's
  bit padding. `Padding/Parsing.lean` then aligns byte windows with
  the spec's block and word slices.
- **Compression.** `Foldl/Schedule.lean` and
  `Foldl/Sequential.lean` express the spec's loops as finite folds.
  Both executable compressors use a 16-word schedule ring. The SHA-256
  proof in `Compress/Match.lean` and the SHA-512 proof in
  `Compress/Fused.lean` track the working variables and the ring contents
  against the fused spec fold. SHA-512's `Compress/Impl.lean` also
  relates the sequential implementation model to the executable fold.
- **Final state and digest.** `Pipeline.lean` combines the padding,
  parsing, and compression results for any initial state.
  `Digest.lean` relates the emitted bytes to the spec's word
  concatenation. Each `Main.lean` proof supplies its IV and chooses
  the corresponding digest result.

`Common/` contains the reusable list, byte, bit vector, and fold
arguments. Word sizes, schedule constants, and ring invariants live with
the corresponding family.

## Verification

Run `lake --wfail build equiv` to build the proof tree with warnings
treated as errors. CI runs Lean's built-in text lint checks with
`lake lint --linters=.all spec equiv.AxiomCheck`.
`AxiomCheck.lean` collects the axioms of all eight public theorems
and checks each against `propext`, `Classical.choice`, and `Quot.sound`.

