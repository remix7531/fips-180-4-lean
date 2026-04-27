# `equiv/` — spec ↔ implementation equivalence

This directory bridges the impl-shaped intermediate layer (`impl/`) to the
FIPS-180-4 spec (`spec/`).  The proof threads through several intermediate
forms of `compress`, each with a different shape but computing the same
function.  This document maps out those forms and the bridges between them.

## Public API

Three names are user-facing:

| name | location |
|---|---|
| `SHS.SHA256.Impl.compress` | `impl/SHA256.lean` |
| `SHS.SHA256.Impl.sha256`   | `impl/SHA256.lean` |
| `SHS.SHA256.Equiv.compress_correct` | `equiv/SHA256/Main.lean` |
| `SHS.SHA256.Equiv.sha256_correct`   | `equiv/SHA256/Main.lean` |

`SHS.SHA256.compress` and `SHS.SHA256.sha256` (the spec) are also
user-facing, in `spec/`.  Everything else in `equiv/` is internal proof
machinery.

## Directory layout

```
equiv/
├── README.md           this file
├── Common/             shared infrastructure (word-size agnostic)
│   ├── Loop.lean       forIn ↔ Fin.foldl, loop-fusion, state-bijection transport
│   ├── Bytes.lean      byteToBits + flatMap_byteToBits_{drop,take}_8
│   ├── ByteArray.lean  ByteArray.get!_{append,push,appendZeros}_* helpers
│   ├── Chunks.lean     List.toChunks_{cons_step,eq_drop_take,length_eq}
│   ├── ArrayFold.lean  Array.foldl ∘ ofFn ↔ Fin.foldl, fin_foldl_ext
│   └── FromBits.lean   Word.fromBits structural lemmas (foldl_init, append_same_width)
└── SHA256/             SHA-256-specific equivalence proofs
    ├── Bridge.lean     UInt32 ↔ BitVec 32 operator bridges
    ├── Lift.lean       toSpecState, toSpecBlock + size/getElem! simp lemmas
    ├── Functions.lean  Ch / Maj / bigSigma0/1 / smallSigma0/1 bridges
    ├── Constants.lean  K32 ↔ K
    ├── Foldl/
    │   ├── Schedule.lean    schedule as Fin.foldl 64
    │   ├── Sequential.lean  compress as sequential foldl + tuple bridge
    │   └── Fused.lean       compress as fused foldl (matches impl)
    ├── Compress/
    │   ├── Impl.lean       impl-side factoring + per-step bridges
    │   └── Match.lean      MatchAfter invariant + cross-side meet (toSpecState_implCompressFoldl)
    ├── ToU32s.lean     block-level byte → word lift (beU32 ↔ Word.fromBits)
    ├── Padding/
    │   ├── Layout.lean byte-level paddedBlock layout: 3 cases (complete / final<56 / final≥56)
    │   └── Equiv.lean  byte ↔ bit pad/parse equivalence; impl_sha256_eq_refactored
    ├── Digest.lean     digestBitVec / extractDigest / digest_list_eq_8chunks
    └── Main.lean       user-facing theorems: compress_correct, sha256_correct
```

The `Common/` layer is genuinely word-size agnostic: every lemma is
stated over `BitVec n`, `List`, `Array`, `ByteArray`, or `Nat` with no
SHA-256 constants.  A parallel `equiv/SHA512/` directory mirrors
`equiv/SHA256/` (different rotation/shift constants in `Bridge`,
`Functions`, `Constants`; 80-round schedule and 16-word state in
`Compress`/`Foldl`; 128-byte blocks in `Padding`; 64-byte digest in
`Digest`) and reuses `Common/` unchanged.

## The sha256 ladder

The top-level `sha256_correct` composes four bridges, each living in
its own module:

```
  Impl.sha256 data
    ↑ impl_sha256_eq_refactored        (Padding/Equiv: streaming pad ↔ block list)
    ↑ foldl_compress_lift              (Main: per-block compress_correct over the fold)
    ↑ implPaddedBlocks_lift_eq_parsePad (Padding/Equiv: byte-level vs bit-level parse)
    ↑ digestBitVec_extract             (Digest: 32-byte BE digest ↔ 256-bit BitVec)
  SHS.SHA256.sha256 (bytesToBitMessage data) _
```

The per-block `compress_correct` itself reduces to the chain below.

## The compress ladder

Each bridge theorem is an *equality*; the arrows go both ways.

```
                  ┌────────────────────────────────────────┐
                  │  SHS.SHA256.compress                   │   spec source
                  │  ──────────────────                    │   (surface form)
                  │  Id.run do { mut a..h; for t in [0:64] │
                  │    do …; return #[a + H[0]!, …] }      │
                  └────────────────┬───────────────────────┘
                                   ▲
                                   │   spec_compress_eq_seq
                                   │   (forIn → Fin.foldl,
                                   │    MProd 8-tuple → SpecVars,
                                   │    pre-computes schedule)
                                   ▼
                  ┌────────────────────────────────────────┐
                  │  specCompressSeq                       │   spec, sequential
                  │  ────────────────                      │
                  │  let W := schedule M                   │
                  │  addH H                                │
                  │    (Fin.foldl 64                       │
                  │       (specRoundStep W) (initVars H))  │
                  └────────────────┬───────────────────────┘
                                   ▲
                                   │   spec_compress_eq_fused
                                   │   (interleave schedule and round
                                   │    into one fold)
                                   ▼
                  ┌────────────────────────────────────────┐
                  │  specCompressFused                     │   spec, fused
                  │  ──────────────────                    │
                  │  addH H                                │
                  │    (Fin.foldl 64 (specFusedStep M)     │
                  │       (zeroSched, initVars H)).2       │
                  └────────────────┬───────────────────────┘
                                   ▲
                                   │   toSpecState_implCompressFoldl
                                   │   (the cross-side meet:
                                   │    ring-buffer ↔ schedule-array
                                   │    invariant)
                                   ▼
                  ┌────────────────────────────────────────┐
                  │  implCompressFoldl                     │   impl, factored
                  │  ──────────────────                    │
                  │  let (_, s') :=                        │
                  │    Fin.foldl 64 implFusedStep          │
                  │      (block, state)                    │
                  │  Vector.zipWith (· + ·) state s'       │
                  └────────────────┬───────────────────────┘
                                   ▲
                                   │   impl_compress_eq_foldl (rfl)
                                   ▼
                  ┌────────────────────────────────────────┐
                  │  Impl.compress                         │   impl source
                  │  ─────────────                         │   (the inlined
                  │  inlined 25-line lambda inside         │    25-line lambda
                  │  Fin.foldl 64                          │    is the impl's
                  │                                        │    surface form)
                  └────────────────────────────────────────┘
```

The main theorem `compress_correct` is essentially "the top equals the
bottom".  Its proof is just the chain of bridge rewrites.  The actual
hard work lives in `toSpecState_implCompressFoldl`, which connects
`implCompressFoldl` to `specCompressFused` after lifting (via the
`MatchAfter` ring-buffer ↔ schedule-array invariant).

## Naming convention

Across `equiv/` we follow Mathlib-style conventions:

- **Definitions / types**: `camelCase` (e.g. `byteToBits`, `paddedBlock`,
  `implPaddedBytes`, `toSpecState`).
- **Theorems / lemmas**: `snake_case` (e.g. `paddedBlock_complete`,
  `bytesToBitMessage_append`, `fromBits_byteToBits`).
- **Namespaces**: `PascalCase`, one sub-namespace per file, matching the
  file path:

  | file | namespace |
  |---|---|
  | `equiv/Common/Foo.lean` | `SHS.Equiv.Foo` |
  | `equiv/SHA256/Foo.lean` | `SHS.Equiv.SHA256.Foo` |
  | `equiv/SHA256/Foldl/Foo.lean` | `SHS.Equiv.SHA256.Foldl.Foo` |
  | `equiv/SHA256/Padding/Foo.lean` | `SHS.Equiv.SHA256.Padding.Foo` |

  Top-level `SHS.Equiv` collects all spec ↔ implementation
  equivalence proofs.  `Common/` contents sit at `SHS.Equiv.*` so they
  are reusable across hash families.  Per-algorithm work nests one
  level deeper: `SHS.Equiv.SHA256.*`, `SHS.Equiv.SHA512.*` (when it
  lands).  Names within each sub-namespace drop the module prefix
  where redundant (e.g.
  `SHS.Equiv.SHA256.Padding.Layout.paddedBlock_complete`, not
  `…paddedBlock_paddedBlock_complete`).

## File-level call graph (from `Main.lean`)

Reading top-down from `Main.lean`, each module is consumed by the one
above it.  Arrows are `imports` edges; the right column says what the
file is responsible for.

```
Main.lean              compress_correct, sha256_correct
  └─ Pipeline.lean     foldl_compress_lift, bitLen_lt_of_size_lt
       ├─ Compress/Match.lean        toSpecState_implCompressFoldl, MatchAfter
       │    └─ Compress/Impl.lean    impl factored fold + per-step bridges, impl_compress_eq_foldl
       │    ├─ Lift.lean             toSpecState / toSpecBlock + getElem! / size simp
       │    ├─ Functions.lean        Ch / Maj / Σ₀ / Σ₁ / σ₀ / σ₁ bridges
       │    │    └─ Bridge.lean      UInt32 ↔ BitVec 32 operator bridges
       │    ├─ Constants.lean        K32 ↔ K
       │    └─ Foldl/Fused.lean      spec_compress_eq_fused
       │         ├─ Foldl/Schedule.lean    schedule_eq_foldl  (uses Common/Loop)
       │         └─ Foldl/Sequential.lean  spec_compress_eq_seq (8-tuple ↔ SpecVars)
       └─ Padding/Equiv.lean       impl_sha256_eq_refactored, implPaddedBlocks_lift_eq_parsePad,
                                   bytesToBitMessage_implPaddedBytes
            ├─ Padding/Layout.lean   byte-level paddedBlock layout (3 cases)
            ├─ Digest.lean           digestBitVec_extract  (32-byte BE ↔ 256-bit)
            ├─ ToU32s.lean           Impl.toU32s ↔ Word.fromBits via beU32
            └─ Common/{Bytes,ByteArray,Chunks,ArrayFold,FromBits}.lean   shared infrastructure
```

`Common/Loop.lean` is also imported transitively (by `Foldl/Schedule.lean`).

## Direction

All bridge theorems are stated **impl → spec**: lift `UInt32` values
to `BitVec 32` via `UInt32.toBitVec`, then equality lives on the
spec's representation.  This direction is total (no size-precondition
hypotheses) and leaves impl values size-typed (`Vector`).

## Naming conventions

If a name lives on both sides (e.g. `compress`), it carries a
`spec`/`impl` prefix.  Side-less names exist on at most one side.  The
side-less theorem `compress_correct` is the cross-side bridge between
the spec source and impl source; its proof is just the chain of bridge
rewrites.  The actual hard work lives in `toSpecState_implCompressFoldl`,
which connects `implCompressFoldl` to `specCompressFused` after lifting
(the ring-buffer ↔ schedule-array invariant).

