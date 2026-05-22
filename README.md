# FIPS PUB 180-4 - Lean 4 Specification

**[Read the rendered spec →][site]**

A Lean 4 port of [NIST FIPS PUB 180-4][spec] (Secure Hash Standard) in
three layers:

* **`spec/`** — a [literate][literate-programming] transcription of
  the standard covering the full SHA family (SHA-1, SHA-224, SHA-256,
  SHA-384, SHA-512, SHA-512/224, SHA-512/256).  All 1415 NIST CAVP
  vectors pass.  Rendered via [mdgen] + `pandoc`.
* **`impl/`** — a performance-tuned executable SHA-256 implementation
  (~170 MiB/s; ~2.4× slower than `sha256sum`), plus SHA-224 sharing the
  same compression core, and a parallel SHA-512 family (SHA-512,
  SHA-384, SHA-512/224, SHA-512/256) sharing one 80-round 64-bit
  compression core.
* **`equiv/`** — machine-checked equivalence proofs between the impl
  and the spec for the SHA-2 family (SHA-256, SHA-224, SHA-512,
  SHA-384, SHA-512/256, SHA-512/224), pinned to a small classical-axiom
  trust base.

[site]: https://remix7531.com/fips-180-4-lean/
[literate-programming]: https://en.wikipedia.org/wiki/Literate_programming
[spec]: http://dx.doi.org/10.6028/NIST.FIPS.180-4
[mdgen]: https://github.com/Seasawher/mdgen

## Build

```sh
direnv allow       # nix dev shell (or install elan + pandoc manually)
make               # lake build
make test          # all 1415 CAVP vectors
make html          # docs/FIPS-180-4.html
```

## Benchmark

`tests/bench/cavp.sh` times spec vs impl on the SHA-256 NIST CAVP run;
`lake exe stress` measures impl throughput against `sha256sum` on
multi-MB random files.  Steady-state impl throughput is ~170 MiB/s
from 8 MiB up; `sha256sum` saturates at ~410 MiB/s.

## Coverage and trust base

The `impl/` implementation and `equiv/` proofs cover the entire SHA-2
family: SHA-256 / SHA-224 (32-bit, 64-round shared core) and SHA-512 /
SHA-384 / SHA-512/256 / SHA-512/224 (64-bit, 80-round shared core).
SHA-1 is spec-only.

* `SHS.Equiv.SHA256.{compress_correct, sha256_correct, sha224_correct}`
  — per-block + top-level equivalences for the SHA-256 family
  (`data.size < 2 ^ 61`, FIPS 180-4 §5.1.1 bit-length cap).
* `SHS.Equiv.SHA512.{compress_correct, sha512_correct, sha384_correct,
  sha512_256_correct, sha512_224_correct}` — same shape for the
  SHA-512 family (same size bound; FIPS 180-4 §5.1.2 allows a wider
  range but the impl encodes bit length via `UInt64`).

All eight theorems depend only on Lean core's classical axioms
(`propext`, `Classical.choice`, `Quot.sound`); see
`equiv/AxiomCheck.lean` for the pinned set, which fails the build if a
new axiom is introduced.

The proofs equate the **Lean source** of impl and spec; they do not
cover bugs in the Lean compiler, C toolchain, or runtime.

## License

GPL-3.0-or-later.
