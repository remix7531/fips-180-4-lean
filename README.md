# FIPS PUB 180-4 - Lean 4 Specification

**[Read the rendered spec →][site]**

A Lean 4 port of [NIST FIPS PUB 180-4][spec] (Secure Hash Standard) in
three layers:

* **`spec/`** — a [literate][literate-programming] transcription of
  the standard covering the full SHA family (SHA-1, SHA-224, SHA-256,
  SHA-384, SHA-512, SHA-512/224, SHA-512/256).  All 1415 NIST CAVP
  vectors pass.  Rendered via [mdgen] + `pandoc`.
* **`impl/`** — a performance-tuned executable SHA-256 implementation
  (~177 MiB/s; ~2.3× slower than `sha256sum`).
* **`equiv/`** — machine-checked equivalence proofs between the impl
  and the spec, with public theorems `compress_correct` and
  `sha256_correct` pinned to a small classical-axiom trust base.

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

`bench/cavp.sh` times spec vs impl on the SHA-256 NIST CAVP run;
`lake exe stress` measures impl throughput against `sha256sum` on
multi-MB random files.  Steady-state impl throughput is ~177 MiB/s
from 8 MiB up; `sha256sum` saturates at ~410 MiB/s.

## Coverage and trust base

The `impl/` implementation and `equiv/` proofs cover only SHA-256;
the other algorithms are spec-only.

* `SHS.Equiv.SHA256.compress_correct` — `Impl.compress` agrees with
  the spec's per-block compression function.  Depends only on Lean
  core's classical axioms (`propext`, `Classical.choice`, `Quot.sound`).
* `SHS.Equiv.SHA256.sha256_correct` — `Impl.sha256` agrees with
  `SHS.SHA256.sha256` for all `data` with `data.size < 2 ^ 61` (the
  FIPS 180-4 §5.1.1 bit-length cap).  Adds `Lean.ofReduceBool` and
  `Lean.trustCompiler` from three `bv_decide` calls in the byte ↔
  `BitVec` bridges.  See `equiv/AxiomCheck.lean` for the pinned set.

The proofs equate the **Lean source** of impl and spec; they do not
cover bugs in the Lean compiler, C toolchain, or runtime.

## License

GPL-3.0-or-later.
