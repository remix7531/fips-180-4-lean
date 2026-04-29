# FIPS PUB 180-4 - Lean 4 Specification

**[Read the rendered spec →][site]**

A [literate][literate-programming] Lean 4 port of [NIST FIPS PUB 180-4][spec] (Secure Hash
Standard) — the standard's prose and its Lean code live side-by-side in one
document, with each part driving the other. [mdgen] and `pandoc` render the
source into HTML. All 1415 NIST CAVP test vectors pass.

[site]: https://remix7531.com/fips-180-4-lean/
[literate-programming]: https://en.wikipedia.org/wiki/Literate_programming
[spec]: http://dx.doi.org/10.6028/NIST.FIPS.180-4
[mdgen]: https://github.com/Seasawher/mdgen

## Build

```sh
direnv allow       # nix dev shell (or install elan + pandoc manually)
make               # lake build
make test          # all 1415 CAVP vectors
make fast-test     # ~10% sample
make html          # docs/FIPS-180-4.html
```

## Benchmark

`bench/cavp.sh` times the full 1415-vector CAVP run for both pipelines.
On a modern consumer AMD CPU:

| pipeline | time |
|---|---|
| spec | ~28.4 s |
| impl | ~1.2 s (≈24× faster) |

The spec is a direct transcription of the standard and is not optimised;
the impl is a `UInt32`-based implementation and is being proven
equivalent to the spec under `equiv/`.

## Layout

```
spec.lean, spec/    Lean + markdown chapters (the literate spec)
impl/               UInt32-based reference port (SHA-256)
equiv/              spec ↔ impl equivalence proofs
tests/              CAVP runner and vector parser
bench/              timing scripts
support/            pandoc filters, CSS, Lean syntax definition
```

## Coverage

The literate spec covers the entire Secure Hash Standard: **SHA-1, SHA-224,
SHA-256, SHA-384, SHA-512, SHA-512/224, SHA-512/256**.  Every algorithm
is exercised against the corresponding NIST CAVP test vectors via
`make test`.

The `impl/` reference implementation and the `equiv/` machine-checked
equivalence proof currently cover **only SHA-256**.  The other
algorithms in the spec are not yet paired with a verified
implementation.

The headline correctness theorems are:

* `SHS.Equiv.SHA256.compress_correct` — `Impl.compress` agrees with the
  spec's per-block compression function.
* `SHS.Equiv.SHA256.sha256_correct` — `Impl.sha256` agrees with
  `SHS.SHA256.sha256` for all `data : ByteArray` with `data.size < 2 ^
  61` (the FIPS 180-4 §5.1.1 bit-length cap converted to bytes).
  `Impl.sha256` `panic!`s on oversized inputs rather than producing a
  wrong digest.

## Trust base

The pinned axiom sets (see `equiv/AxiomCheck.lean`):

* **`compress_correct`** (the SHA-256 compression function): only
  `propext`, `Classical.choice`, `Quot.sound` — Lean core's classical
  axioms.
* **`sha256_correct`** (the full byte-in / byte-out hash): the three
  classical axioms, plus `Lean.ofReduceBool` and `Lean.trustCompiler`
  emitted by three remaining `bv_decide` calls in the byte ↔ `BitVec`
  digest/parsing bridges (`equiv/SHA256/ToU32s.lean`,
  `equiv/SHA256/Digest.lean`).  These two extra axioms state that the
  native compiler's `Bool` reduction is sound.

### Scope of the proofs

The correctness theorems prove equivalence between the **Lean source**
of `Impl.sha256` and the literate spec.  They do **not** prove that the
compiled binary produced by `lake build` (which lowers Lean → C → native
code through the Lean compiler and a C toolchain) computes the same
function.  Bugs in the Lean compiler, the C compiler, or the runtime
are out of scope and are not covered by `sha256_correct`.

## License

GPL-3.0-or-later.
