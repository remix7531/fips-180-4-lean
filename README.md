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

## License

GPL-3.0-or-later.
