# FIPS PUB 180-4 - Lean 4 Specification

**[Read the rendered spec →][site]**

A Lean 4 port of [NIST FIPS PUB 180-4][spec] (Secure Hash Standard) in
three layers:

* **`spec/`** — a [literate][literate-programming] transcription of
  the standard covering the full SHA family (SHA-1, SHA-224, SHA-256,
  SHA-384, SHA-512, SHA-512/224, SHA-512/256). The bundled NIST CAVP
  corpus contains 1415 short and long vectors and 700 Monte Carlo chains.
  The specification is rendered with [mdgen] and `pandoc`.
* **`impl/`** — an executable SHA-256 implementation that shares its
  compression core with SHA-224, and a parallel SHA-512 family (SHA-512,
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

Use `nix develop` to enter the development shell. Outside Nix, use Elan,
Bash, and Pandoc. The project uses Lean 4.36.0.

```sh
lake build spec impl equiv tests
lake test
bash scripts/build-html.sh
```

`lake build` defaults to `spec`. `lake test` runs the full suite.
`lake test -- --fast` samples it. See the [proof checks](equiv/README.md#verification).

`nix build` builds the Lean package and runs the sampled suite.

## Coverage and trust base

The `impl/` implementation and `equiv/` proofs cover the entire SHA-2
family: SHA-256 / SHA-224 (32-bit, 64-round shared core) and SHA-512 /
SHA-384 / SHA-512/256 / SHA-512/224 (64-bit, 80-round shared core).
SHA-1 is spec-only. The test suite exercises both SHA-1 methods.

* `SHS.Equiv.SHA256.{compress_correct, sha256_correct, sha224_correct}`
  — per-block + top-level equivalences for the SHA-256 family
  (`data.size < 2 ^ 61`, FIPS 180-4 §5.1.1 bit-length cap).
* `SHS.Equiv.SHA512.{compress_correct, sha512_correct, sha384_correct,
  sha512_256_correct, sha512_224_correct}` — same shape for the
  SHA-512 family (same size bound; FIPS 180-4 §5.1.2 allows a wider
  range but the impl encodes bit length via `UInt64`).

All eight theorems depend on exactly `propext`, `Classical.choice`, and
`Quot.sound`. `equiv/AxiomCheck.lean` fails the build if a theorem's
axiom set changes.

The two IV generation checks in `spec/SHA512t.lean`, `H0_512_224_correct`
and `H0_512_256_correct`, use `native_decide`. Each depends on an additional
axiom for its compiled computation. The SHA-512 correctness theorems use
the published IV constants directly.

The proofs equate the **Lean source** of impl and spec; they do not
cover bugs in the Lean compiler, C toolchain, or runtime.

## License

LGPL-3.0-or-later. See [LICENSE](LICENSE).
