# FIPS PUB 180-4 - Lean 4 Specification

A literate Lean 4 port of [NIST FIPS PUB 180-4][spec] (Secure Hash Standard).
The standard's prose lives beside its Lean code; [mdgen] and `pandoc` render
both into HTML. All 1415 NIST CAVP test vectors pass.

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

## Layout

```
spec.lean, spec/    Lean + markdown chapters (the literate spec)
tests/              CAVP runner and vector parser
support/            pandoc filters, CSS, Lean syntax definition
```

## License

GPL-3.0-or-later.
