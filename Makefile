.PHONY: all lean test full-test bench stress stress-gen docs html clean

all: lean

# --- Lean ---
#
# Build every library and executable in the project: `spec` (the default
# Lake target), the `impl` reference SHA-256 implementation, the `equiv`
# spec ↔ impl equivalence proofs, and the `tests` CAVP runner.  Building
# `equiv` from a clean `.lake` is the regression gate for the proof —
# without it, breakage in `equiv/SHA256/Foldl/*` or `equiv/AxiomCheck`
# would only show up locally where caches mask it.
lean:
	lake build spec impl equiv tests

# --- NIST CAVP test vectors ---
#
# `test` runs ~1/10 of short/long vectors and 1/10 of MCT chains across
# all seven SHA-family algorithms; tens of seconds, suitable for CI and
# default `make`.  `full-test` runs the complete CAVS workload (all
# vectors, all 100 MCT chains × 7 algorithms) and takes many minutes.

test:
	lake exe cavp --fast

full-test:
	lake exe cavp

# --- Compare spec vs impl execution time on the full CAVP vector set ---

bench:
	bench/cavp.sh

# --- Large-input stress test against GNU sha256sum ---
#
# `stress-gen` populates `tests/stress/` with random binary files via dd
# (1 MiB, 8 MiB, 32 MiB).  `stress` reads each file, hashes it via spec
# (small only) and impl, and compares against `sha256sum`.

stress-gen:
	bench/gen-stress.sh

stress: stress-gen
	lake exe stress

# --- Generate markdown from Lean via mdgen ---

docs:
	lake build mdgen
	mkdir -p docs
	lake exe mdgen spec docs

html: docs
	cp spec/doc-logo.png docs/
	cat spec/01-intro.md \
	    docs/Notation.md \
	    docs/Functions.md \
	    docs/Preprocessing.md \
	    docs/SHA512t.md \
	    docs/HashAlgorithms.md \
	    docs/SHA512tHash.md \
	    spec/99-trailer.md > docs/FIPS-PUB-180-4.md
	pandoc docs/FIPS-PUB-180-4.md \
		--lua-filter=support/toc-placement.lua \
		--lua-filter=support/eqn-tag.lua \
		--standalone --katex=https://cdn.jsdelivr.net/npm/katex@latest/dist/ \
		--highlight-style=tango \
		--syntax-definition=support/lean.xml \
		-H support/style.html \
		-o docs/FIPS-180-4.html

clean:
	rm -rf docs
