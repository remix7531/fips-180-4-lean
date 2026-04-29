.PHONY: all lean test fast-test bench docs html clean

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

# --- Run NIST CAVP test vectors against the spec ---

test:
	lake exe cavp

# --- Fast subset (~10% of vectors, deterministic) for quick iteration ---

fast-test:
	lake exe cavp --fast

# --- Compare spec vs impl execution time on the full CAVP vector set ---

bench:
	bench/cavp.sh

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
