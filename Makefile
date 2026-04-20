.PHONY: all lean test fast-test docs html clean

all: lean

# --- Lean ---

lean:
	lake build

# --- Run NIST CAVP test vectors against the spec ---

test:
	lake exe cavp

# --- Fast subset (~10% of vectors, deterministic) for quick iteration ---

fast-test:
	lake exe cavp --fast

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
		--standalone --mathjax --highlight-style=tango \
		--syntax-definition=support/lean.xml \
		-H support/style.html \
		-o docs/FIPS-180-4.html

clean:
	rm -rf docs
