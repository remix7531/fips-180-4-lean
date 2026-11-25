#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lake build mdgen
mkdir -p docs
lake exe mdgen spec docs

cp spec/doc-logo.png docs/
{
    cat spec/01-intro.md \
        docs/Notation.md \
        docs/Functions.md \
        docs/Preprocessing.md \
        docs/SHA512t.md \
        docs/HashAlgorithms.md
    for family in SHA1 SHA256 SHA512; do
        printf '\n'
        cat "docs/HashAlgorithms/$family.md"
    done
    cat docs/SHA512tHash.md spec/99-trailer.md
} > docs/FIPS-PUB-180-4.md

pandoc docs/FIPS-PUB-180-4.md \
    --lua-filter=spec/support/toc-placement.lua \
    --lua-filter=spec/support/eqn-tag.lua \
    --standalone --katex=https://cdn.jsdelivr.net/npm/katex@latest/dist/ \
    --highlight-style=tango \
    --syntax-definition=spec/support/lean.xml \
    -H spec/support/style.html \
    -o docs/FIPS-180-4.html
