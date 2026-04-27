#!/usr/bin/env bash
# Compare spec vs impl execution time on the full NIST CAVP vector set.
set -euo pipefail

cd "$(dirname "$0")/.."

lake build cavp >/dev/null

run() {
  local label="$1" flag="$2"
  local t0 t1
  t0=$(date +%s%3N)
  lake exe cavp -- "$flag" >/dev/null 2>&1
  t1=$(date +%s%3N)
  printf '%-4s : %5d ms\n' "$label" "$((t1 - t0))"
}

run spec --spec
run impl --impl
