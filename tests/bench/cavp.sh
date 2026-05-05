#!/usr/bin/env bash
# Compare spec vs impl execution time on the NIST CAVP vector set.
#
# Always pinned to SHA-256 (the only algorithm with a verified
# implementation) so the two numbers cover the same workload.
# Reports four timings: spec/impl on the full short/long vector set,
# and spec/impl on the Monte-Carlo chains (the latter sampled to 1/10
# via `--fast` — full MCT would take many minutes per pipeline).
set -euo pipefail

cd "$(dirname "$0")/.."

lake build cavp >/dev/null

run() {
  local label="$1"
  shift
  local t0 t1
  t0=$(date +%s%3N)
  lake exe cavp -- "$@" >/dev/null 2>&1
  t1=$(date +%s%3N)
  printf '%-18s : %5d ms\n' "$label" "$((t1 - t0))"
}

run "spec short/long" --spec --alg=SHA256 --no-monte
run "impl short/long" --impl --alg=SHA256 --no-monte
run "spec MCT chains" --spec --alg=SHA256 --monte-only --fast
run "impl MCT chains" --impl --alg=SHA256 --monte-only --fast
