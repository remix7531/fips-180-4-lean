#!/usr/bin/env bash
# Populate `tests/stress/` with the default stress-test data files.
# Each file is created once with `dd if=/dev/urandom`; rerun deletes
# nothing — existing files are kept.  The exact bytes don't matter
# (the test compares spec/impl to whatever sha256sum reports), only
# that the files exist and are stable across runs.
set -euo pipefail

cd "$(dirname "$0")/.."

mkdir -p tests/stress

gen() {
  local path="$1" bs="$2" count="$3"
  if [[ -f "$path" ]]; then
    printf 'kept   %s (%s bytes)\n' "$path" "$(stat -c %s "$path" 2>/dev/null || stat -f %z "$path")"
  else
    dd if=/dev/urandom of="$path" bs="$bs" count="$count" status=none
    printf 'wrote  %s\n' "$path"
  fi
}

gen tests/stress/1MiB.bin   1M  1
gen tests/stress/8MiB.bin   1M  8
gen tests/stress/32MiB.bin  1M  32
gen tests/stress/128MiB.bin 1M  128
gen tests/stress/512MiB.bin 1M  512
