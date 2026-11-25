#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
repository=$PWD
runner=${1:?expected the absolute path to the compiled CAVP runner}

output=$("$runner" --spec --alg=SHA1 --no-monte)
if [[ "$output" != *"spec SHA1 bit-oriented: 1 passed, 0 failed"* ||
      "$output" != *"spec SHA1 alternate: 1 passed, 0 failed"* ]]; then
  printf 'FAIL cavp skipped supplemental SHA-1 vectors\n%s\n' "$output" >&2
  exit 1
fi

fixtures=$(mktemp -d)
trap 'rm -rf -- "$fixtures"' EXIT
cd "$fixtures"
mkdir -p tests/vectors

expect_failure() {
  local expected_status="$1" diagnostic="$2" output status
  shift 2
  if output=$("$runner" "$@" 2>&1); then
    status=0
  else
    status=$?
  fi
  if [[ "$status" != "$expected_status" || "$output" != *"$diagnostic"* ]]; then
    printf 'FAIL cavp %s\nExpected status %s and diagnostic %s\nGot status %s\n%s\n' \
      "$*" "$expected_status" "$diagnostic" "$status" "$output" >&2
    exit 1
  fi
}

expect_failure 2 "unknown argument --typo" --typo
expect_failure 2 "unknown algorithm BOGUS" --alg=BOGUS
expect_failure 2 "at most one --alg" --alg=SHA1 --alg=SHA256
expect_failure 2 "repeated argument --fast" --fast --fast
expect_failure 2 "mutually exclusive" --spec --impl
expect_failure 2 "mutually exclusive" --no-monte --monte-only
expect_failure 2 "--impl requires --alg" --impl
expect_failure 2 "--impl requires --alg" --impl --alg=SHA1

short=tests/vectors/SHA256ShortMsg.rsp
monte=tests/vectors/SHA256Monte.rsp
cp "$repository/tests/vectors/SHA256LongMsg.rsp" tests/vectors/
sha256_empty=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
printf -v zero_digest '%064d' 0
vectors=(--impl --alg=SHA256 --no-monte)
chains=(--impl --alg=SHA256 --monte-only)

write_vector() {
  printf 'Len = %s\nMsg = %s\nMD = %s\n' "$1" "$2" "$3"
}

printf '# No vectors\n[L = 32]\n' > "$short"
expect_failure 1 "no vectors selected" "${vectors[@]}"
printf 'Len = 0\nMsg = 00\n' > "$short"
expect_failure 1 "missing MD" "${vectors[@]}"
printf 'Len = 0\nLen = 8\n' > "$short"
expect_failure 1 "duplicate field Len" "${vectors[@]}"
printf 'Len 0\n' > "$short"
expect_failure 1 "expected key = value" "${vectors[@]}"
printf '[L = 64]\n' > "$short"
expect_failure 1 "expected L = 32" "${vectors[@]}"
write_vector invalid 00 "$sha256_empty" > "$short"
expect_failure 1 "invalid Len" "${vectors[@]}"
write_vector 0 zz "$sha256_empty" > "$short"
expect_failure 1 "invalid Msg hex" "${vectors[@]}"
write_vector 16 00 "$sha256_empty" > "$short"
expect_failure 1 "requires 2 message bytes" "${vectors[@]}"
write_vector 0 00 zz > "$short"
expect_failure 1 "invalid MD hex" "${vectors[@]}"
write_vector 0 00 00 > "$short"
expect_failure 1 "expected MD to contain 32 bytes" "${vectors[@]}"
write_vector 0 00 "$zero_digest" > "$short"
expect_failure 1 "FAIL impl SHA256 Len=0" "${vectors[@]}"
write_vector 5 68 "$sha256_empty" > "$short"
expect_failure 1 "no vectors selected" "${vectors[@]}"
write_vector 0 00 "$sha256_empty" > "$short"
printf '\nLen = 8\nMsg = 00\n' >> "$short"
expect_failure 1 "vector 2: missing MD" "${vectors[@]}" --fast

printf 'Seed = zz\n' > "$monte"
expect_failure 1 "invalid Seed hex" "${chains[@]}"
printf 'Seed = %s\n' "$zero_digest" > "$monte"
expect_failure 1 "no Monte Carlo chains selected" "${chains[@]}"
printf '\nCOUNT = 0\n' >> "$monte"
expect_failure 1 "Monte Carlo record 0: missing MD" "${chains[@]}"
printf 'Seed = %s\n\nCOUNT = 1\nMD = %s\n' "$zero_digest" "$zero_digest" > "$monte"
expect_failure 1 "expected COUNT = 0" "${chains[@]}"
printf 'Seed = %s\n\nCOUNT = 0\nMD = %s\n' "$zero_digest" "$zero_digest" > "$monte"
expect_failure 1 "no Monte Carlo chains selected" "${chains[@]}" --fast
expect_failure 1 "FAIL impl SHA256 Monte COUNT=0" "${chains[@]}"

check_padding_boundary() {
  local algorithm="$1" empty_digest="$2" wrong_digest msg len
  shift 2
  local short="tests/vectors/${algorithm}ShortMsg.rsp"
  cp "$repository/tests/vectors/${algorithm}LongMsg.rsp" tests/vectors/
  printf -v wrong_digest '%0*d' "${#empty_digest}" 0
  write_vector 0 00 "$empty_digest" > "$short"
  for len in "$@"; do
    printf -v msg '%0*d' "$((len / 4))" 0
    printf '\n' >> "$short"
    write_vector "$len" "$msg" "$wrong_digest" >> "$short"
  done
  # Both boundary records are outside the ordinary 1-in-10 sample.
  for len in "$@"; do
    expect_failure 1 "FAIL impl $algorithm Len=$len" --impl "--alg=$algorithm" --no-monte --fast
  done
}

sha512_empty=cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e
check_padding_boundary SHA256 "$sha256_empty" 440 448
check_padding_boundary SHA512 "$sha512_empty" 888 896

printf 'CAVP rejection and padding boundary checks passed\n'
