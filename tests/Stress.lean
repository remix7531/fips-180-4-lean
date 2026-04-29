import tests.CAVP
import spec
import impl.SHA256

/-! # Large-input stress test

Validates the spec and impl SHA-256 pipelines against GNU `sha256sum`
on multi-MB on-disk test files.  Each test file is read from disk
identically by `sha256sum` (the oracle) and by our hash pipelines, so
all three see the same bytes; the comparison catches any divergence.

The spec is too slow to validate on inputs above ~1 MiB in reasonable
time, so it's skipped above `specMaxBytes`.

Test files are not committed to the repo (they're large and not
deterministic); regenerate via `bench/gen-stress.sh` (also wired up as
`make stress-gen`).  Missing files produce a skip with a hint, not a
failure — so this exe stays useful even when the data isn't present.

Flags:
  `--no-spec`   skip spec validation entirely (impl-only).
  any positional args are treated as additional file paths to test. -/

set_option autoImplicit false

open SHS tests.CAVP RspParser

namespace tests.Stress

/-! ## Default test files -/

/-- The default test files; create with `bench/gen-stress.sh`. -/
def defaultFiles : List String :=
  ["tests/stress/1MiB.bin",
   "tests/stress/8MiB.bin",
   "tests/stress/32MiB.bin"]

/-- Largest input we run through the spec pipeline. -/
def specMaxBytes : Nat := 1024 * 1024  -- 1 MiB

/-! ## sha256sum oracle -/

/-- Run `sha256sum PATH` and parse the 64-char hex digest from stdout.
The output format is `<hex>  <path>\n`. -/
def gnuSha256File (path : String) : IO String := do
  let child ← IO.Process.spawn {
    cmd := "sha256sum",
    args := #[path],
    stdout := .piped,
    stderr := .piped
  }
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let rc ← child.wait
  if rc ≠ 0 then
    throw (IO.userError s!"sha256sum exited {rc}: {stderr}")
  let s := stdout.trimAscii.toString
  if s.length < 64 then
    throw (IO.userError s!"sha256sum output too short: {stdout}")
  return (s.take 64).toString

/-! ## Hashing helpers -/

private def implDigestHex (data : ByteArray) : String :=
  let d := SHS.SHA256.Impl.sha256 data
  byteArrayToHex (d.toList.foldl (·.push ·) ByteArray.empty)

private def specDigestHex (data : ByteArray) : Option String :=
  let bits := bytesToBits data
  if h : bits.length < 2 ^ 64 then some (toHex (SHA256.sha256 bits h)) else none

/-! ## Runner -/

/-- Throughput in KiB/s (integer).  KiB rather than MiB so the integer
division resolves to a non-zero value at our slow spec/impl rates. -/
private def kibPerSec (sz ms : Nat) : Nat :=
  if ms = 0 then 0 else sz * 1000 / ms / 1024

/-- Validate one file: read it, sha256sum it, hash via impl (and spec
when small), compare both to the oracle.  Missing files produce a
warning and `(0, 0)` rather than a failure. -/
def runFile (path : String) (validateSpec : Bool) : IO (Nat × Nat) := do
  if !(← System.FilePath.pathExists path) then
    IO.eprintln s!"[{path}] missing; run `make stress-gen` to populate"
    return (0, 0)
  let data ← IO.FS.readBinFile path
  let tOracle0 ← IO.monoMsNow
  let oracle ← gnuSha256File path
  let tOracle1 ← IO.monoMsNow
  IO.println s!"[{path}] sha256sum: {tOracle1 - tOracle0} ms"
  let mut pass := 0
  let mut fail := 0
  -- Equality comparison forces evaluation; do it inside the timing
  -- brackets so the `monoMsNow` window captures the actual hashing.
  let tImpl0 ← IO.monoMsNow
  let implOk ← IO.ofExcept
    (Except.ok (implDigestHex data == oracle) : Except String _)
  let tImpl1 ← IO.monoMsNow
  let dt := tImpl1 - tImpl0
  IO.println s!"[{path}] impl: {dt} ms ({kibPerSec data.size dt} KiB/s)"
  if implOk then pass := pass + 1
  else
    fail := fail + 1
    IO.eprintln s!"FAIL [{path}] impl: expected {oracle} got {implDigestHex data}"
  if validateSpec ∧ data.size ≤ specMaxBytes then
    let tSpec0 ← IO.monoMsNow
    let specOk ← IO.ofExcept
      (Except.ok (specDigestHex data == some oracle) : Except String _)
    let tSpec1 ← IO.monoMsNow
    let dt := tSpec1 - tSpec0
    IO.println s!"[{path}] spec: {dt} ms ({kibPerSec data.size dt} KiB/s)"
    if specOk then pass := pass + 1
    else
      fail := fail + 1
      IO.eprintln s!"FAIL [{path}] spec: expected {oracle} got {specDigestHex data}"
  return (pass, fail)

end tests.Stress

open tests.Stress

/-- Stress-test entry point.  See module docstring for flags. -/
def main (args : List String) : IO Unit := do
  let withSpec := !args.contains "--no-spec"
  let extra := args.filter (fun a => !a.startsWith "--")
  let files := if extra.isEmpty then defaultFiles else extra
  let pass ← IO.mkRef (0 : Nat)
  let fail ← IO.mkRef (0 : Nat)
  for path in files do
    let (p, f) ← runFile path withSpec
    pass.modify (· + p); fail.modify (· + f)
  let p ← pass.get
  let f ← fail.get
  IO.println s!"\nTotal: {p} passed, {f} failed"
  if f > 0 then IO.Process.exit 1
