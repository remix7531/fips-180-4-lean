import tests.CAVP

open tests.CAVP

/-- Parse `--key=val` from `args`, returning `val` for the first match. -/
private def argValue? (args : List String) (key : String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith key then some ((a.drop key.length).toString) else none)

/-- CAVP test runner.  All workload knobs come from CLI; spec and impl
pipelines are treated symmetrically.

Flags:
  `--spec` / `--impl`     restrict to one pipeline (default: both).
  `--alg=NAME`            restrict to a single algorithm name.
  `--no-monte`            skip the Monte-Carlo Test entirely.
  `--monte-only`          skip short/long vectors and negative tests;
                          run only the Monte-Carlo Test.
  `--fast`                run only 1/10 of short/long vectors and a
                          single MCT chain per algorithm (each chain is
                          1000 inner hashes, so MCT is sampled more
                          aggressively than short/long).  Vector counts
                          come from the .rsp files and are otherwise
                          never capped. -/
def main (args : List String) : IO Unit := do
  let fast       := args.contains "--fast"
  let runSpec    := !args.contains "--impl"
  let runImpl    := !args.contains "--spec"
  let monteOnly  := args.contains "--monte-only"
  let runMonte   := !args.contains "--no-monte"
  let runVectors := !monteOnly
  let sample     := if fast then some 10 else none
  -- MCT chains are 1000× costlier per unit than a short/long vector,
  -- so sample them harder under `--fast`: keep 1 of 100.
  let monteSample := if fast then some 100 else none
  let algFilter := argValue? args "--alg="
  let keep alg  := algFilter.all (· = alg)
  let dir       := "tests/vectors"
  -- `--impl` runs an impl-only sweep but only SHA-256 has a verified
  -- implementation, so the user must pin `--alg=SHA256` to be explicit.
  if args.contains "--impl" ∧ algFilter ≠ some "SHA256" then
    IO.eprintln "--impl requires --alg=SHA256 (no other impl is available yet)"
    IO.Process.exit 2
  let pass ← IO.mkRef (0 : Nat)
  let fail ← IO.mkRef (0 : Nat)
  let report (label path : String) (r : IO (Nat × Nat)) : IO Unit := do
    let (p, f) ← r
    IO.println s!"{label}: {p} passed, {f} failed  ({path})"
    pass.modify (· + p); fail.modify (· + f)
  if runVectors ∧ runSpec then
    for (alg, path) in specCases dir do
      if keep alg then
        report s!"spec {alg}" path (runFile s!"spec {alg}" path (specHash alg) sample)
  if runVectors ∧ runImpl ∧ keep "SHA256" then
    for path in implCases dir do
      report "impl SHA256" path (runFile "impl SHA256" path implSha256Hash sample)
  if runMonte then
    if runImpl ∧ keep "SHA256" then
      let path := s!"{dir}/SHA256Monte.rsp"
      report "impl SHA256 Monte" path
        (runFileMonte "impl SHA256" path implSha256HashBytes monteSample)
    if runSpec then
      for (alg, path) in specMonteCases dir do
        if keep alg then
          report s!"spec {alg} Monte" path
            (runFileMonte s!"spec {alg}" path (specHashBytes alg) monteSample)
  if runVectors ∧ algFilter.isNone then
    let (p, f) ← runNegativeTests
    IO.println s!"negative tests: {p} passed, {f} failed"
    pass.modify (· + p); fail.modify (· + f)
  let p ← pass.get
  let f ← fail.get
  IO.println s!"\nTotal: {p} passed, {f} failed"
  if f > 0 then IO.Process.exit 1
