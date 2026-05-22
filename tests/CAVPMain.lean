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
  -- `--impl` runs an impl-only sweep.  SHA-1 is spec-only, so the user
  -- must pin one of the six SHA-2 algorithms to be explicit.
  if args.contains "--impl" ∧ algFilter ≠ some "SHA256" ∧ algFilter ≠ some "SHA224"
      ∧ algFilter ≠ some "SHA512" ∧ algFilter ≠ some "SHA384"
      ∧ algFilter ≠ some "SHA512_256" ∧ algFilter ≠ some "SHA512_224" then
    IO.eprintln "--impl requires --alg=SHA{1,224,256,384,512,512_224,512_256}"
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
  if runVectors ∧ runImpl ∧ keep "SHA224" then
    for path in implCases224 dir do
      report "impl SHA224" path (runFile "impl SHA224" path implSha224Hash sample)
  if runVectors ∧ runImpl ∧ keep "SHA512" then
    for path in implCases512 dir do
      report "impl SHA512" path (runFile "impl SHA512" path implSha512Hash sample)
  if runVectors ∧ runImpl ∧ keep "SHA384" then
    for path in implCases384 dir do
      report "impl SHA384" path (runFile "impl SHA384" path implSha384Hash sample)
  if runVectors ∧ runImpl ∧ keep "SHA512_256" then
    for path in implCases512_256 dir do
      report "impl SHA512_256" path (runFile "impl SHA512_256" path implSha512_256Hash sample)
  if runVectors ∧ runImpl ∧ keep "SHA512_224" then
    for path in implCases512_224 dir do
      report "impl SHA512_224" path (runFile "impl SHA512_224" path implSha512_224Hash sample)
  if runMonte then
    if runImpl ∧ keep "SHA256" then
      let path := s!"{dir}/SHA256Monte.rsp"
      report "impl SHA256 Monte" path
        (runFileMonte "impl SHA256" path implSha256HashBytes monteSample)
    if runImpl ∧ keep "SHA224" then
      let path := s!"{dir}/SHA224Monte.rsp"
      report "impl SHA224 Monte" path
        (runFileMonte "impl SHA224" path implSha224HashBytes monteSample)
    if runImpl ∧ keep "SHA512" then
      let path := s!"{dir}/SHA512Monte.rsp"
      report "impl SHA512 Monte" path
        (runFileMonte "impl SHA512" path implSha512HashBytes monteSample)
    if runImpl ∧ keep "SHA384" then
      let path := s!"{dir}/SHA384Monte.rsp"
      report "impl SHA384 Monte" path
        (runFileMonte "impl SHA384" path implSha384HashBytes monteSample)
    if runImpl ∧ keep "SHA512_256" then
      let path := s!"{dir}/SHA512_256Monte.rsp"
      report "impl SHA512_256 Monte" path
        (runFileMonte "impl SHA512_256" path implSha512_256HashBytes monteSample)
    if runImpl ∧ keep "SHA512_224" then
      let path := s!"{dir}/SHA512_224Monte.rsp"
      report "impl SHA512_224 Monte" path
        (runFileMonte "impl SHA512_224" path implSha512_224HashBytes monteSample)
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
