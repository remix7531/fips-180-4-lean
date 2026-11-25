import tests.CAVP

open tests.CAVP

private def parseArgs (args : List String) : Except String (Option String) := do
  let switches := ["--spec", "--impl", "--no-monte", "--monte-only", "--fast"]
  let mut algFilter := none
  let mut seen : List String := []
  for arg in args do
    if seen.contains arg then throw s!"repeated argument {arg}"
    seen := arg :: seen
    if switches.contains arg then continue
    unless arg.startsWith "--alg=" do throw s!"unknown argument {arg}"
    unless algFilter.isNone do throw "expected at most one --alg argument"
    let alg := (arg.drop "--alg=".length).toString
    unless supportedAlgs.contains alg do throw s!"unknown algorithm {alg}"
    algFilter := some alg
  if args.contains "--spec" && args.contains "--impl" then
    throw "--spec and --impl are mutually exclusive"
  if args.contains "--no-monte" && args.contains "--monte-only" then
    throw "--no-monte and --monte-only are mutually exclusive"
  if args.contains "--impl" && !implCases.any (fun entry => algFilter == some entry.1) then
    let names := String.intercalate ", " (implCases.map Prod.fst)
    throw s!"--impl requires --alg with one of {names}"
  return algFilter

/-- CAVP test runner.  All workload knobs come from CLI; spec and impl
pipelines are treated symmetrically.

Flags:
  `--spec` / `--impl`     restrict to one pipeline (default: both).
  `--alg=NAME`            restrict to a single algorithm name.
  `--no-monte`            skip the Monte-Carlo Test entirely.
  `--monte-only`          skip short/long vectors and negative tests;
                          run only the Monte-Carlo Test.
  `--fast`                sample 1/10 of the short and long vectors and
                          1/100 of the Monte Carlo chains. Also retain
                          padding boundaries. Supplemental bit-oriented
                          vectors always run when their spec is selected. -/
def main (args : List String) : IO Unit := do
  let algFilter ← match parseArgs args with
    | .ok alg => pure alg
    | .error message =>
      IO.eprintln message
      IO.Process.exit 2
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
  let keep alg  := algFilter.all (· = alg)
  let dir       := "tests/vectors"
  let pass ← IO.mkRef (0 : Nat)
  let fail ← IO.mkRef (0 : Nat)
  let report (label path : String) (r : IO (Nat × Nat)) : IO Unit := do
    let (p, f) ← r
    IO.println s!"{label}: {p} passed, {f} failed  ({path})"
    pass.modify (· + p); fail.modify (· + f)
  if runVectors ∧ runSpec then
    for alg in supportedAlgs do
      if keep alg then
        let label := s!"spec {alg}"
        for suffix in ["ShortMsg", "LongMsg"] do
          let path := s!"{dir}/{alg}{suffix}.rsp"
          report label path (runFile alg label path (specHash alg) sample)
    for alg in ["SHA1", "SHA256", "SHA512"] do
      if keep alg then
        let label := s!"spec {alg} bit-oriented"
        let path := s!"{dir}/{alg}Bits.rsp"
        report label path (runFile alg label path (specHash alg) none)
    if keep "SHA1" then
      let label := "spec SHA1 alternate"
      let short := s!"{dir}/SHA1ShortMsg.rsp"
      report label short (runFile "SHA1" label short specSha1AltHash sample)
      let bits := s!"{dir}/SHA1Bits.rsp"
      report label bits (runFile "SHA1" label bits specSha1AltHash none)
  if runVectors ∧ runImpl then
    for (alg, hash, _) in implCases do
      if keep alg then
        let label := s!"impl {alg}"
        for suffix in ["ShortMsg", "LongMsg"] do
          let path := s!"{dir}/{alg}{suffix}.rsp"
          report label path (runFile alg label path hash sample (byteAlignedOnly := true))
  if runMonte then
    if runImpl then
      for (alg, _, hash) in implCases do
        if keep alg then
          let label := s!"impl {alg} Monte"
          let path := s!"{dir}/{alg}Monte.rsp"
          report label path (runFileMonte alg label path hash monteSample)
    if runSpec then
      for alg in supportedAlgs do
        if keep alg then
          let label := s!"spec {alg} Monte"
          let path := s!"{dir}/{alg}Monte.rsp"
          report label path (runFileMonte alg label path (specHashBytes alg) monteSample)
  if runVectors ∧ algFilter.isNone then
    let (p, f) ← runNegativeTests
    IO.println s!"negative tests: {p} passed, {f} failed"
    pass.modify (· + p); fail.modify (· + f)
  let p ← pass.get
  let f ← fail.get
  IO.println s!"\nTotal: {p} passed, {f} failed"
  if p + f == 0 then
    IO.eprintln "no tests selected"
    IO.Process.exit 1
  if f > 0 then IO.Process.exit 1
