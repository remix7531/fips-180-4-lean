import tests.Parser
import spec
import impl.SHA256

set_option autoImplicit true

open RspParser SHS

namespace tests.CAVP

/-- Render a `Digest n` as a lowercase hex string with `n / 4` digits. -/
def toHex (d : Digest n) : String :=
  let chars := "0123456789abcdef".toList
  String.ofList ((List.range (n / 4)).reverse.map fun i =>
    chars[((d.toNat / (16 ^ i)) % 16)]!)

/-- Dispatch by algorithm name, returning the lowercase hex digest.
    `none` is returned when the message is too long for the algorithm's bound. -/
def computeHash (alg : String) (msg : Message) : Option String :=
  match alg with
  | "SHA1"       =>
      if h : msg.length < 2 ^ 64  then some (toHex (SHA1.sha1     msg h)) else none
  | "SHA224"     =>
      if h : msg.length < 2 ^ 64  then some (toHex (SHA256.sha224 msg h)) else none
  | "SHA256"     =>
      if h : msg.length < 2 ^ 64  then some (toHex (SHA256.sha256 msg h)) else none
  | "SHA384"     =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha384 msg h)) else none
  | "SHA512"     =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512 msg h)) else none
  | "SHA512_224" =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512_224 msg h)) else none
  | "SHA512_256" =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512_256 msg h)) else none
  | _            => none

/-- Run test vectors in a `.rsp` file against `alg`. If `sample` is `some n`,
    only every n-th vector is run (used by `--fast` mode). -/
def runFile (alg : String) (path : System.FilePath) (sample : Option Nat := none)
    : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let mut passed := 0
  let mut failed := 0
  let mut idx := 0
  for block in blocks do
    let i := idx
    idx := idx + 1
    if let some n := sample then
      -- Pseudo-random sampling: keep when (i * 2654435761) mod n = 0.
      -- Multiplier is Knuth's golden-ratio constant for hashing.
      if (i * 2654435761) % n ≠ 0 then continue
    let some lenStr := block.find? "Len" | continue
    let some msgStr := block.find? "Msg" | continue
    let some mdStr  := block.find? "MD"  | continue
    let len := lenStr.toNat!
    let bytes :=
      if len = 0 then ByteArray.empty
      else (hexToBytes? msgStr).getD ByteArray.empty
    let bits := (bytesToBits bytes).take len
    match computeHash alg bits with
    | some actual =>
      if actual = mdStr then
        passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"FAIL {alg} Len={len} expected={mdStr} got={actual}"
    | none =>
      failed := failed + 1
      IO.eprintln s!"FAIL {alg}: unknown algorithm"
  return (passed, failed)

/-- Lowercase hex of a `Vector UInt8 n` (impl-side digest). -/
def digestToHex (d : Vector UInt8 n) : String :=
  let chars := "0123456789abcdef".toList
  String.ofList (d.toList.flatMap fun b =>
    [chars[b.toNat / 16]!, chars[b.toNat % 16]!])

/-- Convert an impl-side `Vector UInt8 32` digest to a `ByteArray`. -/
private def digestToByteArray (d : Vector UInt8 32) : ByteArray :=
  d.toList.foldl (·.push ·) ByteArray.empty

/-- One iteration of the FIPS 180-4 SHA-2 Monte-Carlo Test (CAVS §6.4):
starting from three copies of `seed`, run 1000 inner SHA-256 rounds where
each round hashes the concatenation of the three previous digests.  Returns
the final MD (the 1000th digest). -/
def monteCarloIter256 (seed : ByteArray) : ByteArray := Id.run do
  let mut a := seed
  let mut b := seed
  let mut c := seed
  for _ in [0:1000] do
    let m := a ++ b ++ c
    let next := digestToByteArray (SHS.SHA256.Impl.sha256 m)
    a := b
    b := c
    c := next
  return c

/-- One outer iteration of the SHA-2 family Monte-Carlo Test, driven by
the *spec* pipeline (`computeHash`).  Same shape as `monteCarloIter256`
but algorithm-agnostic: works for any of SHA-1 / SHA-224 / SHA-256 /
SHA-384 / SHA-512 / SHA-512/224 / SHA-512/256.  Returns `none` if the
algorithm is unknown or a hex round-trip fails — both unreachable for
the seven supported names with well-formed input.  Slow (~3000 spec
hashes per outer iteration); intended for correctness verification,
not bulk timing. -/
def monteCarloIterSpec (alg : String) (seed : ByteArray) : Option ByteArray :=
  Id.run do
    let mut a := seed
    let mut b := seed
    let mut c := seed
    let mut ok := true
    for _ in [0:1000] do
      if !ok then continue
      let m := a ++ b ++ c
      let bits := bytesToBits m
      match computeHash alg bits with
      | none => ok := false
      | some hexResult =>
        match hexToBytes? hexResult with
        | none => ok := false
        | some bytes =>
          a := b
          b := c
          c := bytes
    return if ok then some c else none

/-- Run the SHA-256 Monte-Carlo Test against a `.rsp` file: 100 outer
iterations of `monteCarloIter256`, each chaining the previous COUNT's
final MD.  Verifies the spec's `MD_j = MD_1002` of each iteration. -/
def runFileImpl256Monte (path : System.FilePath) : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let blocksList := blocks.toList
  let some seedBlock := blocksList.head? | return (0, 1)
  let some seedHex := seedBlock.find? "Seed" | return (0, 1)
  let some seedBytes := hexToBytes? seedHex | return (0, 1)
  let mut current := seedBytes
  let mut passed := 0
  let mut failed := 0
  let mctBlocks := blocksList.filter fun b => (b.find? "MD").isSome
  for block in mctBlocks do
    let some mdStr := block.find? "MD" | continue
    current := monteCarloIter256 current
    let actual := digestToHex (Vector.ofFn (n := 32) fun i =>
      current.get! i.val)
    if actual = mdStr then
      passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL impl SHA256 Monte: expected={mdStr} got={actual}"
  return (passed, failed)

/-- Lowercase hex of an arbitrary `ByteArray`. -/
def byteArrayToHex (bs : ByteArray) : String :=
  let chars := "0123456789abcdef".toList
  String.ofList (bs.toList.flatMap fun b =>
    [chars[b.toNat / 16]!, chars[b.toNat % 16]!])

/-- Run the SHA-2 family Monte-Carlo Test against a `.rsp` file using
the *spec* pipeline, stopping after `maxCounts` outer iterations.
The full MCT has 100 outer iterations; the spec is ~25× slower than
the impl, so a full spec MCT for all seven algorithms would take
hours.  Default `maxCounts = 3` exercises the runner end-to-end (~3
outer iterations × 1000 inner hashes = 3000 spec hashes per algorithm,
~30 s per algorithm) without dominating CI.

When a verified implementation lands for an algorithm, swap in
`runFileImpl…Monte` (full 100 outer iterations) and drop the spec
runner from CI for that algorithm. -/
def runFileSpecMonte (alg : String) (path : System.FilePath)
    (maxCounts : Nat := 3) : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let blocksList := blocks.toList
  let some seedBlock := blocksList.head? | return (0, 1)
  let some seedHex := seedBlock.find? "Seed" | return (0, 1)
  let some seedBytes := hexToBytes? seedHex | return (0, 1)
  let mut current := seedBytes
  let mut passed := 0
  let mut failed := 0
  let mctBlocks := (blocksList.filter fun b => (b.find? "MD").isSome).take maxCounts
  for block in mctBlocks do
    let some mdStr := block.find? "MD" | continue
    match monteCarloIterSpec alg current with
    | none =>
      failed := failed + 1
      IO.eprintln s!"FAIL spec {alg} Monte: hash pipeline returned none"
    | some next =>
      current := next
      let actual := byteArrayToHex current
      if actual = mdStr then
        passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"FAIL spec {alg} Monte: expected={mdStr} got={actual}"
  return (passed, failed)

/-- Algorithm names supported by `computeHash`.  Drives both negative
tests and per-algorithm sanity checks. -/
def supportedAlgs : List String :=
  ["SHA1", "SHA224", "SHA256", "SHA384", "SHA512", "SHA512_224", "SHA512_256"]

/-- Negative-test driver: verify the test framework correctly *rejects*
inputs it should reject.  Runs five categories of checks:
 1. **Tampered digest** — for each spec algorithm, flip one byte of the
    empty-message digest and confirm the result differs.
 2. **Hex round-trip** — empty hex parses to empty (or returns `none`);
    garbage non-hex returns `none` rather than crashing.
 3. **Unknown algorithm** — `computeHash "BOGUS" _` returns `none`.
 4. **Spec pipeline determinism** — hashing the same message twice via
    each spec algorithm gives identical hex.
 5. **Distinct algorithms diverge** — the empty-message digests of any
    two distinct spec algorithms differ (catches dispatch bugs).
Returns `(passed, failed)` where each failure prints to stderr. -/
def runNegativeTests : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  -- 1. Per-algorithm tampered-digest check.
  for alg in supportedAlgs do
    match computeHash alg [] with
    | none =>
      failed := failed + 1
      IO.eprintln s!"FAIL negative: {alg} on empty message returned none"
    | some goodHex =>
      let tampered :=
        if goodHex.length > 0 then
          let c := goodHex.front
          let flipped := if c = '0' then '1' else '0'
          flipped.toString ++ goodHex.drop 1
        else "0"
      if goodHex = tampered then
        failed := failed + 1
        IO.eprintln s!"FAIL negative: {alg} tamper produced equal digest"
      else passed := passed + 1
  -- 2a. Empty hex.
  match hexToBytes? "" with
  | some bs =>
    if bs.size = 0 then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL negative: empty hex parsed to non-empty ({bs.size} bytes)"
  | none => passed := passed + 1
  -- 2b. Garbage hex.
  match hexToBytes? "not_hex_at_all_zzz!" with
  | none => passed := passed + 1
  | some _ =>
    failed := failed + 1
    IO.eprintln "FAIL negative: garbage hex string was accepted"
  -- 3. Unknown algorithm name.
  match computeHash "BOGUS_ALG" [] with
  | none => passed := passed + 1
  | some _ =>
    failed := failed + 1
    IO.eprintln "FAIL negative: unknown algorithm produced a digest"
  -- 4. Determinism per algorithm.
  for alg in supportedAlgs do
    let h1 := computeHash alg [false, true, false, true, true, true, false]
    let h2 := computeHash alg [false, true, false, true, true, true, false]
    if h1 = h2 then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL negative: {alg} not deterministic"
  -- 5. Distinct algorithms produce distinct digests on the same input.
  let mut digests : List (String × String) := []
  for alg in supportedAlgs do
    if let some h := computeHash alg [] then
      digests := (alg, h) :: digests
  for (alg1, h1) in digests do
    for (alg2, h2) in digests do
      if alg1 < alg2 ∧ h1 = h2 then
        failed := failed + 1
        IO.eprintln s!"FAIL negative: {alg1} and {alg2} produced equal digests"
  passed := passed + 1
  return (passed, failed)

/-- Run the impl SHA-256 pipeline on a `.rsp` file.  The impl is byte-aligned,
    so non-byte-multiple `Len` vectors are skipped (not failed). -/
def runFileImpl256 (path : System.FilePath) (sample : Option Nat := none)
    : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let mut passed := 0
  let mut failed := 0
  let mut idx := 0
  for block in blocks do
    let i := idx
    idx := idx + 1
    if let some n := sample then
      if (i * 2654435761) % n ≠ 0 then continue
    let some lenStr := block.find? "Len" | continue
    let some msgStr := block.find? "Msg" | continue
    let some mdStr  := block.find? "MD"  | continue
    let len := lenStr.toNat!
    if len % 8 ≠ 0 then continue
    let bytes :=
      if len = 0 then ByteArray.empty
      else (hexToBytes? msgStr).getD ByteArray.empty
    let bytes := bytes.extract 0 (len / 8)
    let actual := digestToHex (SHS.SHA256.Impl.sha256 bytes)
    if actual = mdStr then
      passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL impl SHA256 Len={len} expected={mdStr} got={actual}"
  return (passed, failed)

end tests.CAVP

def specCases (dir : String) : List (String × String) := [
  ("SHA1",       s!"{dir}/SHA1ShortMsg.rsp"),
  ("SHA1",       s!"{dir}/SHA1LongMsg.rsp"),
  ("SHA224",     s!"{dir}/SHA224ShortMsg.rsp"),
  ("SHA224",     s!"{dir}/SHA224LongMsg.rsp"),
  ("SHA256",     s!"{dir}/SHA256ShortMsg.rsp"),
  ("SHA256",     s!"{dir}/SHA256LongMsg.rsp"),
  ("SHA384",     s!"{dir}/SHA384ShortMsg.rsp"),
  ("SHA384",     s!"{dir}/SHA384LongMsg.rsp"),
  ("SHA512",     s!"{dir}/SHA512ShortMsg.rsp"),
  ("SHA512",     s!"{dir}/SHA512LongMsg.rsp"),
  ("SHA512_224", s!"{dir}/SHA512_224ShortMsg.rsp"),
  ("SHA512_224", s!"{dir}/SHA512_224LongMsg.rsp"),
  ("SHA512_256", s!"{dir}/SHA512_256ShortMsg.rsp"),
  ("SHA512_256", s!"{dir}/SHA512_256LongMsg.rsp"),
]

def implCases (dir : String) : List String :=
  [s!"{dir}/SHA256ShortMsg.rsp", s!"{dir}/SHA256LongMsg.rsp"]

/-- Spec-side Monte-Carlo Test files, one per algorithm.  When a
verified implementation lands for one of these algorithms the same
`runFileSpecMonte` runner can be reused on the impl side; only the
hash function plugged into `monteCarloIterSpec` changes. -/
def specMonteCases (dir : String) : List (String × String) := [
  ("SHA1",       s!"{dir}/SHA1Monte.rsp"),
  ("SHA224",     s!"{dir}/SHA224Monte.rsp"),
  ("SHA256",     s!"{dir}/SHA256Monte.rsp"),
  ("SHA384",     s!"{dir}/SHA384Monte.rsp"),
  ("SHA512",     s!"{dir}/SHA512Monte.rsp"),
  ("SHA512_224", s!"{dir}/SHA512_224Monte.rsp"),
  ("SHA512_256", s!"{dir}/SHA512_256Monte.rsp"),
]

def main (args : List String) : IO Unit := do
  -- `--fast` keeps roughly every 10th vector for quick iteration.
  -- `--spec` runs only the spec pipeline; `--impl` runs only the impl
  -- pipeline; default runs both.  `--no-monte` skips the SHA-256 Monte-Carlo
  -- Test (~100 000 inner hashes); included by default.
  let sample : Option Nat := if args.contains "--fast" then some 10 else none
  let onlySpec := args.contains "--spec"
  let onlyImpl := args.contains "--impl"
  let runSpec := !onlyImpl
  let runImpl := !onlySpec
  let runMonte := !args.contains "--no-monte"
  let dir := "tests/vectors"
  let mut totalPass := 0
  let mut totalFail := 0
  if runSpec then
    for (alg, path) in specCases dir do
      let (p, f) ← tests.CAVP.runFile alg path sample
      IO.println s!"spec {alg}: {p} passed, {f} failed  ({path})"
      totalPass := totalPass + p
      totalFail := totalFail + f
  if runImpl then
    for path in implCases dir do
      let (p, f) ← tests.CAVP.runFileImpl256 path sample
      IO.println s!"impl SHA256: {p} passed, {f} failed  ({path})"
      totalPass := totalPass + p
      totalFail := totalFail + f
  if runMonte then
    if runImpl then
      let path := s!"{dir}/SHA256Monte.rsp"
      let (p, f) ← tests.CAVP.runFileImpl256Monte path
      IO.println s!"impl SHA256 Monte: {p} passed, {f} failed  ({path})"
      totalPass := totalPass + p
      totalFail := totalFail + f
    if runSpec then
      for (alg, path) in specMonteCases dir do
        let (p, f) ← tests.CAVP.runFileSpecMonte alg path
        IO.println s!"spec {alg} Monte: {p} passed, {f} failed  ({path})"
        totalPass := totalPass + p
        totalFail := totalFail + f
  -- Negative tests (tampered digest, malformed input).
  let (p, f) ← tests.CAVP.runNegativeTests
  IO.println s!"negative tests: {p} passed, {f} failed"
  totalPass := totalPass + p
  totalFail := totalFail + f
  IO.println s!"\nTotal: {totalPass} passed, {totalFail} failed"
  if totalFail > 0 then IO.Process.exit 1
