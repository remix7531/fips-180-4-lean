import tests.Parser
import spec
import impl.SHA256

set_option autoImplicit true

open RspParser SHS

namespace tests.CAVP

/-! ## Hex helpers -/

private def hexChars : List Char := "0123456789abcdef".toList

/-- Lowercase hex of a `Digest n` (n / 4 hex digits, MSB first). -/
def toHex (d : Digest n) : String :=
  String.ofList ((List.range (n / 4)).reverse.map fun i =>
    hexChars[((d.toNat / (16 ^ i)) % 16)]!)

/-- Lowercase hex of a `ByteArray` (size * 2 hex digits). -/
def byteArrayToHex (bs : ByteArray) : String :=
  String.ofList (bs.toList.flatMap fun b =>
    [hexChars[b.toNat / 16]!, hexChars[b.toNat % 16]!])

/-! ## Hash dispatch

Each pipeline (spec or impl) is exposed as a `(ByteArray, Nat) → Option String`
function: takes the raw message bytes plus the bit length declared in the
vector, returns the lowercase hex digest, or `none` to skip the vector
(e.g. impl rejecting non-byte-aligned lengths). -/

/-- Spec dispatch by algorithm name on a bit-level `Message`. -/
def computeHash (alg : String) (msg : Message) : Option String :=
  match alg with
  | "SHA1"       => if h : msg.length < 2 ^ 64  then some (toHex (SHA1.sha1     msg h)) else none
  | "SHA224"     => if h : msg.length < 2 ^ 64  then some (toHex (SHA256.sha224 msg h)) else none
  | "SHA256"     => if h : msg.length < 2 ^ 64  then some (toHex (SHA256.sha256 msg h)) else none
  | "SHA384"     => if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha384 msg h)) else none
  | "SHA512"     => if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512 msg h)) else none
  | "SHA512_224" =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512_224 msg h)) else none
  | "SHA512_256" =>
      if h : msg.length < 2 ^ 128 then some (toHex (SHA512.sha512_256 msg h)) else none
  | _            => none

/-- Spec hash adapter: truncates `bytes` to `len` bits, then dispatches. -/
def specHash (alg : String) (bytes : ByteArray) (len : Nat) : Option String :=
  computeHash alg ((bytesToBits bytes).take len)

/-- Convert an impl-side `Vector UInt8 n` digest to a `ByteArray`. -/
private def vectorToByteArray {n} (d : Vector UInt8 n) : ByteArray :=
  d.toList.foldl (·.push ·) ByteArray.empty

/-- Impl SHA-256 hash adapter: byte-aligned only. -/
def implSha256Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA256.Impl.sha256 bs)))

/-- Spec MCT step: hash bytes through `computeHash`, decode the hex back to
bytes for the next round.  Returns `none` on unknown algorithm or hex
round-trip failure. -/
def specHashBytes (alg : String) (bytes : ByteArray) : Option ByteArray := do
  let hex ← computeHash alg (bytesToBits bytes)
  hexToBytes? hex

/-- Impl SHA-256 MCT step: direct ByteArray → ByteArray. -/
def implSha256HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA256.Impl.sha256 bytes))

/-! ## Short/long-message vector runner -/

/-- 1/n pseudo-random sampling: keep when `(i * 2654435761) % n = 0`.
Multiplier is Knuth's golden-ratio hash constant. -/
private def keepSample (sample : Option Nat) (i : Nat) : Bool :=
  match sample with
  | none   => true
  | some n => (i * 2654435761) % n = 0

/-- Run a short/long-message `.rsp` file against `hash`.  `sample = some n`
keeps roughly every n-th vector. -/
def runFile (label : String) (path : System.FilePath)
    (hash : ByteArray → Nat → Option String) (sample : Option Nat := none)
    : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let mut passed := 0
  let mut failed := 0
  let mut idx := 0
  for block in blocks do
    let i := idx; idx := idx + 1
    if !keepSample sample i then continue
    let some lenStr := block.find? "Len" | continue
    let some msgStr := block.find? "Msg" | continue
    let some mdStr  := block.find? "MD"  | continue
    let len := lenStr.toNat!
    let bytes ←
      if len = 0 then pure ByteArray.empty
      else match hexToBytes? msgStr with
        | some bs => pure bs
        | none =>
          failed := failed + 1
          IO.eprintln s!"FAIL {label} Len={len}: malformed hex Msg={msgStr}"
          continue
    match hash bytes len with
    | none => continue
    | some actual =>
      if actual = mdStr then passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"FAIL {label} Len={len} expected={mdStr} got={actual}"
  return (passed, failed)

/-! ## Monte-Carlo Test (CAVS §6.4) -/

/-- One outer Monte-Carlo iteration: from three copies of `seed`, run 1000
inner rounds where each round hashes `a ++ b ++ c` and rotates the
window.  Returns the final digest, or `none` if the per-round hash
returns `none` at any point. -/
def monteCarloIter (hash : ByteArray → Option ByteArray) (seed : ByteArray)
    : Option ByteArray := Id.run do
  let mut a := seed; let mut b := seed; let mut c := seed
  let mut ok := true
  for _ in [0:1000] do
    if !ok then continue
    match hash (a ++ b ++ c) with
    | none      => ok := false
    | some next => a := b; b := c; c := next
  return if ok then some c else none

/-- Run an MCT `.rsp` file: read the seed, then run one outer iteration
per `MD` block in the file (CAVS standard: 100), chaining each iteration
into the next.  `sample = some n` keeps the first `1/n` of the chains
(the chain is sequentially dependent, so sampling truncates rather than
strides).  The inner 1000-hash count per chain is fixed by CAVS and not
adjustable. -/
def runFileMonte (label : String) (path : System.FilePath)
    (hash : ByteArray → Option ByteArray) (sample : Option Nat := none)
    : IO (Nat × Nat) := do
  let blocks ← RspParser.load path
  let blocksList := blocks.toList
  let fileFail (msg : String) : IO (Nat × Nat) := do
    IO.eprintln s!"FAIL {label} Monte: {msg} ({path})"
    return (0, 1)
  let some seedBlock := blocksList.head?       | fileFail "no blocks in file"
  let some seedHex   := seedBlock.find? "Seed" | fileFail "no Seed in first block"
  let some seedBytes := hexToBytes? seedHex    | fileFail s!"malformed Seed hex {seedHex}"
  let allMd := blocksList.filter fun b => (b.find? "MD").isSome
  let mctBlocks := match sample with
    | none   => allMd
    | some n => allMd.take (allMd.length / n)
  let mut current := seedBytes
  let mut passed := 0
  let mut failed := 0
  for block in mctBlocks do
    let some mdStr := block.find? "MD" | continue
    match monteCarloIter hash current with
    | none =>
      failed := failed + 1
      IO.eprintln s!"FAIL {label} Monte: hash returned none"
    | some next =>
      current := next
      let actual := byteArrayToHex current
      if actual = mdStr then passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"FAIL {label} Monte: expected={mdStr} got={actual}"
  return (passed, failed)

/-! ## Negative tests -/

/-- Algorithm names supported by `computeHash`. -/
def supportedAlgs : List String :=
  ["SHA1", "SHA224", "SHA256", "SHA384", "SHA512", "SHA512_224", "SHA512_256"]

/-- Negative-test driver: verify the framework rejects what it should
reject (tampered digest, malformed hex, unknown algorithm), and confirm
basic invariants (determinism, distinct algorithms diverge). -/
def runNegativeTests : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  -- 1. Tampered digest per algorithm.
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
  -- 4. Determinism.
  for alg in supportedAlgs do
    let h1 := computeHash alg [false, true, false, true, true, true, false]
    let h2 := computeHash alg [false, true, false, true, true, true, false]
    if h1 = h2 then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL negative: {alg} not deterministic"
  -- 5. Distinct algorithms diverge: every unordered pair is a separate check.
  let digests : List (String × String) := supportedAlgs.filterMap fun alg =>
    (computeHash alg []).map (alg, ·)
  for (alg1, h1) in digests do
    for (alg2, h2) in digests do
      if alg1 < alg2 then
        if h1 = h2 then
          failed := failed + 1
          IO.eprintln s!"FAIL negative: {alg1} and {alg2} produced equal digests"
        else passed := passed + 1
  return (passed, failed)

/-! ## Test cases -/

/-- Spec-side short/long-message vector files, one pair per algorithm. -/
def specCases (dir : String) : List (String × String) :=
  supportedAlgs.flatMap fun alg =>
    [(alg, s!"{dir}/{alg}ShortMsg.rsp"), (alg, s!"{dir}/{alg}LongMsg.rsp")]

/-- Spec-side Monte-Carlo Test files. -/
def specMonteCases (dir : String) : List (String × String) :=
  supportedAlgs.map fun alg => (alg, s!"{dir}/{alg}Monte.rsp")

/-- Impl-side short/long-message vector files (SHA-256 only). -/
def implCases (dir : String) : List String :=
  [s!"{dir}/SHA256ShortMsg.rsp", s!"{dir}/SHA256LongMsg.rsp"]

end tests.CAVP
