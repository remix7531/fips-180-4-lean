import tests.Parser
import spec
import impl.SHA256
import impl.SHA512

open RspParser SHS

namespace tests.CAVP

/-! ## Hex helpers -/

private def hexChars : List Char := "0123456789abcdef".toList

/-- Lowercase hex of a `Digest n` (n / 4 hex digits, MSB first). -/
def toHex {n : Nat} (d : Digest n) : String :=
  String.ofList ((List.range (n / 4)).reverse.map fun i =>
    hexChars[((d.toNat / (16 ^ i)) % 16)]!)

/-- Lowercase hex of a `ByteArray` (size * 2 hex digits). -/
def byteArrayToHex (bs : ByteArray) : String :=
  String.ofList (bs.toList.flatMap fun b =>
    [hexChars[b.toNat / 16]!, hexChars[b.toNat % 16]!])

/-! ## Hash dispatch

Each pipeline (spec or impl) is exposed as a `(ByteArray, Nat) → Option String`
function: takes the raw message bytes plus the bit length declared in the
vector, and returns the lowercase hex digest if the pipeline supports that
input. -/

private def digestSizes : List (String × Nat) :=
  [("SHA1", 20), ("SHA224", 28), ("SHA256", 32), ("SHA384", 48), ("SHA512", 64),
   ("SHA512_224", 28), ("SHA512_256", 32)]

/-- Algorithm names supported by `computeHash`. -/
def supportedAlgs : List String :=
  digestSizes.map Prod.fst

private def digestSize (alg : String) : IO Nat := do
  let some (_, size) := digestSizes.find? (·.1 == alg)
    | throw (IO.userError s!"unknown algorithm {alg}")
  return size

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

/-- Spec adapter for the alternate SHA-1 circular schedule. -/
def specSha1AltHash (bytes : ByteArray) (len : Nat) : Option String :=
  let msg := (bytesToBits bytes).take len
  if h : msg.length < 2 ^ 64 then some (toHex (SHA1.sha1_alt msg h)) else none

/-- Convert an impl-side `Vector UInt8 n` digest to a `ByteArray`. -/
private def vectorToByteArray {n} (d : Vector UInt8 n) : ByteArray :=
  d.toList.foldl (·.push ·) ByteArray.empty

/-- Impl SHA-256 hash adapter: byte-aligned only. -/
def implSha256Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA256.Impl.sha256 bs)))

/-- Impl SHA-224 hash adapter: byte-aligned only.  SHA-224 shares the
SHA-256 compression machinery, so this validates `Impl.sha224` against
the same CAVP harness used for SHA-256. -/
def implSha224Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA256.Impl.sha224 bs)))

/-- Spec MCT step: hash bytes through `computeHash`, decode the hex back to
bytes for the next round.  Returns `none` on unknown algorithm or hex
round-trip failure. -/
def specHashBytes (alg : String) (bytes : ByteArray) : Option ByteArray := do
  let hex ← computeHash alg (bytesToBits bytes)
  hexToBytes? hex

/-- Impl SHA-256 MCT step: direct ByteArray → ByteArray. -/
def implSha256HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA256.Impl.sha256 bytes))

/-- Impl SHA-224 MCT step: direct ByteArray → ByteArray. -/
def implSha224HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA256.Impl.sha224 bytes))

/-- Impl SHA-512 hash adapter: byte-aligned only. -/
def implSha512Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA512.Impl.sha512 bs)))

/-- Impl SHA-512 MCT step: direct ByteArray → ByteArray. -/
def implSha512HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA512.Impl.sha512 bytes))

/-- Impl SHA-384 hash adapter. -/
def implSha384Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA512.Impl.sha384 bs)))

def implSha384HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA512.Impl.sha384 bytes))

/-- Impl SHA-512/256 hash adapter. -/
def implSha512_256Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA512.Impl.sha512_256 bs)))

def implSha512_256HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA512.Impl.sha512_256 bytes))

/-- Impl SHA-512/224 hash adapter. -/
def implSha512_224Hash (bytes : ByteArray) (len : Nat) : Option String :=
  if len % 8 ≠ 0 then none
  else
    let bs := bytes.extract 0 (len / 8)
    some (byteArrayToHex (vectorToByteArray (SHS.SHA512.Impl.sha512_224 bs)))

def implSha512_224HashBytes (bytes : ByteArray) : Option ByteArray :=
  some (vectorToByteArray (SHS.SHA512.Impl.sha512_224 bytes))

/-! ## Short/long-message vector runner -/

private def requireField (block : Block) (key : String) : Except String String :=
  match block.find? key with
  | some value => .ok value
  | none => .error s!"missing {key}"

private def parseDigest (size : Nat) (field value : String) : Except String ByteArray := do
  let some bytes := hexToBytes? value | throw s!"invalid {field} hex"
  unless bytes.size == size do
    throw s!"expected {field} to contain {size} bytes, got {bytes.size}"
  return bytes

private def parseVector (size : Nat) (block : Block) :
    Except String (Nat × ByteArray × String) := do
  let lenStr ← requireField block "Len"
  let msgStr ← requireField block "Msg"
  let mdStr ← requireField block "MD"
  unless block.fields.size == 3 do throw "unexpected vector field"
  let some len := lenStr.toNat? | throw s!"invalid Len: {lenStr}"
  let some bytes := hexToBytes? msgStr | throw "invalid Msg hex"
  -- CAVP encodes the empty message with the placeholder 00.
  let bytes := if len == 0 && msgStr == "00" then ByteArray.empty else bytes
  unless bytes.size == (len + 7) / 8 do
    throw s!"Len={len} requires {(len + 7) / 8} message bytes, got {bytes.size}"
  let expected ← parseDigest size "MD" mdStr
  return (len, bytes, byteArrayToHex expected)

/-- Sample roughly every n-th vector. -/
private def keepSample (sample : Option Nat) (i : Nat) : Bool :=
  match sample with
  | none   => true
  | some n => (i * 2654435761) % n = 0

private def isPaddingBoundary (alg : String) (len : Nat) : Bool :=
  if alg == "SHA384" || alg.startsWith "SHA512" then len == 888 || len == 896
  else len == 440 || len == 448

/-- Run a short or long message file. Sampling always keeps vectors on both sides of
the algorithm's byte-aligned padding transition. -/
def runFile (alg label : String) (path : System.FilePath)
    (hash : ByteArray → Nat → Option String) (sample : Option Nat)
    (byteAlignedOnly : Bool := false)
    : IO (Nat × Nat) := do
  let size ← digestSize alg
  let blocks ← RspParser.load path size
  let mut passed := 0
  let mut failed := 0
  for i in [:blocks.size] do
    let (len, bytes, expected) ← match parseVector size blocks[i]! with
      | .ok vector => pure vector
      | .error message => throw (IO.userError s!"{path}: vector {i + 1}: {message}")
    if byteAlignedOnly && len % 8 != 0 then continue
    if !keepSample sample i && !isPaddingBoundary alg len then continue
    match hash bytes len with
    | none => throw (IO.userError s!"{path}: {label} could not hash vector {i + 1}")
    | some actual =>
      if actual = expected then passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"FAIL {label} Len={len} expected={expected} got={actual}"
  if passed + failed == 0 then
    throw (IO.userError s!"{path}: no vectors selected")
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

private def parseMonteSeed (size : Nat) (block : Block) : Except String ByteArray := do
  let seed ← requireField block "Seed"
  unless block.fields.size == 1 do throw "unexpected seed field"
  parseDigest size "Seed" seed

private def parseMonteDigest (size i : Nat) (block : Block) : Except String String := do
  let count ← requireField block "COUNT"
  let expected ← requireField block "MD"
  unless block.fields.size == 2 do throw "unexpected Monte Carlo field"
  unless count.toNat? == some i do throw s!"expected COUNT = {i}, got {count}"
  return byteArrayToHex (← parseDigest size "MD" expected)

/-- Run the Monte Carlo chains in order, starting from the seed and using
each result as the seed of the next chain. Sampling keeps the first
`1/n` of the chains because each depends on the previous result. -/
def runFileMonte (alg label : String) (path : System.FilePath)
    (hash : ByteArray → Option ByteArray) (sample : Option Nat)
    : IO (Nat × Nat) := do
  let size ← digestSize alg
  let blocks ← RspParser.load path size
  let some seedBlock := blocks[0]? | throw (IO.userError s!"{path}: missing seed block")
  let mut current ← match parseMonteSeed size seedBlock with
    | .ok seed => pure seed
    | .error message => throw (IO.userError s!"{path}: seed block: {message}")
  let count := blocks.size - 1
  let mut digests : Array String := #[]
  for i in [:count] do
    match parseMonteDigest size i blocks[i + 1]! with
    | .ok expected => digests := digests.push expected
    | .error message => throw (IO.userError s!"{path}: Monte Carlo record {i}: {message}")
  let selected := count / sample.getD 1
  if selected == 0 then
    throw (IO.userError s!"{path}: no Monte Carlo chains selected")
  let mut passed := 0
  let mut failed := 0
  for i in [:selected] do
    let expected := digests[i]!
    let some next := monteCarloIter hash current
      | throw (IO.userError s!"{path}: {label} could not hash Monte Carlo record {i}")
    current := next
    let actual := byteArrayToHex current
    if actual == expected then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL {label} COUNT={i} expected={expected} got={actual}"
  return (passed, failed)

/-! ## Negative tests -/

/-- Negative-test driver: verify the framework rejects what it should
reject (malformed hex, unknown algorithm), and confirm
basic invariants (determinism, distinct algorithms diverge). -/
def runNegativeTests : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  -- Empty hex.
  match hexToBytes? "" with
  | some bs =>
    if bs.size = 0 then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL negative: empty hex parsed to non-empty ({bs.size} bytes)"
  | none => passed := passed + 1
  -- Garbage hex.
  match hexToBytes? "not_hex_at_all_zzz!" with
  | none => passed := passed + 1
  | some _ =>
    failed := failed + 1
    IO.eprintln "FAIL negative: garbage hex string was accepted"
  -- Unknown algorithm name.
  match computeHash "BOGUS_ALG" [] with
  | none => passed := passed + 1
  | some _ =>
    failed := failed + 1
    IO.eprintln "FAIL negative: unknown algorithm produced a digest"
  -- Determinism.
  for alg in supportedAlgs do
    let h1 := computeHash alg [false, true, false, true, true, true, false]
    let h2 := computeHash alg [false, true, false, true, true, true, false]
    if h1 = h2 then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL negative: {alg} not deterministic"
  -- Each unordered pair of algorithms is a separate check.
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

/-- Algorithms with executable hash adapters for message vectors and Monte Carlo tests. -/
def implCases : List
    (String × (ByteArray → Nat → Option String) × (ByteArray → Option ByteArray)) :=
  [("SHA256", implSha256Hash, implSha256HashBytes),
   ("SHA224", implSha224Hash, implSha224HashBytes),
   ("SHA512", implSha512Hash, implSha512HashBytes),
   ("SHA384", implSha384Hash, implSha384HashBytes),
   ("SHA512_256", implSha512_256Hash, implSha512_256HashBytes),
   ("SHA512_224", implSha512_224Hash, implSha512_224HashBytes)]

end tests.CAVP
