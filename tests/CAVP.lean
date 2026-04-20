import tests.Parser
import spec

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

end tests.CAVP

def main (args : List String) : IO Unit := do
  -- `--fast` keeps roughly every 10th vector for quick iteration.
  let sample : Option Nat := if args.contains "--fast" then some 10 else none
  let dir := "tests/vectors"
  let cases : List (String × String) := [
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
  let mut totalPass := 0
  let mut totalFail := 0
  for (alg, path) in cases do
    let (p, f) ← tests.CAVP.runFile alg path sample
    IO.println s!"{alg}: {p} passed, {f} failed  ({path})"
    totalPass := totalPass + p
    totalFail := totalFail + f
  IO.println s!"\nTotal: {totalPass} passed, {totalFail} failed"
  if totalFail > 0 then IO.Process.exit 1
