/-!
# RspParser

Parser for NIST CAVP `.rsp` test vector files.

The `.rsp` format groups test cases into blocks separated by blank lines.
Each block contains `key = value` pairs. Lines starting with `#` are comments.
An optional `[L = n]` header gives the digest size in bytes.

Example:
```
#  CAVS 11.0
[L = 20]

Len = 0
Msg = 00
MD = da39a3ee5e6b4b0d3255bfef95601890afd80709

Len = 8
Msg = 24
MD = 5cb38f81bd...
```
-/

namespace RspParser

/-- A single test-vector block: an ordered sequence of `(key, value)` pairs. -/
structure Block where
  fields : Array (String × String)
  deriving Repr, Inhabited

/-- Look up a field by key. -/
def Block.find? (b : Block) (key : String) : Option String :=
  (b.fields.find? (·.1 = key)).map (·.2)

private def parseLine (line : String) : Option (String × String) :=
  match line.splitOn "=" with
  | [key, value] =>
    let key := key.trimAscii.toString
    if key.isEmpty then none else some (key, value.trimAscii.toString)
  | _ => none

/-- Parse the header and record blocks of an `.rsp` file. -/
def parse (content : String) : Except String (Option Nat × Array Block) := do
  let mut digestSize := none
  let mut blocks : Array Block := #[]
  let mut current : Array (String × String) := #[]
  let mut lineNumber := 0
  for rawLine in content.splitOn "\n" do
    lineNumber := lineNumber + 1
    let line := rawLine.trimAscii.toString
    if line.isEmpty then
      if !current.isEmpty then
        blocks := blocks.push ⟨current⟩
        current := #[]
      continue
    if line.startsWith "#" then continue
    if line.startsWith "[" then
      unless line.endsWith "]" && digestSize.isNone && blocks.isEmpty && current.isEmpty do
        throw s!"line {lineNumber}: unexpected header"
      let some ("L", value) := parseLine ((line.drop 1).dropEnd 1).toString
        | throw s!"line {lineNumber}: expected [L = n]"
      let some size := value.toNat?
        | throw s!"line {lineNumber}: invalid digest size"
      digestSize := some size
      continue
    let some (key, value) := parseLine line
      | throw s!"line {lineNumber}: expected key = value"
    if current.any (·.1 == key) then
      throw s!"line {lineNumber}: duplicate field {key}"
    current := current.push (key, value)
  if !current.isEmpty then
    blocks := blocks.push ⟨current⟩
  return (digestSize, blocks)

/-- Read and parse an `.rsp` file from disk. -/
def load (path : System.FilePath) (digestSize : Nat) : IO (Array Block) := do
  let content ← IO.FS.readFile path
  match parse content with
  | .error message => throw (IO.userError s!"{path}: {message}")
  | .ok (headerSize, blocks) =>
    unless headerSize.all (· == digestSize) do
      throw (IO.userError s!"{path}: expected L = {digestSize}")
    return blocks

/-- Hex character to its 0–15 nibble value. -/
private def hexCharToNibble? (c : Char) : Option Nat :=
  let n := c.toNat
  if      0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)        -- '0'..'9'
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)   -- 'a'..'f'
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)   -- 'A'..'F'
  else none

/-- Parse an even-length hex string into a `ByteArray`. Returns `none` on
    odd length or invalid characters. -/
def hexToBytes? (s : String) : Option ByteArray :=
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then none
  else
    (List.range (cs.size / 2)).foldlM (init := ByteArray.empty) fun acc i => do
      let hi ← hexCharToNibble? cs[2*i]!
      let lo ← hexCharToNibble? cs[2*i + 1]!
      return acc.push (UInt8.ofNat (hi * 16 + lo))

/-- Convert a `ByteArray` to a list of bits, MSB first within each byte. -/
def bytesToBits (bs : ByteArray) : List Bool :=
  bs.toList.flatMap fun b =>
    (List.range 8).reverse.map fun i => b.toNat.testBit i

end RspParser

