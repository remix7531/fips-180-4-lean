/-!
# RspParser

Parser for NIST CAVP `.rsp` test vector files.

The `.rsp` format groups test cases into blocks separated by blank lines.
Each block contains `key = value` pairs. Lines starting with `#` are comments;
lines in `[...]` brackets are section metadata. Values are typically hex strings.

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
  | key :: rest@(_ :: _) =>
    some (key.trimAscii.toString, (String.intercalate "=" rest).trimAscii.toString)
  | _ => none

/-- Parse the contents of an `.rsp` file into a sequence of blocks.
    Lines starting with `#` (comments) or `[` (section metadata) are ignored. -/
def parse (content : String) : Array Block := Id.run do
  let mut blocks : Array Block := #[]
  let mut current : Array (String × String) := #[]
  for rawLine in content.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.isEmpty then
      if !current.isEmpty then
        blocks := blocks.push ⟨current⟩
        current := #[]
    else if line.startsWith "#" || line.startsWith "[" then
      pure ()
    else
      match parseLine line with
      | some kv => current := current.push kv
      | none    => pure ()
  if !current.isEmpty then
    blocks := blocks.push ⟨current⟩
  return blocks

/-- Read and parse an `.rsp` file from disk. -/
def load (path : System.FilePath) : IO (Array Block) := do
  let content ← IO.FS.readFile path
  return parse content

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

