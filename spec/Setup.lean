--#--

-- TODO: input preconditions are not yet encoded in the Lean signatures.
-- The spec text constrains `0 ≤ n < w` for `Notation.ROTR`/`ROTL`/`SHR` and
-- `0 ≤ t ≤ 79` for `Functions.SHA1.f` and `SHA1.K`, but the Lean defs accept
-- any `Nat`. Out-of-range `n` is folded modulo `w` by `BitVec` shifts; out-of-
-- range `t` falls through to the final `else` branch.  Block/schedule indexing
-- is now bounds-checked at compile time via the `Vector` migration, so no
-- runtime panic remains for in-spec inputs.

namespace SHS

set_option autoImplicit true

-- Type aliases for the names introduced above. `Word`, `HashValue`, `Block`, and
-- `Schedule` are also re-introduced as `scoped notation` inside each algorithm
-- namespace where the word size `w` is fixed.
/-- A single bit, modelled as `Bool`. -/
abbrev Bit := Bool
/-- A message: a list of bits, MSB-first. -/
abbrev Message := List Bit
/-- An `w`-bit unsigned word. -/
abbrev Word (w : Nat) := BitVec w
/-- The hash state: an array of `w`-bit words (length depends on the algorithm). -/
abbrev HashValue (w : Nat) := Array (Word w)
/-- A message block: an array of `w`-bit words processed by one compression call. -/
abbrev Block (w : Nat) := Array (Word w)
/-- A round-key/message schedule: an array of `w`-bit words. -/
abbrev Schedule (w : Nat) := Array (Word w)
/-- A digest: an `n`-bit truncation of the final hash state. -/
abbrev Digest (n : Nat) := BitVec n

-- Operator aliases matching the FIPS notation.  The precedence numbers are
-- chosen so the resulting parse tree is unambiguous (∧ binds tighter than ∨/⊕,
-- ¬ binds tightest); type-directed elaboration then picks the BitVec
-- interpretation.  ⊕ is right-associative to match the standard convention
-- for chained XORs in the round functions; ∨ stays left-associative.
/-- FIPS-180-4 bitwise XOR (right-associative). -/
scoped infixr:30 " ⊕ " => HXor.hXor
/-- FIPS-180-4 bitwise AND. -/
scoped infixl:35 " ∧ " => HAnd.hAnd
/-- FIPS-180-4 bitwise OR. -/
scoped infixl:30 " ∨ " => HOr.hOr
/-- FIPS-180-4 bitwise NOT (one's complement). -/
scoped notation:max "¬" a:40 => Complement.complement a
/-- FIPS-180-4 left shift. -/
scoped infixl:75 " << " => HShiftLeft.hShiftLeft
/-- FIPS-180-4 right shift. -/
scoped infixl:75 " >> " => HShiftRight.hShiftRight
/-- Congruence of natural numbers modulo a natural number. -/
scoped notation:50 a " ≡ " b " [MOD " n "]" => Nat.mod a n = Nat.mod b n

/-- `min { k < n | p k }` — the smallest `k` in `[0, n)` satisfying `p`, or `0` if none. -/
syntax "min " "{" ident " < " term " | " term "}" : term
macro_rules
  | `(min { $k:ident < $n:term | $p:term }) =>
    `(((List.range $n).find? (fun $k => $p)).getD 0)

/-- Encode an ASCII string as a `Message` (list of bits).  Each character
    contributes its 8-bit code point, MSB first; the bytes themselves are
    emitted left-to-right.  Matches the FIPS 180-4 §3.1 worked example
    `"abc" → 0x61 0x62 0x63 → 01100001 01100010 01100011`. -/
def Message.fromString (s : String) : List Bool :=
  s.toList.flatMap fun c => (List.range 8).reverse.map c.toNat.testBit

/-- Pack a list of bits (MSB-first) into a `BitVec n`. -/
def Word.fromBits {n : Nat} (bits : List Bool) : BitVec n :=
  bits.foldl (fun acc b => acc <<< 1 ||| (if b then 1 else 0)) 0

/-- Split a list into consecutive chunks, including any final partial chunk.
Width zero keeps a nonempty input in one chunk. -/
def listChunks {α : Type _} (width : Nat) (items : List α) : List (List α) :=
  match width, items with
  | _, [] => []
  | 0, items => [items]
  | width + 1, items => go width items #[]
where
  go (width : Nat) (items : List α) (chunks : Array (List α)) : List (List α) :=
    match items with
    | [] => chunks.toList
    | item :: rest =>
      let parts := rest.splitAt width
      go width parts.2 (chunks.push (item :: parts.1))
  termination_by items.length
  decreasing_by
    simp only [List.splitAt_eq, List.length_drop, List.length_cons]
    omega

/-- The left-most `n` bits of an `m`-bit vector. -/
def _root_.BitVec.leftmost (n : Nat) {m : Nat} (x : BitVec m) : BitVec n :=
  x.extractLsb' (m - n) n

end SHS

/-- `do`-notation sugar for indexed assignment on `Vector`/`Array` (and any
    type with a `.set i v` method): `arr[i] := v` desugars to
    `arr := arr.set i v`. Lean's built-in indexed-assignment doElem only
    fires for a few specific types; this overrides it for any `mut` binding,
    so `Vector` works too. The implicit bound proof is discharged by
    `get_elem_tactic` on the `.set` call. -/
syntax (name := doSetMut) (priority := high)
  ident "[" term "]" " := " term : doElem
macro_rules
  | `(doElem| $x:ident[$i] := $v) => `(doElem| $x:ident := ($x).set $i $v)
--#--
