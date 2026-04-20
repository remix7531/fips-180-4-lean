--#--
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Basic
import Batteries.Data.List.Basic

-- TODO: input preconditions are not yet encoded in the Lean signatures.
-- The spec text constrains, e.g., `0 ≤ n < w` for ROTR/ROTL/SHR and
-- `0 ≤ t ≤ 79` for SHA-1 `f` and `K`, but the Lean defs accept any `Nat`.
-- Out-of-range inputs panic at runtime via `arr[!]`.

namespace SHS

-- Type aliases for the names introduced above. `Word`, `HashValue`, `Block`, and
-- `Schedule` are also re-introduced as `scoped notation` inside each algorithm
-- namespace where the word size `w` is fixed.
abbrev Bit := Bool
abbrev Message := List Bit
abbrev Word (w : Nat) := BitVec w
abbrev HashValue (w : Nat) := Array (Word w)
abbrev Block (w : Nat) := Array (Word w)
abbrev Schedule (w : Nat) := Array (Word w)
abbrev Digest (n : Nat) := BitVec n

-- Operator aliases matching the FIPS notation. Precedences mirror Lean's
-- propositional operators (∧ at 35, ∨ at 30, ¬ at max with arg:40) so that the
-- parse tree is unambiguous; type-directed elaboration then picks the BitVec
-- interpretation.
scoped infixr:30 " ⊕ " => HXor.hXor
scoped infixl:35 " ∧ " => HAnd.hAnd
scoped infixl:30 " ∨ " => HOr.hOr
scoped notation:max "¬" a:40 => Complement.complement a
scoped infixl:75 " << " => HShiftLeft.hShiftLeft
scoped infixl:75 " >> " => HShiftRight.hShiftRight

-- `min { k < n | p k }` is the smallest k in [0, n) satisfying p, or 0 if none.
syntax "min " "{" ident " < " term " | " term "}" : term
macro_rules
  | `(min { $k:ident < $n:term | $p:term }) =>
    `(((List.range $n).find? (fun $k => $p)).getD 0)

/-- Encode an ASCII string as a `Message` (list of bits, MSB-first per byte). -/
def Message.fromString (s : String) : List Bool :=
  s.toList.flatMap fun c => (List.range 8).reverse.map c.toNat.testBit

/-- Pack a list of bits (MSB-first) into a `BitVec n`. -/
def Word.fromBits {n : Nat} (bits : List Bool) : BitVec n :=
  bits.foldl (fun acc b => acc <<< 1 ||| (if b then 1 else 0)) 0

/-- The left-most `n` bits of an `m`-bit vector. -/
def _root_.BitVec.leftmost (n : Nat) {m : Nat} (x : BitVec m) : BitVec n :=
  x.extractLsb' (m - n) n

/-- Numeric literals elaborate as the `H0_t` argument subtype when the
    spec's three clauses hold. Lets `H0_t 224` elide the `⟨224, …⟩` noise. -/
instance (n : Nat) [h : Decidable (0 < n ∧ n < 512 ∧ n ≠ 384)] :
    OfNat {t : Nat // 0 < t ∧ t < 512 ∧ t ≠ 384} n where
  ofNat := match h with
    | .isTrue p => ⟨n, p⟩
    | .isFalse _ => ⟨1, by decide⟩

set_option autoImplicit true

end SHS
--#--
