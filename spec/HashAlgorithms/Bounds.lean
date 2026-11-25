--#--
namespace SHS.HashAlgorithmBounds

-- Schedule indices are bounded by the loop range or by the ring mask or modulus.
scoped macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
      first
      | exact ‹_ ∈ _›.upper
      | exact Nat.lt_of_lt_of_le ‹_ ∈ _›.upper (by decide)
      | exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) ‹_ ∈ _›.upper
      | exact Nat.mod_lt _ (by decide)
      | exact Nat.lt_succ_of_le Nat.and_le_right
      | decide)

end SHS.HashAlgorithmBounds
--#--
