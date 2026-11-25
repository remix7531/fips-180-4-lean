import equiv.SHA256.Main
import equiv.SHA512.Main
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom regression gate

Each public correctness theorem must depend on exactly the three
classical axioms below.
-/

open Lean Elab Command in
run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``SHS.Equiv.SHA256.sha256_correct,
    ``SHS.Equiv.SHA256.compress_correct,
    ``SHS.Equiv.SHA256.sha224_correct,
    ``SHS.Equiv.SHA512.sha512_correct,
    ``SHS.Equiv.SHA512.compress_correct,
    ``SHS.Equiv.SHA512.sha384_correct,
    ``SHS.Equiv.SHA512.sha512_256_correct,
    ``SHS.Equiv.SHA512.sha512_224_correct
  ]
  for theoremName in declarations do
    let actual ← collectAxioms theoremName
    let added := actual.filter (fun name => !expected.contains name)
    let removed := expected.filter (fun name => !actual.contains name)
    unless added.isEmpty && removed.isEmpty do
      logError m!"Axiom set changed for {theoremName}. Added {added}. Removed {removed}."
