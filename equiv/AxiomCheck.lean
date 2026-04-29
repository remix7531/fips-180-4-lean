import equiv.SHA256.Main

/-! # Axiom regression gate

Pins the axiom set the public correctness theorems depend on.  If the
build fails here, a new axiom has been introduced — review the change
deliberately and update the pinned messages below. -/

/-- info: 'SHS.Equiv.SHA256.sha256_correct' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.sha256_correct

/-- info: 'SHS.Equiv.SHA256.compress_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.compress_correct
