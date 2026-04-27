import equiv.SHA256.Main

/-! # Axiom regression gate

Pins the axiom set the public correctness theorems depend on.  If the
build fails here, a new axiom has been introduced — review the change
deliberately and update the pinned messages below. -/

/-- info: 'SHS.Equiv.SHA256.sha256_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SHS.Equiv.SHA256.Functions.Maj_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.bigSigma0_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.bigSigma1_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.smallSigma0_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.smallSigma1_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.ToU32s.beU32_eq_fromBits._native.bv_decide.ax_1_5,
 SHS.Equiv.SHA256.Digest.fromBits_4bytes_BE_256._native.bv_decide.ax_1_9✝] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.sha256_correct

/-- info: 'SHS.Equiv.SHA256.compress_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SHS.Equiv.SHA256.Functions.Maj_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.bigSigma0_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.bigSigma1_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.smallSigma0_toBitVec._native.bv_decide.ax_1_6,
 SHS.Equiv.SHA256.Functions.smallSigma1_toBitVec._native.bv_decide.ax_1_6] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.compress_correct
