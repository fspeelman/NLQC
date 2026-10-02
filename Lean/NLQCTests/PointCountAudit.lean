import NLQCLean.Semialgebraic.FinitePointCount
import NLQCLean.Geometry.C1PieceFamilyVolume
import NLQCLean.Geometry.PolynomialStrictDeriv
import NLQCLean.Geometry.DirectVolume.Assembly

/-! Axiom audit of the hypothesis-free geometry steps: the elementary point count
(track C), the C¹-piece volume engine (D1) and polynomial strict derivatives (B1). -/

/-- info: 'NLQCLean.PurePowerZeros.commonZeros_finite_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PurePowerZeros.commonZeros_finite_ncard_le

/-- info: 'NLQCLean.PurePowerZeros.card_isolatedZeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PurePowerZeros.card_isolatedZeros_le

/-- info: 'NLQCLean.HasSemialgebraicFormat.ncard_le_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HasSemialgebraicFormat.ncard_le_of_finite

/-- info: 'NLQCLean.volume_iUnion_C1Pieces_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.volume_iUnion_C1Pieces_le

/-- info: 'NLQCLean.PolynomialCalculus.hasStrictFDerivAt_eval_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PolynomialCalculus.hasStrictFDerivAt_eval_pi

/-- info: 'NLQCLean.PolynomialCalculus.IsLocalExtrOn.exists_lagrange_of_linearIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PolynomialCalculus.IsLocalExtrOn.exists_lagrange_of_linearIndependent

/-- info: 'NLQCLean.DirectVolume.polynomialImageVolumeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.DirectVolume.polynomialImageVolumeBound

/-- info: 'NLQCLean.DirectVolume.polynomialImageVolumeBoundWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.DirectVolume.polynomialImageVolumeBoundWith
