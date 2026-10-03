import NLQCLean.Semialgebraic.FinitePointCount
import NLQCLean.Geometry.C1PieceFamilyVolume
import NLQCLean.Geometry.PolynomialStrictDeriv
import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.ImageVolume.PolynomialImageVolume
import NLQCLean.Bounds.FixedBudgetStability
import NLQCLean.Bounds.FixedBudgetStabilityPVM
import NLQCLean.Bounds.ExplicitControlledPhaseTranscript
import NLQCLean.Bounds.ExplicitControlledPhaseSharedRandom
import NLQCLean.Geometry.PolynomialTube
import NLQCLean.Geometry.UnitaryFrobeniusVolume
import NLQCLean.Approx.PVMWitnessCutoff
import NLQCLean.Exact.OrbitInvariantAlgebraicity
import NLQCLean.Bounds.ExplicitControlledPhaseResultant
import NLQCLean.Bounds.ExplicitControlledPhaseGelfond
import NLQCLean.Bounds.ExplicitControlledPhaseAngle

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

/-- info: 'NLQCLean.polynomialImageVolumeBoundWith_imageVolumeConstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.polynomialImageVolumeBoundWith_imageVolumeConstant

/-- info: 'NLQCLean.polynomialImageVolumeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.polynomialImageVolumeBound

/-- info: 'NLQCLean.DirectVolume.exists_polynomialImageVolume_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.DirectVolume.exists_polynomialImageVolume_constant

/-- info: 'NLQCLean.DirectVolume.exists_polynomial_tube_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.DirectVolume.exists_polynomial_tube_constant

/-- info: 'NLQCLean.volume_unitaryFrobeniusTube_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.volume_unitaryFrobeniusTube_ge

/-- info: 'NLQCLean.unitaryFrobeniusVolume_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryFrobeniusVolume_ge

/-- info: 'NLQCLean.PVMReverseBlocks.witnessFormat_nearBell_rank_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PVMReverseBlocks.witnessFormat_nearBell_rank_error

/-- info: 'NLQCLean.PVMReverseBlocks.IsValid.local_velocity_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PVMReverseBlocks.IsValid.local_velocity_decomposition

/-- info: 'NLQCLean.purity_isRationalOrbitInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_isRationalOrbitInvariant

/-- info: 'NLQCLean.Elimination.elim_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Elimination.elim_flat

/-- info: 'NLQCLean.Elimination.lagrangeSystem_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Elimination.lagrangeSystem_generic

/-- info: 'NLQCLean.exists_controlledPhase_one_resultant_eliminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_controlledPhase_one_resultant_eliminant

/-- info: 'NLQCLean.Gelfond.norm_eval_exp_I_ge_of_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Gelfond.norm_eval_exp_I_ge_of_irreducible

/-- info: 'NLQCLean.Gelfond.norm_eval_exp_I_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Gelfond.norm_eval_exp_I_ge

/-- info: 'NLQCLean.Gelfond.eq_zero_of_norm_small_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Gelfond.eq_zero_of_norm_small_angle

/-- info: 'NLQCLean.Gelfond.norm_eval_exp_angle_ge_of_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Gelfond.norm_eval_exp_angle_ge_of_irreducible

/-- info: 'NLQCLean.Gelfond.norm_eval_exp_angle_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Gelfond.norm_eval_exp_angle_ge

/-- info: 'NLQCLean.polynomialTypeTranscendenceMeasureExpAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.polynomialTypeTranscendenceMeasureExpAngle

/-- info: 'NLQCLean.exists_explicit_controlledPhaseLeastDeficit_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhaseLeastDeficit_lower_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_protocol_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_protocol_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_iterated_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_iterated_log_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_quantum_iterated_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_quantum_iterated_log_bound

/-- info: 'NLQCLean.exists_controlledPhase_one_eliminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_controlledPhase_one_eliminant

/-- info: 'NLQCLean.controlledPhase_one_triple_exp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_one_triple_exp_bound

/-- info: 'NLQCLean.controlledPhase_one_protocol_triple_exp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_one_protocol_triple_exp_bound

/-- info: 'NLQCLean.controlledPhase_one_triple_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_one_triple_log_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_lower_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_protocol_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_protocol_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_iterated_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_iterated_log_bound

/-- info: 'NLQCLean.exists_pow_le_of_saOn_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_pow_le_of_saOn_graph

/-- info: 'NLQCLean.lojasiewicz_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.lojasiewicz_inequality

/-- info: 'NLQCLean.exists_stability_of_familyMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_stability_of_familyMax

/-- info: 'NLQCLean.FixedBudget.exists_fixedBudget_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.FixedBudget.exists_fixedBudget_stability

/-- info: 'NLQCLean.FixedBudget.exists_exactSet_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.FixedBudget.exists_exactSet_eq_iUnion_orbits

/-- info: 'NLQCLean.PhysicalPolynomial.pvmScoreNumeratorPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.pvmScoreNumeratorPolynomial_evaluate

/-- info: 'NLQCLean.FixedBudget.exists_fixedBudget_stability_pvm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.FixedBudget.exists_fixedBudget_stability_pvm

/-- info: 'NLQCLean.FixedBudget.exists_pvmExactSet_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.FixedBudget.exists_pvmExactSet_eq_iUnion_orbits

/-- info: 'NLQCLean.exists_isometry_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_isometry_extension

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.purify_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.purify_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.exists_transcript_representative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_transcript_representative

/-- info: 'NLQCLean.TranscriptPolynomial.card_tCoordIndex_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.TranscriptPolynomial.card_tCoordIndex_le

/-- info: 'NLQCLean.Deformation.exists_eliminant_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Deformation.exists_eliminant_of_family

/-- info: 'NLQCLean.exists_controlledPhase_certificate_eliminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_controlledPhase_certificate_eliminant

/-- info: 'NLQCLean.exists_transcript_deficit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_transcript_deficit_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_quantum_tradeoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_quantum_tradeoff

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_borel_quantum_tradeoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_borel_quantum_tradeoff

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_sixth_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_sixth_power

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_sixth_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_sixth_log_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_loscc_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_loscc_qubit_bound

/-- info: 'NLQCLean.exists_explicit_controlledPhase_one_sharedRandom_quantum_tradeoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_explicit_controlledPhase_one_sharedRandom_quantum_tradeoff
