import NLQCLean.Bounds.ControlledPhaseLength

/-!
# Controlled-phase scalar certificate audit

These boundaries use the full ambient derivative, both signs of sine,
the corner permutation, charged protocol coverage, and the proved
image-volume bound.
-/

set_option pp.deepTerms true
set_option pp.universes false
set_option format.width 120

namespace NLQCTests

open NLQCLean Matrix
open scoped Matrix.Norms.Frobenius

set_option pp.universes true in
#check @NLQCLean.realign_trace_eq_swap_trace

/-- info: 'NLQCLean.realign_trace_eq_swap_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.realign_trace_eq_swap_trace

set_option pp.universes true in
#check @NLQCLean.norm_fderiv_purity_apply_le

/-- info: 'NLQCLean.norm_fderiv_purity_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.norm_fderiv_purity_apply_le

set_option pp.universes true in
#check @NLQCLean.fderiv_purity_localSkew_eq_zero

/-- info: 'NLQCLean.fderiv_purity_localSkew_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.fderiv_purity_localSkew_eq_zero

set_option pp.universes true in
#check @NLQCLean.purity_controlledPhase

/-- info: 'NLQCLean.purity_controlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_controlledPhase

set_option pp.universes true in
#check @NLQCLean.controlledPhase_eq_phaseFamily_upper

/-- info: 'NLQCLean.controlledPhase_eq_phaseFamily_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_eq_phaseFamily_upper

set_option pp.universes true in
#check @NLQCLean.controlledPhase_eq_phaseFamily_lower

/-- info: 'NLQCLean.controlledPhase_eq_phaseFamily_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_eq_phaseFamily_lower

set_option pp.universes true in
#check @NLQCLean.exists_phasePurity_inverse_lipschitz_upper

/-- info: 'NLQCLean.exists_phasePurity_inverse_lipschitz_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_phasePurity_inverse_lipschitz_upper

set_option pp.universes true in
#check @NLQCLean.exists_phasePurity_inverse_lipschitz_lower

/-- info: 'NLQCLean.exists_phasePurity_inverse_lipschitz_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_phasePurity_inverse_lipschitz_lower

set_option pp.universes true in
#check @NLQCLean.ReverseBlocks.fderiv_coordinatePurity_eq_residual

/-- info: 'NLQCLean.ReverseBlocks.fderiv_coordinatePurity_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ReverseBlocks.fderiv_coordinatePurity_eq_residual

set_option pp.universes true in
#check @NLQCLean.ReverseBlocks.thickenedScalarPurityPolynomial_degree

/-- info: 'NLQCLean.ReverseBlocks.thickenedScalarPurityPolynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ReverseBlocks.thickenedScalarPurityPolynomial_degree

set_option pp.universes true in
#check @NLQCLean.ReverseBlocks.scalarPurityWitnessFormat_source_radius_lt_three

/-- info: 'NLQCLean.ReverseBlocks.scalarPurityWitnessFormat_source_radius_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ReverseBlocks.scalarPurityWitnessFormat_source_radius_lt_three

set_option pp.universes true in
#check @NLQCLean.pureReachable_purity_mem_scalarWitness

/-- info: 'NLQCLean.pureReachable_purity_mem_scalarWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pureReachable_purity_mem_scalarWitness

set_option pp.universes true in
#check @NLQCLean.mixedReachable_purity_mem_scalarWitness

/-- info: 'NLQCLean.mixedReachable_purity_mem_scalarWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mixedReachable_purity_mem_scalarWitness

set_option pp.universes true in
#check @NLQCLean.exists_scalarPurityWitness_volume_constant

/-- info: 'NLQCLean.exists_scalarPurityWitness_volume_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_scalarPurityWitness_volume_constant

set_option pp.universes true in
#check @NLQCLean.exists_chargedControlledPhase_length_constant

/-- info: 'NLQCLean.exists_chargedControlledPhase_length_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_chargedControlledPhase_length_constant

set_option pp.universes true in
#check @NLQCLean.chargedControlledPhaseAngles_eq_mixed
set_option pp.universes true in
#check @NLQCLean.volume_le_inverse_lipschitz_image

example (θ : ℝ) : purity (1 / 16) (controlledPhase θ) = (3 + Real.cos θ) / 4 :=
  purity_controlledPhase θ

example {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    controlledPhase θ =
      (phaseFamily 2 (Real.cos θ)).submatrix qubitCornerFlip qubitCornerFlip :=
  controlledPhase_eq_phaseFamily_upper h0 hπ

example {K : ℕ} (s : ReverseShape 2 K) (c : ℝ) (i : Fin 1) :
    ((ReverseBlocks.thickenedScalarPurityPolynomial s c).coordinates i).totalDegree ≤ 72 :=
  ReverseBlocks.thickenedScalarPurityPolynomial_degree s c i

example {K : ℕ} (s : ReverseShape 2 K) (δ : ℝ) :
    (ReverseBlocks.scalarPurityWitnessFormat s δ).numEquations +
      (ReverseBlocks.scalarPurityWitnessFormat s δ).numInequalities = 9 :=
  ReverseBlocks.scalarPurityWitnessFormat_constraint_count s δ

example {K : ℕ} (s : ReverseShape 2 K) (δ : ℝ)
    {z : RealEuclidean (witnessCoordinateBudget 2 K + 1)}
    (hz : z ∈ (ReverseBlocks.scalarPurityWitnessFormat s δ).source) : ‖z‖ < 3 :=
  ReverseBlocks.scalarPurityWitnessFormat_source_radius_lt_three s δ hz

end NLQCTests
