import NLQCLean.Exact.OrbitInvariantAlgebraicity
import NLQCLean.Exact.ControlledPhaseExclusion
import NLQCLean.Exact.BitstringExactExclusion
import NLQCLean.Exact.SpectatorExactExclusion
import NLQCLean.Invariants.SpectatorControlledPhasePurity
import NLQCLean.Approx.FiniteClassicalSpectralFloors
import NLQCLean.Models.ClassicalCommunication.BorelMixedCompression
import NLQCLean.Bounds.UniversalMaxBounds
import NLQCLean.Bounds.StrongUniversalExplicit
import NLQCLean.Bounds.SwapNeighborhoodAlmostEvery
import NLQCLean.Models.ClassicalCommunication.BorelRankCompression
import NLQCLean.Bounds.Quantitative
import NLQCLean.Bounds.AlmostEveryExact
import NLQCLean.Bounds.QualitativeDiamond
import NLQCLean.Bounds.StrongUniversalResources
import NLQCLean.Bounds.SwapFloor
import NLQCLean.Bounds.AlmostEveryQualitativeGap
import NLQCLean.Approx.SpectralFootprintFloors
import NLQCLean.Bounds.ControlledPhaseLength
import NLQCLean.Approx.GenericSpectralThresholds
import NLQCLean.Bounds.ControlledPhaseAlmostEvery
import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression
import NLQCLean.Bounds.FiniteControlledPhaseAlmostEvery
import NLQCLean.Bounds.FiniteClassicalHaar
import NLQCLean.Bounds.FiniteClassicalAlmostEvery
import NLQCLean.Bounds.ArbitraryFiniteClassicalAlmostEvery
import NLQCLean.Bounds.FiniteClassicalStrongUniversal
import NLQCLean.Bounds.FiniteClassicalQubits
import NLQCLean.Bounds.FiniteControlledPhaseQubits
import NLQCLean.Bounds.FiniteControlledPhaseLength
import NLQCLean.Models.ClassicalCommunication.FiniteOutputRestriction

/-!
# Main unitary results

Reader-facing entry point for unconditional impossibility, full-group and
near-SWAP quantitative bounds, and almost-every fixed-target conclusions.
All results here are unconditional. Supporting definitions remain in their
mathematical modules; the quantitative bounds rest on the polynomial
image-volume bound `DirectVolume.polynomialImageVolumeBound`.
-/

namespace NLQCLean.Results.Unitary

/-- Direct spectral bounds for the resource and quantum messages alone. -/
alias finite_classical_score_spectral_bound :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.scoreU_le_schmidtMass

alias finite_mixed_classical_score_spectral_bound :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_scoreU_le_schmidtMass

alias finite_classical_diamond_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.unitary_spectral_floor_of_diamondError

alias finite_mixed_classical_diamond_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_unitary_spectral_floor_of_diamondError

alias finite_classical_swap_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.swap_quantumFootprint_floor

alias finite_mixed_classical_swap_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_swap_quantumFootprint_floor

alias finite_classical_swap_diamond_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.swap_quantumFootprint_floor_of_diamondError

alias finite_mixed_classical_swap_diamond_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_swap_quantumFootprint_floor_of_diamondError

alias finite_classical_full_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.unitary_full_spectral_floor

alias finite_mixed_classical_full_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_unitary_full_spectral_floor

alias ae_finite_classical_full_spectral_threshold :=
  NLQCLean.ae_finite_classical_full_spectral_threshold

/-- The universal unitary dimension and precision lower bounds in one form. -/
alias exists_universal_max_resource_bound :=
  NLQCLean.exists_strongUniversalMaxResourceBound

alias exists_universal_max_diamond_resource_bound :=
  NLQCLean.exists_strongUniversalMaxDiamondResourceBound

/-- Explicit universal unitary bound for `d ≥ 2`:
`K ≥ d² max(1 − ε, √ln(1/ε)/51, √(ln(1/ε) − 420)/46)`. -/
alias universal_explicit_resource_bound := NLQCLean.strongUniversal_explicit

/-- Explicit universal unitary bound for `d ≥ 8`:
`K ≥ d² max(1 − ε, √ln(1/ε)/24, √(ln(1/ε) − 92)/22)`. -/
alias universal_explicit_resource_bound_of_eight := NLQCLean.strongUniversal_explicit_of_eight

alias universal_explicit_diamond_resource_bound := NLQCLean.strongUniversalDiamond_explicit

alias universal_explicit_diamond_resource_bound_of_eight :=
  NLQCLean.strongUniversalDiamond_explicit_of_eight

/-- The named forms with explicit constants: `c = 1/51`, qubit offset `6`, restricted
Haar constant `336`. -/
alias universal_resource_bound_explicit := NLQCLean.strongUniversalResourceBound_explicit

alias universal_diamond_resource_bound_explicit :=
  NLQCLean.strongUniversalDiamondResourceBound_explicit

alias universal_qubit_bound_explicit := NLQCLean.strongUniversalQubitBound_explicit

alias universal_diamond_qubit_bound_explicit :=
  NLQCLean.strongUniversalDiamondQubitBound_explicit

/-- Qubit offset `5` once `n ≥ 3`. -/
alias universal_qubit_bound_explicit_of_three := NLQCLean.strongUniversalQubitBound_explicit_of_three

alias restricted_haar_bound_explicit := NLQCLean.strongRestrictedHaarBound_explicit

alias restricted_diamond_haar_bound_explicit := NLQCLean.strongRestrictedDiamondHaarBound_explicit

/-- The split near-SWAP Haar bound `exp((595/3)K² + (687/20)N) ε^(3N/32)`, `d ≥ 2`. -/
alias restricted_haar_split_bound := NLQCLean.strongRestrictedHaarSplitBound_two

/-- The split near-SWAP Haar bound `exp((595/3)K² + (703/20)N) ε^(7N/16)`, `d ≥ 8`. -/
alias restricted_haar_split_bound_of_eight := NLQCLean.strongRestrictedHaarSplitBound_eight

/-- One fixed-target threshold throughout the near-SWAP region. -/
alias exists_ae_swap_neighborhood_resource_bound :=
  NLQCLean.exists_ae_swapNeighborhood_resource_constant

alias exists_ae_swap_neighborhood_physical_resource_bound :=
  NLQCLean.exists_ae_swapNeighborhood_physical_resource_constant

alias borel_mixed_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

alias borel_mixed_classical_diamond_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

alias borel_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint

alias borel_classical_diamond_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

/-- Actual finite-protocol restriction, with the resource and both quantum
messages unchanged and the original normalized diamond error contracted. -/
alias finite_rectangular_diagonal_diamond_error_le :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_diamondError_le

/-- The same actual restriction applies to common-map finite mixed resources. -/
alias finite_mixed_rectangular_diagonal_diamond_error_le :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedDiamondError_le

/-- Source `lem:algebraic-values`: polynomiality and invariance are needed
only on unitary matrices; every original finite architecture is allowed. -/
alias pure_orbit_invariant_algebraic :=
  NLQCLean.PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary

alias mixed_orbit_invariant_algebraic :=
  NLQCLean.MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq

/-- The direct rational-polynomial presentations of the same source result. -/
alias pure_rational_orbit_invariant_algebraic :=
  NLQCLean.PureProtocol.isAlgebraic_rationalInvariant_of_performsUnitary

alias mixed_rational_orbit_invariant_algebraic :=
  NLQCLean.MixedResource.isAlgebraic_rationalInvariant_of_mixedChannel_eq

/-- The source gate on every positive number of qubits per party, including
identity spectators and its full local-unitary orbit. -/
alias pure_first_qubit_phase_algebraic :=
  NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase

alias mixed_first_qubit_phase_algebraic :=
  NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase

alias pure_first_qubit_one_exact_exclusion :=
  NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one

alias mixed_first_qubit_one_exact_exclusion :=
  NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one

alias pure_first_qubit_one_local_orbit_exact_exclusion :=
  NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit

alias mixed_first_qubit_one_local_orbit_exact_exclusion :=
  NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one_orbit

alias first_qubit_controlled_phase_purity :=
  NLQCLean.purity_bitstringControlledPhase

/-- Exact finite pure implementation forces algebraicity of the complex
phase at any real angle. -/
alias pure_controlled_phase_phase_algebraic :=
  NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase

/-- The same necessary condition holds for common-map finite-mixed channels. -/
alias mixed_controlled_phase_phase_algebraic :=
  NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase

/-- Every nonzero algebraic-angle two-qubit controlled phase excludes all
finite pure and common-map mixed architectures. -/
alias controlled_phase_no_finite_exact_implementation :=
  NLQCLean.controlledPhase_no_finite_exact_implementation

/-- The named angle-one controlled phase has no finite exact implementation. -/
alias controlled_phase_one_no_finite_exact_implementation :=
  NLQCLean.controlledPhase_one_no_finite_exact_implementation

/-- The same exact exclusion holds throughout the full local-unitary orbit. -/
alias controlled_phase_local_orbit_no_finite_exact_implementation :=
  NLQCLean.controlledPhase_orbit_no_finite_exact_implementation

alias exists_no_finite_exact_implementation :=
  NLQCLean.exists_unitary_no_finite_exact_implementation

alias exists_qualitative_score_gap := NLQCLean.exists_unitary_qualitative_gap

alias exists_qualitative_diamond_gap := NLQCLean.exists_unitary_qualitative_diamond_gap

alias pure_swap_footprint_floor := NLQCLean.PureProtocol.swap_footprint_floor

alias mixed_swap_footprint_floor := NLQCLean.MixedResource.swap_footprint_floor

alias pure_spectral_floor := NLQCLean.PureProtocol.unitary_spectral_floor

alias mixed_spectral_floor := NLQCLean.MixedResource.unitary_spectral_floor

alias pure_exact_schmidt_rank_floor := NLQCLean.PureProtocol.unitary_exact_schmidt_rank_floor

alias mixed_exact_schmidt_rank_floor := NLQCLean.MixedResource.unitary_exact_schmidt_rank_floor

alias pure_full_spectral_floor := NLQCLean.PureProtocol.unitary_full_spectral_floor

alias mixed_full_spectral_floor := NLQCLean.MixedResource.unitary_full_spectral_floor

alias ae_full_schmidt_rank := NLQCLean.ae_unitary_operatorSchmidtRank_full

alias ae_positive_smallest_schmidt_weight := NLQCLean.ae_unitary_pos_schmidtWeight_lower_bound

alias ae_full_spectral_footprint_threshold := NLQCLean.ae_full_spectral_footprint_threshold

alias exists_score_maximum_protocol := NLQCLean.exists_unitaryScoreMaximum_protocol

alias score_deficit_eq_zero_iff := NLQCLean.unitaryScoreDeficit_eq_zero_iff

alias isCompact_pure_reachable := NLQCLean.isCompact_pureReachable

alias isCompact_mixed_reachable := NLQCLean.isCompact_mixedReachable

alias exists_general_target_gap := NLQCLean.exists_general_target_unitary_gap_of_no_finite_exact

alias ae_general_target_gap := NLQCLean.ae_general_target_unitary_gap

alias exists_charged_controlled_phase_length_bound :=
  NLQCLean.exists_chargedControlledPhase_length_constant

alias exists_ae_charged_controlled_phase_resource_bound :=
  NLQCLean.exists_ae_chargedControlledPhase_resource_constant

alias exists_ae_finite_classical_controlled_phase_log_bound :=
  NLQCLean.exists_ae_finiteControlledPhase_log_bound

alias finite_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint

alias finite_classical_diamond_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

alias finite_mixed_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

alias finite_mixed_classical_diamond_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

alias exists_finite_classical_haar_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant

alias exists_finite_classical_universal_log_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant

alias exists_ae_finite_classical_log_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_finite_classical_log_constant

alias exists_ae_arbitrary_finite_classical_log_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant

alias exists_finite_classical_strong_universal_log_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_log_constant

alias exists_ae_finite_loscc_controlled_phase_qubit_bound :=
  NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound

alias exists_finite_classical_controlled_phase_length_bound :=
  NLQCLean.exists_finiteControlledPhase_length_constant

alias exists_finite_classical_controlled_phase_worst_case_bound :=
  NLQCLean.exists_finiteControlledPhase_worst_case_constant

alias exists_finite_classical_universal_qubit_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_qubit_constant

alias exists_finite_classical_strong_universal_qubit_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_qubit_constant

alias exists_ae_finite_classical_qubit_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_finite_classical_qubit_constant

alias exists_full_group_score_haar_bound :=
  NLQCLean.exists_haar_fraction_constant

alias exists_full_group_resource_bound :=
  NLQCLean.exists_universal_resource_constant

alias exists_full_group_qubit_bound :=
  NLQCLean.exists_universal_qubit_constant

alias exists_full_group_diamond_haar_bound :=
  NLQCLean.exists_diamond_haar_constant

alias exists_full_group_diamond_resource_bound :=
  NLQCLean.exists_universal_diamond_resource_constant

alias exists_full_group_diamond_qubit_bound :=
  NLQCLean.exists_universal_diamond_qubit_constant

alias exists_restricted_haar_bound :=
  NLQCLean.exists_strongRestrictedHaarBound

alias exists_restricted_diamond_haar_bound :=
  NLQCLean.exists_strongRestrictedDiamondHaarBound

alias exists_universal_resource_bound :=
  NLQCLean.exists_strongUniversalResourceBound

alias exists_universal_diamond_resource_bound :=
  NLQCLean.exists_strongUniversalDiamondResourceBound

alias exists_universal_qubit_bound :=
  NLQCLean.exists_strongUniversalQubitBound

alias exists_universal_diamond_qubit_bound :=
  NLQCLean.exists_strongUniversalDiamondQubitBound

alias exists_ae_forbidden_error_threshold :=
  NLQCLean.exists_ae_unitary_forbidden_error_constant

alias exists_ae_resource_bound :=
  NLQCLean.exists_ae_unitary_resource_constant

alias exists_ae_diamond_resource_bound :=
  NLQCLean.exists_ae_diamond_resource_constant

alias exists_ae_physical_resource_bound :=
  NLQCLean.exists_ae_unitary_physical_resource_constant

alias exists_ae_qubit_bound :=
  NLQCLean.exists_ae_unitary_qubit_constant

alias exists_ae_diamond_qubit_bound :=
  NLQCLean.exists_ae_diamond_qubit_constant

alias ae_no_finite_exact_implementation :=
  NLQCLean.ae_unitary_no_finite_exact_implementation

end NLQCLean.Results.Unitary
