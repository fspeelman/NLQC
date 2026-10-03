import NLQCLean.Approx.FiniteClassicalSpectralFloors
import NLQCLean.Models.ClassicalCommunication.BorelMixedCompression
import NLQCLean.Models.ClassicalCommunication.BorelRankCompression
import NLQCLean.Bounds.Quantitative
import NLQCLean.Bounds.AlmostEveryExact
import NLQCLean.Bounds.PVMQualitativeGap
import NLQCLean.Approx.PVMRankFloor
import NLQCLean.Bounds.AlmostEveryQualitativeGap
import NLQCLean.Approx.GeneralizedBellBasis
import NLQCLean.Approx.GenericSpectralThresholds
import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression
import NLQCLean.Bounds.FiniteClassicalHaar
import NLQCLean.Bounds.FiniteClassicalAlmostEvery
import NLQCLean.Bounds.ArbitraryFiniteClassicalAlmostEvery
import NLQCLean.Bounds.FiniteClassicalQubits
import NLQCLean.Bounds.NearBellUniversalExplicit

/-!
# Main projective-measurement results

Reader-facing entry point for unconditional impossibility, score and joint-TV
quantitative bounds, and almost-every fixed-target conclusions. All results
here are unconditional; the quantitative bounds rest on the polynomial
image-volume bound `DirectVolume.polynomialImageVolumeBound`.
-/

namespace NLQCLean.Results.PVM

/-- Direct spectral bounds for the resource and quantum messages alone. -/
alias finite_classical_score_spectral_bound :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.scorePVM_le_max_column_schmidtMass

alias finite_mixed_classical_score_spectral_bound :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_scorePVM_le_max_column_schmidtMass

alias finite_classical_tv_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.pvm_spectral_floor_of_pvmTVError

alias finite_mixed_classical_tv_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_pvm_spectral_floor_of_pvmTVError

alias finite_classical_bell_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.generalizedBellPVM_quantumFootprint_floor

alias finite_mixed_classical_bell_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_generalizedBellPVM_quantumFootprint_floor

alias finite_classical_bell_tv_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.generalizedBellPVM_quantumFootprint_floor_of_pvmTVError

alias finite_mixed_classical_bell_tv_quantum_footprint_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_generalizedBellPVM_quantumFootprint_floor_of_pvmTVError

alias finite_classical_full_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.pvm_full_spectral_floor

alias finite_mixed_classical_full_spectral_floor :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixed_pvm_full_spectral_floor

alias ae_finite_classical_full_spectral_threshold :=
  NLQCLean.ae_finite_classical_full_spectral_threshold

alias borel_mixed_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

alias borel_mixed_classical_tv_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError

alias borel_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

alias borel_classical_tv_reachable_transfer :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

alias exists_ae_arbitrary_finite_classical_log_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant

alias exists_no_finite_exact_implementation :=
  NLQCLean.exists_pvm_no_finite_exact_implementation

alias exists_qualitative_gap := NLQCLean.exists_pvm_qualitative_gap

alias pure_footprint_floor := NLQCLean.PureProtocol.pvm_footprint_floor

alias mixed_footprint_floor := NLQCLean.MixedResource.pvm_footprint_floor

alias pure_spectral_allocation := NLQCLean.PureProtocol.pvm_spectral_allocation

alias mixed_spectral_allocation := NLQCLean.MixedResource.pvm_spectral_allocation

alias pure_exact_schmidt_rank_floor := NLQCLean.PureProtocol.pvm_exact_schmidt_rank_floor

alias mixed_exact_schmidt_rank_floor := NLQCLean.MixedResource.pvm_exact_schmidt_rank_floor

alias pure_full_spectral_floor := NLQCLean.PureProtocol.pvm_full_spectral_floor

alias mixed_full_spectral_floor := NLQCLean.MixedResource.pvm_full_spectral_floor

alias ae_full_column_schmidt_rank := NLQCLean.ae_pvmColumnSchmidtRank_full

alias ae_positive_smallest_column_schmidt_weight :=
  NLQCLean.ae_pvm_pos_uniform_schmidtWeight_lower_bound

alias ae_full_spectral_footprint_threshold := NLQCLean.ae_full_spectral_footprint_threshold

alias finite_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

alias finite_classical_tv_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

alias finite_mixed_classical_score_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

alias finite_mixed_classical_tv_reachable_transfer :=
  NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError

alias exists_finite_classical_haar_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant

alias exists_finite_classical_universal_log_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant

alias exists_ae_finite_classical_log_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_finite_classical_log_constant

alias exists_finite_classical_universal_qubit_bound :=
  NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_qubit_constant

alias exists_ae_finite_classical_qubit_bound :=
  NLQCLean.ClassicalCommunication.exists_ae_finite_classical_qubit_constant

alias generalized_bell_basis := NLQCLean.generalizedBellUnitary

alias pure_bell_footprint_floor := NLQCLean.PureProtocol.generalizedBellPVM_footprint_floor

alias mixed_bell_footprint_floor := NLQCLean.MixedResource.generalizedBellPVM_footprint_floor

alias pure_universal_cubic_floor := NLQCLean.PurePVMUniversalScore.cubic_floor

alias mixed_universal_cubic_floor := NLQCLean.MixedPVMUniversalScore.cubic_floor

alias pure_universal_quarter_floor := NLQCLean.PurePVMUniversalScore.cubic_quarter_floor

alias mixed_universal_quarter_floor := NLQCLean.MixedPVMUniversalScore.cubic_quarter_floor

alias pure_universal_qubit_floor := NLQCLean.PurePVMUniversalScore.cubic_qubit_floor

alias mixed_universal_qubit_floor := NLQCLean.MixedPVMUniversalScore.cubic_qubit_floor

alias pure_universal_tv_cubic_floor := NLQCLean.PurePVMUniversalTV.cubic_floor

alias mixed_universal_tv_cubic_floor := NLQCLean.MixedPVMUniversalTV.cubic_floor

alias pure_universal_tv_qubit_floor := NLQCLean.PurePVMUniversalTV.cubic_qubit_floor

alias mixed_universal_tv_qubit_floor := NLQCLean.MixedPVMUniversalTV.cubic_qubit_floor

alias exists_score_maximum_protocol := NLQCLean.exists_pvmScoreMaximum_protocol

alias score_deficit_eq_zero_iff := NLQCLean.pvmScoreDeficit_eq_zero_iff

alias isCompact_pure_reachable := NLQCLean.isCompact_purePVMReachable

alias isCompact_mixed_reachable := NLQCLean.isCompact_mixedPVMReachable

alias exists_general_target_gap := NLQCLean.exists_general_target_pvm_gap_of_no_finite_exact

alias ae_general_target_gap := NLQCLean.ae_general_target_pvm_gap

alias exists_full_group_score_haar_bound :=
  NLQCLean.exists_pvm_haar_fraction_constant

alias exists_full_group_tv_haar_bound :=
  NLQCLean.exists_pvm_tv_haar_constant

alias exists_universal_resource_bound :=
  NLQCLean.exists_pvm_universal_resource_constant

alias exists_universal_qubit_bound :=
  NLQCLean.exists_pvm_universal_qubit_constant

/-- Explicit universal PVM bound (Theorem B(ii)) for `d ≥ 2`:
`K ≥ max(d³(1 − ε)², d² √ln(1/ε)/36)`, score and joint TV, pure and common-map mixed. -/
alias universal_explicit_resource_bound := NLQCLean.pvmUniversal_explicit

/-- Explicit universal PVM bound for `d ≥ 3`: `K ≥ max(d³(1 − ε)², d² √ln(1/ε)/27)`. -/
alias universal_explicit_resource_bound_of_three := NLQCLean.pvmUniversal_explicit_of_three

/-- Theorem B(ii) in its displayed form with `c = 1/36`. -/
alias universal_max_resource_bound_explicit := NLQCLean.pvmUniversal_max_explicit

/-- `log₂ K ≥ max(3n − 2, 2n + ½ log₂ ln(1/ε) − 6)` at `d = 2ⁿ`. -/
alias universal_qubit_bound_explicit := NLQCLean.pvmUniversal_qubit_explicit

/-- Offset `5` once `n ≥ 2`. -/
alias universal_qubit_bound_explicit_of_two := NLQCLean.pvmUniversal_qubit_explicit_of_two

/-- The near-Bell Haar estimate with explicit factors at tube radius at most `1/2`. -/
alias near_bell_haar_bound_explicit := NLQCLean.nearBell_haar_le_sharp

alias exists_ae_forbidden_error_threshold :=
  NLQCLean.exists_ae_pvm_forbidden_error_constant

alias exists_ae_resource_bound :=
  NLQCLean.exists_ae_pvm_resource_constant

alias exists_ae_tv_resource_bound :=
  NLQCLean.exists_ae_pvm_tv_resource_constant

alias exists_ae_physical_resource_bound :=
  NLQCLean.exists_ae_pvm_physical_resource_constant

alias exists_ae_qubit_bound :=
  NLQCLean.exists_ae_pvm_qubit_constant

alias exists_ae_tv_qubit_bound :=
  NLQCLean.exists_ae_pvm_tv_qubit_constant

alias ae_no_finite_exact_implementation :=
  NLQCLean.ae_pvm_no_finite_exact_implementation

end NLQCLean.Results.PVM
