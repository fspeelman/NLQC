import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM
import NLQCLean.Bounds.BorelClassicalQubits
import NLQCLean.Bounds.FiniteLocalization
import NLQCLean.Bounds.RectangularDiagonalAlmostEvery
import NLQCLean.Bounds.FiniteControlledPhaseLength
import NLQCLean.Bounds.NearBellAlmostEvery
import NLQCLean.Bounds.BorelClassicalStrongPVM
import NLQCLean.Bounds.SharedRandomLOSCC
import NLQCLean.Bounds.BorelClassicalUniversalMax
import NLQCLean.Bounds.BorelControlledPhaseLength
import NLQCLean.Bounds.BorelLocalization
import NLQCLean.Bounds.ExplicitControlledPhase

/-!
# Robust companion: results by source label

Reader-facing names for the results of the robust companion notes
*Almost-perfect non-local quantum computation requires high-dimensional
resources* (1 October 2026 snapshot). Each alias is named after the source
label it formalizes. Theorems A–D, their corollaries, floors, compactness and
qualitative statements are unconditional; the quantitative ones rest on the
polynomial image-volume bound `DirectVolume.polynomialImageVolumeBound`.

Errors are score deficits (`1 - ε ≤ score`) unless the name says diamond or
total variation; footprints charge resource Schmidt rank times both message
dimensions. Only the effective Appendix C bound (`thm:explicit`) takes
hypotheses, the two inputs `BasuPollackRoyExistentialElimination` and the polynomial-type
transcendence measure `PolynomialTypeTranscendenceMeasureExpAngle` (implied by
`CijsouwTranscendenceMeasureExp`);
its constants are proved to exist, not to be computable.
-/

namespace NLQCLean.Results.RobustPaper

/-! ### Theorem A -/

/-- `thm:haar-fraction`, unitaries: `μ(Reach) ≤ min 1 (exp(C d² K²) ε^{κᵤ/2})`
for `K ≥ d²/4`, `0 < ε ≤ 1/2`, pure and common-map mixed resources. -/
alias thm_haar_fraction := NLQCLean.exists_haar_fraction_constant
/-- `thm:haar-fraction`, rank-one PVMs, exponent `κₘ/2`. -/
alias thm_haar_fraction_pvm := NLQCLean.exists_pvm_haar_fraction_constant
/-- `cor:universal-d`: `K ≥ c d √ln(1/ε)` for universal unitary approximation. -/
alias cor_universal_d := NLQCLean.exists_universal_resource_constant
/-- `cor:universal-d` for PVMs (score and joint total variation). -/
alias cor_universal_d_pvm := NLQCLean.exists_pvm_universal_resource_constant
/-- `cor:universal-d`, qubit form `log₂ K ≥ n + ½ log₂ ln(1/ε) - O(1)`. -/
alias cor_universal_d_qubit := NLQCLean.exists_universal_qubit_constant
alias cor_universal_d_pvm_qubit := NLQCLean.exists_pvm_universal_qubit_constant
/-- `cor:almost-every`: almost every unitary has a threshold below which
`K_ε(U) ≥ c d √ln(1/ε)`. -/
alias cor_almost_every := NLQCLean.exists_ae_resource_constant
alias cor_almost_every_pvm := NLQCLean.exists_ae_pvm_resource_constant
alias cor_almost_every_qubit := NLQCLean.exists_ae_unitary_qubit_constant
alias cor_almost_every_pvm_qubit := NLQCLean.exists_ae_pvm_qubit_constant

/-! ### Theorem B(i) and the near-SWAP region -/

/-- `thm:swap-haar`: restricted near-SWAP Haar estimate with `exp(C K²)`. -/
alias thm_swap_haar := NLQCLean.exists_strongRestrictedHaarBound
/-- `cor:universal-d2`: `K ≥ c d² max(1, √ln(1/ε))` for universal unitary
approximation, pure and common-map mixed resources. -/
alias cor_universal_d2 := NLQCLean.exists_strongUniversalMaxResourceBound
/-- `cor:universal-d2`, qubit form `log₂ K ≥ 2n + ½ log₂ ln(1/ε) - O(1)`. -/
alias cor_universal_d2_qubit := NLQCLean.exists_strongUniversalQubitBound
/-- Regional almost-every bound near SWAP (unlabelled conclusion of the SWAP section). -/
alias regional_swap_almost_every :=
  NLQCLean.exists_ae_swapNeighborhood_resource_constant

/-! ### Theorem B(ii) and the near-Bell region -/

/-- `lem:bell-compression`, message floors: near the Bell basis, a score
`≥ 1 - ε` with `ε ≤ 1/256` forces `d² ≤ 2 m_A²` and `d² ≤ 2 m_B²`. -/
alias lem_bell_compression_messages := NLQCLean.PureProtocol.sq_le_two_mul_message_sq_of_near_bell
/-- `lem:bell-compression`, column spectra in the ball: every Schmidt weight
lies in `[9/(16d), 25/(16d)]`. -/
alias lem_bell_compression_spectra := NLQCLean.schmidtWeights_mem_of_mem_bellNeighborhood
/-- The cubic floor `d³ ≤ 2K` in the near-Bell ball. -/
alias lem_bell_compression_cubic := NLQCLean.PureProtocol.cube_le_two_mul_of_mem_bellNeighborhood
/-- `lem:bell-compression`, slim witnesses: total garbage rank at most
`⌈K/d⌉ + d²`, distance `d √(50ε/9)` and admissible coordinate budget `256 K²`. -/
alias lem_bell_compression_witness := NLQCLean.PureProtocol.exists_pvm_reverse_witness_nearBell
/-- `lem:bell-compression`: `r ≤ 2K/d²` and total garbage rank `≤ 4K/d`. -/
alias lem_bell_compression_resource := NLQCLean.PVMReverseShape.IsNearBell.resource_le
alias lem_bell_compression_support := NLQCLean.PVMReverseShape.IsNearBell.supportSize_le
/-- `thm:bell-haar`: `μ(ball ∩ Reach) ≤ min 1 (exp(C K²) ε^{d⁴/16})` for
`K ≥ d³/4`, `0 < ε ≤ 1/2`. -/
alias thm_bell_haar := NLQCLean.exists_nearBell_haar_constant
/-- `cor:universal-pvm` and Theorem B(ii): `K ≥ c max(d³, d² √ln(1/ε))` for
universal PVM approximation (score and joint total variation, pure and
common-map mixed resources). -/
alias cor_universal_pvm := NLQCLean.exists_nearBell_universal_max_constant
/-- `cor:universal-pvm`, qubit form
`log₂ K ≥ max(3n - 2, 2n + ½ log₂ ln(1/ε) - O(1))`. -/
alias cor_universal_pvm_qubit := NLQCLean.exists_nearBell_universal_qubit_constant
/-- `cor:universal-pvm`, unconditional floor `K ≥ d³(1 - ε)²`. -/
alias cor_universal_pvm_floor := NLQCLean.PurePVMUniversalScore.cubic_floor
alias cor_universal_pvm_floor_mixed := NLQCLean.MixedPVMUniversalScore.cubic_floor
/-- Regional almost-every bound near the Bell basis: for the PVM of
Haar-almost every basis matrix in the ball, `K_ε ≥ c d² √ln(1/ε)` below a
target-dependent threshold (unlabelled conclusion of the Bell section). -/
alias regional_bell_almost_every := NLQCLean.exists_ae_bellNeighborhood_resource_constant

/-! ### Theorem C -/

/-- `lem:free-classical-compression`: actual Borel pure protocols with free
classical messages enter the charged score class at footprint `4 d⁴ Kq⁵`. -/
alias lem_free_classical_compression :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint
alias lem_free_classical_compression_pvm :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint
/-- `lem:free-classical-floors` (i) and (ii). -/
alias lem_free_classical_floors_unitary :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_spectral_floor
alias lem_free_classical_floors_pvm :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_spectral_floor
/-- `lem:free-classical-floors`: `SWAP` needs `Kq ≥ d²(1-ε)`. -/
alias lem_free_classical_floors_swap :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.swap_quantumFootprint_floor
/-- `lem:free-classical-floors`: a maximally entangled basis needs `Kq ≥ d(1-ε)`. -/
alias lem_free_classical_floors_bell :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.generalizedBellPVM_quantumFootprint_floor
/-- `lem:free-classical-floors`: generic thresholds `Kq ≥ d²` and `Kq ≥ d`. -/
alias lem_free_classical_floors_generic :=
  NLQCLean.ClassicalCommunication.ae_borel_classical_full_spectral_threshold
/-- `cor:free-classical`, outer Haar bounds `exp(C d¹⁰ Kq¹⁰) ε^{κ/2}`. -/
alias cor_free_classical_haar :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant
alias cor_free_classical_haar_pvm :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant
/-- `cor:free-classical` (i), unitaries: `log₂ Kq ≥ (1/10) log₂ ln(1/ε) - (2/5) n - O(1)`. -/
alias cor_free_classical_universal :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_qubit_constant
/-- `cor:free-classical` (i), PVMs: `log₂ Kq ≥ (1/10) log₂ ln(1/ε) - (2/5) n - O(1)`,
via the near-Bell theorem B(ii). -/
alias cor_free_classical_universal_pvm :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_strong_pvm_universal_qubit_constant
/-- The same with the weaker coefficient `-(3/5) n` from the full-group bound. -/
alias cor_free_classical_universal_pvm_weak :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_qubit_constant
/-- `cor:free-classical` (i) in every dimension `d ≥ 2`, over the whole Borel and
shared-randomness class: `Kq ≥ max(d²(1-ε), c d^{-2/5} ln(1/ε)^{1/10})` for
unitaries and `Kq ≥ max(d(1-ε), c d^{-2/5} ln(1/ε)^{1/10})` for PVMs. -/
alias cor_free_classical_universal_max :=
  NLQCLean.ClassicalCommunication.exists_borel_classical_universal_max_constant
/-- `cor:free-classical` (ii) with the floors of Theorem C: one threshold for
the precision bound with `-(3/5) n` and `Kq ≥ d²` / `Kq ≥ d`. -/
alias cor_free_classical_almost_every :=
  NLQCLean.ClassicalCommunication.exists_ae_borel_classical_qubit_and_floor_constant
/-- `cor:localization` for finite-outcome local measurements and reporting:
`r ≥ max(d, c d^{-3/5} ln(1/ε)^{1/10})` below a target threshold. -/
alias cor_localization :=
  NLQCLean.ClassicalCommunication.exists_ae_finite_localization_rank_constant
/-- `cor:localization`, outer measure of localizable PVMs at Schmidt number `r`. -/
alias cor_localization_haar :=
  NLQCLean.ClassicalCommunication.exists_finite_localization_haar_constant
/-- `cor:localization` with outcomes in standard Borel spaces and a measurable
reporting function (the source scope), pure and common-map mixed resources. -/
alias cor_localization_borel :=
  NLQCLean.ClassicalCommunication.exists_ae_borel_localization_rank_constant
alias cor_localization_borel_haar :=
  NLQCLean.ClassicalCommunication.exists_borel_localization_haar_constant

/-! ### Appendix C, step 1 -/

/-- `thm:explicit`, step 1: `g_K(θ) > 0` for every nonzero real algebraic
angle, in particular `g_K(1) > 0`. -/
alias thm_explicit_deficit_pos := NLQCLean.controlledPhaseLeastDeficit_pos
alias thm_explicit_deficit_one_pos := NLQCLean.controlledPhaseLeastDeficit_one_pos
/-- `thm:explicit`, step 1: an attaining architecture in the `4K` box with at
most `82 K²` real coordinates, an integer sum-of-squares constraint and an
integer score polynomial with explicit degree and coefficient bounds. -/
alias thm_explicit_polynomial_model :=
  NLQCLean.exists_controlledPhaseLeastDeficit_polynomial_certificate
/-- `thm:explicit`, step 5: free standard-Borel classical messages enter at
footprint `64 Kq⁵`. -/
alias thm_explicit_free_classical_transfer :=
  NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le

/-- `thm:explicit` (Theorem E): for every nonzero real algebraic angle,
`g_K(θ) ≥ exp(-exp(C_E K²))` for all `K ≥ 1`; from E-QE and weak E-TM. -/
alias thm_explicit := NLQCLean.exists_explicit_controlledPhaseLeastDeficit_lower_bound
/-- `thm:explicit`: Cijsouw's transcendence measure (E-TM) implies the
polynomial-type measure (weak E-TM) that the effective bound takes. -/
alias thm_explicit_cijsouw_polynomialType :=
  NLQCLean.CijsouwTranscendenceMeasureExp.polynomialType
/-- `thm:explicit` for the named gate `C₁`. -/
alias thm_explicit_one := NLQCLean.exists_explicit_controlledPhase_one_lower_bound
/-- `thm:explicit`, protocol form: charged footprint `exp(-exp(C_E K²))` and free
standard-Borel classical messages `exp(-exp(4096 C_E Kq¹⁰))`. -/
alias thm_explicit_protocol := NLQCLean.exists_explicit_controlledPhase_protocol_bound
/-- `thm:explicit`: `log₂ K ≥ ½ log₂ ln ln(1/ε) - O(1)` for `0 < ε < 1/e`. -/
alias thm_explicit_iterated_log := NLQCLean.exists_explicit_controlledPhase_iterated_log_bound
/-- `thm:explicit`: `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - O(1)` with free classical messages. -/
alias thm_explicit_quantum_iterated_log :=
  NLQCLean.exists_explicit_controlledPhase_quantum_iterated_log_bound

/-! ### Setting, floors and qualitative divergence -/

/-- `prop:qualitative`: least deficit attained. -/
alias prop_qualitative_attained := NLQCLean.exists_unitaryScoreMaximum_protocol
alias prop_qualitative_attained_pvm := NLQCLean.exists_pvmScoreMaximum_protocol
/-- `prop:qualitative`: zero least deficit iff exact. -/
alias prop_qualitative_exact := NLQCLean.unitaryScoreDeficit_eq_zero_iff
alias prop_qualitative_exact_pvm := NLQCLean.pvmScoreDeficit_eq_zero_iff
/-- `prop:qualitative`: compact reachable sets. -/
alias prop_qualitative_compact := NLQCLean.isCompact_pureReachable
alias prop_qualitative_compact_mixed := NLQCLean.isCompact_mixedReachable
alias prop_qualitative_compact_pvm := NLQCLean.isCompact_purePVMReachable
alias prop_qualitative_compact_mixed_pvm := NLQCLean.isCompact_mixedPVMReachable
/-- `prop:qualitative`: a target without exact protocol has a positive gap at
every footprint, so `K_ε(T) → ∞`. -/
alias prop_qualitative_gap := NLQCLean.exists_general_target_unitary_gap_of_no_finite_exact
alias prop_qualitative_gap_pvm := NLQCLean.exists_general_target_pvm_gap_of_no_finite_exact

/-- `lem:floors` (i): the score is at most the top-`K` Schmidt mass of the Choi vector. -/
alias lem_floors_unitary := NLQCLean.PureProtocol.unitary_spectral_floor
alias lem_floors_unitary_mixed := NLQCLean.MixedResource.unitary_spectral_floor
/-- `lem:floors` (ii): spectral allocation for PVMs. -/
alias lem_floors_pvm := NLQCLean.PureProtocol.pvm_spectral_allocation
alias lem_floors_pvm_mixed := NLQCLean.MixedResource.pvm_spectral_allocation
/-- `lem:floors`: `SWAP` needs `K ≥ d²(1-ε)`. -/
alias lem_floors_swap := NLQCLean.PureProtocol.swap_footprint_floor
alias lem_floors_swap_mixed := NLQCLean.MixedResource.swap_footprint_floor
/-- `lem:floors`: every basis needs `K ≥ d²(1-ε)²`. -/
alias lem_floors_basis := NLQCLean.PureProtocol.pvm_footprint_floor
alias lem_floors_basis_mixed := NLQCLean.MixedResource.pvm_footprint_floor
/-- `lem:floors`: a maximally entangled basis needs `K ≥ d³(1-ε)²`. -/
alias lem_floors_bell := NLQCLean.PureProtocol.generalizedBellPVM_footprint_floor
alias lem_floors_bell_mixed := NLQCLean.MixedResource.generalizedBellPVM_footprint_floor
/-- `lem:floors` at `ε = 0`: operator-Schmidt rank. -/
alias lem_floors_exact := NLQCLean.PureProtocol.unitary_exact_schmidt_rank_floor
alias lem_floors_exact_pvm := NLQCLean.PureProtocol.pvm_exact_schmidt_rank_floor
/-- `lem:floors` (iii): generic targets need `K ≥ d²` / `K ≥ d³` below a
target-dependent threshold. -/
alias lem_floors_generic := NLQCLean.ae_full_spectral_footprint_threshold

/-! ### Diagonal gates -/

/-- `prop:phase-length`, charged controlled phase. -/
alias prop_phase_length := NLQCLean.exists_chargedControlledPhase_length_constant
/-- `prop:phase-length`, finite free-classical controlled phase. -/
alias prop_phase_length_free_classical :=
  NLQCLean.exists_finiteControlledPhase_length_constant
/-- `prop:phase-length`, free standard-Borel classical messages and shared
randomness (the source model). -/
alias prop_phase_length_borel := NLQCLean.exists_borelControlledPhase_length_constant
/-- `thm:diagonal`, charged footprint, coefficient `1/2`, original diamond error. -/
alias thm_diagonal := NLQCLean.exists_ae_chargedRectangularDiagonal_qubit_bound
/-- `thm:diagonal`, finite free classical messages, coefficient `1/10`. -/
alias thm_diagonal_free_classical := NLQCLean.exists_ae_finiteRectangularDiagonal_qubit_bound
/-- `thm:diagonal`, finite LOSCC, initial-resource qubits with coefficient `1/5`. -/
alias thm_diagonal_loscc := NLQCLean.exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound
/-- `thm:diagonal` (ii), free standard-Borel classical messages, pure and
common-map mixed resources: quantum-footprint coefficient `1/10`. -/
alias thm_diagonal_borel := NLQCLean.exists_ae_borelRectangularDiagonal_qubit_bound
/-- `thm:diagonal` (ii), standard-Borel LOSCC: initial-resource-qubit coefficient `1/5`. -/
alias thm_diagonal_borel_loscc :=
  NLQCLean.exists_ae_borelLOSCCRectangularDiagonal_qubit_bound
/-- `thm:diagonal`, worst case: in each dimension one hard diagonal gate with a
threshold valid for every architecture and budget. -/
alias thm_diagonal_worst_case := NLQCLean.exists_hard_chargedRectangularDiagonal_qubit_bound
alias thm_diagonal_free_classical_worst_case :=
  NLQCLean.exists_hard_finiteRectangularDiagonal_qubit_bound
alias thm_diagonal_loscc_worst_case :=
  NLQCLean.exists_hard_finiteLOSCCRectangularDiagonal_qubit_bound
alias thm_diagonal_borel_worst_case :=
  NLQCLean.exists_hard_borelRectangularDiagonal_qubit_bound
alias thm_diagonal_borel_loscc_worst_case :=
  NLQCLean.exists_hard_borelLOSCCRectangularDiagonal_qubit_bound
/-- `thm:diagonal`, two qubits with Choi infidelity: almost every diagonal
two-qubit gate, charged reachability (`K ≥ c √ln(1/ε)`) and free standard-Borel
classical messages (`ln(1/ε) ≤ C Kq¹⁰`). -/
alias thm_diagonal_two_qubit_choi := NLQCLean.exists_ae_twoQubitDiagonal_resource_constant
alias thm_diagonal_two_qubit_choi_borel :=
  NLQCLean.exists_ae_borelTwoQubitDiagonal_log_bound
/-- `thm:diagonal` (ii) with free shared randomness over standard-Borel
protocols (pure and common-map mixed branches): `ln(1/ε) ≤ C Kq¹⁰`. -/
alias thm_diagonal_shared_random :=
  NLQCLean.exists_ae_sharedRandomRectangularDiagonal_log_bound
alias thm_diagonal_shared_random_mixed :=
  NLQCLean.exists_ae_mixedSharedRandomRectangularDiagonal_log_bound
/-- `thm:diagonal` (ii), `n_res` with free shared randomness and a branchwise
qubit cap: coefficient `1/5`. -/
alias thm_diagonal_shared_random_loscc :=
  NLQCLean.exists_ae_sharedRandomLOSCCRectangularDiagonal_qubit_bound
/-- `thm:diagonal`, two qubits, `n_res` with Choi infidelity and shared randomness. -/
alias thm_diagonal_two_qubit_choi_loscc :=
  NLQCLean.exists_ae_sharedRandomLOSCCTwoQubitDiagonal_qubit_bound
/-- `thm:diagonal`, the controlled phase `C_θ` for almost every `θ` (charged). -/
alias thm_diagonal_controlled_phase :=
  NLQCLean.exists_ae_chargedControlledPhase_resource_constant
/-- `rem:two-qubit`: `n_res ≥ (1/5) log₂ ln(1/ε) - O(1)` for Haar-almost every
two-qubit unitary, LOSCC with free shared randomness. The `log₂ K_ε` claim is
`cor_almost_every_qubit` at `n = 1`. -/
alias rem_two_qubit_loscc :=
  NLQCLean.exists_ae_sharedRandomLOSCCTwoQubit_qubit_bound

end NLQCLean.Results.RobustPaper
