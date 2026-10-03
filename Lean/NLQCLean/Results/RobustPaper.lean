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
import NLQCLean.Geometry.UnitaryFrobeniusVolume
import NLQCLean.Approx.PVMWitnessCutoff
import NLQCLean.Geometry.PolynomialTube
import NLQCLean.Approx.WitnessFamilies
import NLQCLean.Bounds.ExplicitControlledPhaseQE
import NLQCLean.Bounds.ExplicitControlledPhaseFree
import NLQCLean.Bounds.ExplicitControlledPhaseGelfond
import NLQCLean.ImageVolume.PolynomialImageVolume
import NLQCLean.Bounds.FixedBudgetStability
import NLQCLean.Bounds.FixedBudgetStabilityPVM
import NLQCLean.Bounds.ExplicitControlledPhaseTranscript
import NLQCLean.Bounds.ExplicitControlledPhaseSharedRandom
import NLQCLean.Bounds.ExplicitControlledPhaseAngle

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
`CijsouwTranscendenceMeasureExp`). The latter is proved
(`thm_explicit_transcendence_measure_angle`), and the `thm_explicit*_of_QE` forms take
`BasuPollackRoyExistentialElimination` only;
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
/-- `cor:universal-d2` with explicit constants:
`K ≥ d² max(1 − ε, √ln(1/ε)/51, √(ln(1/ε) − 420)/46)`. -/
alias cor_universal_d2_explicit := NLQCLean.strongUniversal_explicit
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
/-- `cor:universal-pvm` with explicit constants: `K ≥ max(d³(1 − ε)², d² √ln(1/ε)/36)`. -/
alias cor_universal_pvm_explicit := NLQCLean.pvmUniversal_explicit
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
classical messages enter the charged score class at footprint `d⁴ Kq⁵`. -/
alias lem_free_classical_compression :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint
alias lem_free_classical_compression_pvm :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint
/-- `lem:free-classical-compression` (iii)–(iv): at most `(d r')²` outcomes per party, a
pure resource of the original Schmidt rank, the score not decreased, and the coherent charged
footprint `d⁴ Kq⁵`. -/
alias lem_free_classical_compression_outcomes :=
  NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_bounded_outcomes_charged_linearScore
/-- The pruning step of `lem:free-classical-compression`: at most `s²` outcomes of a finite
instrument do not decrease a real-linear score. -/
alias lem_free_classical_compression_pruning :=
  NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_nondecreasing_compression
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
footprint `16 Kq⁵`. -/
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
standard-Borel classical messages `exp(-exp(256 C_E Kq¹⁰))`. -/
alias thm_explicit_protocol := NLQCLean.exists_explicit_controlledPhase_protocol_bound
/-- `thm:explicit`: `log₂ K ≥ ½ log₂ ln ln(1/ε) - O(1)` for `0 < ε < 1/e`. -/
alias thm_explicit_iterated_log := NLQCLean.exists_explicit_controlledPhase_iterated_log_bound
/-- `thm:explicit`: `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - O(1)` with free classical messages. -/
alias thm_explicit_quantum_iterated_log :=
  NLQCLean.exists_explicit_controlledPhase_quantum_iterated_log_bound

/-! ### Appendix C with quantifier elimination as the only input -/

/-- Hypothesis-free transcendence measure for `e^i` (Hermite's method):
`|P(e^i)|² ≥ Z^{-Z^{2N+9}}`, `Z = 6(N+1)²(H+1)²`, for every nonzero integer polynomial of
degree at most `N ≥ 1` and height at most `H`. -/
alias thm_explicit_transcendence_measure_exp_I :=
  NLQCLean.ExpITranscendence.normSq_aeval_exp_I_ge
/-- `thm:explicit` for `C₁`, assuming only E-QE: `g_K(1) ≥ exp(-exp(exp(C K²)))`. -/
alias thm_explicit_one_of_QE := NLQCLean.exists_explicit_controlledPhase_one_lower_bound_of_QE
/-- Protocol and free-classical forms: `ε ≥ exp(-exp(exp(C K²)))`, resp.
`exp(-exp(exp(256 C Kq¹⁰)))`. -/
alias thm_explicit_one_protocol_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_one_protocol_bound_of_QE
/-- `log₂ K ≥ ½ log₂ ln ln ln(1/ε) - O(1)`. -/
alias thm_explicit_one_triple_log_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_one_triple_log_bound_of_QE

/-! ### Appendix C without external inputs -/

/-- The least deficit and `cos 1` are a root of an explicit nonzero integer polynomial of
degree at most `L = (835 K²)^(2^(2+164K²))` with coefficients at most `(2⁵⁵ K¹⁴)^(L³)`. -/
alias thm_explicit_one_eliminant := NLQCLean.exists_controlledPhase_one_eliminant
/-- `thm:explicit` for `C₁` with no hypothesis: `g_K(1) ≥ exp(-exp(exp(exp(171 K²))))`. -/
alias thm_explicit_one_free := NLQCLean.controlledPhase_one_lower_bound_free
/-- Protocol and free-classical forms: `ε ≥ exp(-exp(exp(exp(171 K²))))`, resp.
`exp(-exp(exp(exp(43776 Kq¹⁰))))`. -/
alias thm_explicit_one_protocol_free := NLQCLean.controlledPhase_one_protocol_bound_free
/-- `log₂ K ≥ ½ log₂ ln ln ln ln(1/ε) - ½ log₂ 171` for `0 < ε < exp(-exp e)`. -/
alias thm_explicit_one_quadruple_log_free := NLQCLean.controlledPhase_one_quadruple_log_bound_free

/-! ### Appendix C: the direct transcript parametrization -/

/-- `eq:explicit-quantum-variables` (transfer): a finite free-classical protocol on
rank-sized resource registers has the same operational channel as a single-operator transcript
protocol with retained dimensions `kA ≤ 2ra`, `kB ≤ 2rb` and decoder environments
`eA ≤ 2 kA b`, `eB ≤ 2 kB a`. -/
alias thm_explicit_transcript_representative :=
  NLQCLean.ClassicalCommunication.exists_transcript_representative
/-- `eq:explicit-quantum-variables` (count): at most `1090 r⁴ q²` real coordinates. -/
alias thm_explicit_transcript_coordinates := NLQCLean.TranscriptPolynomial.card_tCoordIndex_le
/-- `eq:explicit-quantum-tradeoff`, finite free-classical protocols, E-QE only:
`ε ≥ exp(-exp(C R⁴ Kq²))`. -/
alias thm_explicit_one_quantum_tradeoff :=
  NLQCLean.exists_explicit_controlledPhase_one_quantum_tradeoff
/-- `eq:explicit-quantum-tradeoff`, standard-Borel free-classical protocols, pure and
common-map mixed resources, E-QE only. -/
alias thm_explicit_one_borel_quantum_tradeoff :=
  NLQCLean.exists_explicit_controlledPhase_one_borel_quantum_tradeoff
/-- `eq:explicit-quantum-tradeoff` with measurable shared randomness under uniform budgets,
pure and common-map mixed branches, E-QE only. -/
alias thm_explicit_one_sharedRandom_quantum_tradeoff :=
  NLQCLean.exists_explicit_controlledPhase_one_sharedRandom_quantum_tradeoff
/-- `thm:explicit`: `ε ≥ exp(-exp(C Kq⁶))` for every protocol of quantum footprint `Kq`. -/
alias thm_explicit_one_sixth_power := NLQCLean.exists_explicit_controlledPhase_one_sixth_power
/-- `thm:explicit`: `log₂ K_{q,ε}(C₁) ≥ (1/6) log₂ ln ln(1/ε) - O(1)`. -/
alias thm_explicit_one_sixth_log := NLQCLean.exists_explicit_controlledPhase_one_sixth_log_bound
/-- `thm:explicit`: in LOSCC, at least `(1/3) log₂ ln ln(1/ε) - O(1)` resource qubits. -/
alias thm_explicit_one_loscc_qubits :=
  NLQCLean.exists_explicit_controlledPhase_one_loscc_qubit_bound

/-! ### Appendix C with the Gelfond measure for `e^i` -/

/-- Polynomial-type transcendence measure for `e^i` (Gelfond's method), for irreducible
`G ∈ ℤ[i][X]` of degree at most `B` with coefficients at most `2^B`, `B ≥ 128`:
`|G(e^i)| ≥ 2^{-B (200 B^{31} + 1)}`. -/
alias thm_gelfond_measure_exp_I_irreducible :=
  NLQCLean.Gelfond.norm_eval_exp_I_ge_of_irreducible
/-- Polynomial-type transcendence measure for `e^i`: for nonzero `P ∈ ℤ[X]` of degree at most
`N ≤ B` and height at most `H` with `2^N (N+1) H ≤ 2^B`, `B ≥ 128`,
`|P(e^i)| ≥ 2^{-N B (200 B^{31} + 1)}`. -/
alias thm_gelfond_measure_exp_I := NLQCLean.Gelfond.norm_eval_exp_I_ge
/-- `thm:explicit` for `C₁` with no hypothesis, triple exponential:
`g_K(1) ≥ exp(-exp(exp(175 K²)))`. -/
alias thm_explicit_one_free_triple := NLQCLean.controlledPhase_one_lower_bound_free_triple
/-- Protocol and free-classical forms: `ε ≥ exp(-exp(exp(175 K²)))`, resp.
`exp(-exp(exp(44800 Kq¹⁰)))`. -/
alias thm_explicit_one_protocol_free_triple :=
  NLQCLean.controlledPhase_one_protocol_bound_free_triple
/-- `log₂ K ≥ ½ log₂ ln ln ln(1/ε) - ½ log₂ 175` for `0 < ε < exp(-e)`. -/
alias thm_explicit_one_triple_log_free := NLQCLean.controlledPhase_one_triple_log_bound_free
/-- `thm:explicit` for `C₁`, assuming only E-QE, double exponential:
`g_K(1) ≥ exp(-exp(C K²))`. -/
alias thm_explicit_one_double_exp_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_one_double_exp_bound_of_QE
/-- Protocol and free-classical forms: `ε ≥ exp(-exp(C K²))`, resp.
`exp(-exp(256 C Kq¹⁰))`. -/
alias thm_explicit_one_protocol_double_exp_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_one_protocol_double_exp_bound_of_QE
/-- `log₂ K ≥ ½ log₂ ln ln(1/ε) - O(1)`. -/
alias thm_explicit_one_iterated_log_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_one_iterated_log_bound_of_QE

/-! ### Appendix C for every algebraic angle with quantifier elimination as the only input -/

/-- Liouville inequality over `ℤ[i][ϑ]` used in the doubling step for `e^{iθ}`. -/
alias thm_gelfond_angle_liouville := NLQCLean.Gelfond.eq_zero_of_norm_small_angle
/-- Gelfond's method for `e^{iθ}`, `aθ` a root of a monic `f ∈ ℤ[X]`: for nonzero
`P ∈ ℤ[X]` of degree at most `N ≤ B` and height at most `H` with `2^N (N+1) H ≤ 2^B`, and `B`
also bounding `a`, `deg f`, `1 + max|f_i|` and `|θ|`, `|P(e^{iθ})| ≥ 2^{-N B (B⁴⁸ + 1)}`. -/
alias thm_gelfond_measure_angle := NLQCLean.Gelfond.norm_eval_exp_angle_ge
/-- The weak E-TM (`PolynomialTypeTranscendenceMeasureExpAngle`) is a theorem: exponent `50`. -/
alias thm_explicit_transcendence_measure_angle :=
  NLQCLean.polynomialTypeTranscendenceMeasureExpAngle
/-- `thm:explicit` for every nonzero real algebraic angle, assuming only E-QE. -/
alias thm_explicit_of_QE := NLQCLean.exists_explicit_controlledPhaseLeastDeficit_lower_bound_of_QE
/-- `thm:explicit`, protocol form, assuming only E-QE. -/
alias thm_explicit_protocol_of_QE := NLQCLean.exists_explicit_controlledPhase_protocol_bound_of_QE
/-- `thm:explicit`, `log₂ K ≥ ½ log₂ ln ln(1/ε) - O(1)`, assuming only E-QE. -/
alias thm_explicit_iterated_log_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_iterated_log_bound_of_QE
/-- `thm:explicit`, `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - O(1)`, assuming only E-QE. -/
alias thm_explicit_quantum_iterated_log_of_QE :=
  NLQCLean.exists_explicit_controlledPhase_quantum_iterated_log_bound_of_QE

/-! ### Setting, floors and qualitative divergence -/

/-- `cor:fixed-budget-stability` (unitary targets): for `d ≥ 2`, `K ≥ 1` and nonempty
`E_{d,K} = Reach_{K,0}`, every `T ∈ Reach_{K,ε}` is within normalized Frobenius distance
`C ε^α` of `E_{d,K}`. -/
alias cor_fixed_budget_stability := NLQCLean.FixedBudget.exists_fixedBudget_stability
/-- `cor:fixed-budget-stability`: `E_{d,K}` is a finite union of local-equivalence orbits. -/
alias cor_fixed_budget_stability_orbits := NLQCLean.FixedBudget.exists_exactSet_eq_iUnion_orbits
/-- `cor:fixed-budget-stability` for PVMs (basis unitaries): for `d ≥ 2`, `K ≥ 1` and a basis
with an exact protocol of footprint at most `K`, every `M ∈ Reach^{PVM}_{K,ε}` is within
normalized Frobenius distance `C ε^α` of `Reach^{PVM}_{K,0}`. -/
alias cor_fixed_budget_stability_pvm := NLQCLean.FixedBudget.exists_fixedBudget_stability_pvm
/-- `cor:fixed-budget-stability` for PVMs: the exact basis set is a finite union of basis
orbits. -/
alias cor_fixed_budget_stability_pvm_orbits :=
  NLQCLean.FixedBudget.exists_pvmExactSet_eq_iUnion_orbits
/-- The semialgebraic Łojasiewicz inequality used for `cor:fixed-budget-stability`. -/
alias lojasiewicz_inequality := NLQCLean.lojasiewicz_inequality

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

/-! ### Appendix A: ingredients of the tube estimate -/

/-- `prop:witness`, unitaries: at most `e^{3D}` compact families of norm `√6`, cut out by
eight constraints of degree at most `100`, covering the reachable set at normalized distance
`δ = √(2ε)`, with the derivative split `rank A ≤ 4d² − 3`, `‖dT̂‖ ≤ D`, `‖B‖ ≤ δD`. -/
alias prop_witness := NLQCLean.witnessFamilies_unitary
/-- `prop:witness`, measurements, with `δ = 2√ε` and `rank A ≤ 3d² − 2`. -/
alias prop_witness_pvm := NLQCLean.witnessFamilies_pvm

/-- `lem:image-volume` for every format budget `Δ₀ ≥ 2` (at most `Δ₀` equations and weak
inequalities of degree at most `Δ₀`, `DirectVolume.PolyFormat` = `def:format`) and radius
`R₀`: `Vol_m(φ(Y)) ≤ C^(k+m) ω_m sup J_m φ` for polynomial `φ` of degree at most `Δ₀`. -/
alias lem_image_volume := NLQCLean.DirectVolume.exists_polynomialImageVolume_constant
/-- `lem:image-volume` with the explicit constant `max(4, R+1)(2Δ+1)c'`. -/
alias lem_image_volume_explicit := NLQCLean.DirectVolume.volume_image_le_of_polyFormat
/-- `lem:image-volume` for the library's fixed format (at most `20` constraints of degree at
most `100`, radius `3`) with the smaller base `35248`, by the barrier route. -/
alias lem_image_volume_barrier := NLQCLean.polynomialImageVolumeBoundWith_imageVolumeConstant
/-- `prop:tube` in its displayed form `μ(S) ≤ e^{C(D+N)} [C(L+s)]^ℓ (Cs)^{N-ℓ}`, with the
singular-value hypotheses in their variational form `dT̂ = A + B`, `rank A ≤ ℓ`. -/
alias prop_tube := NLQCLean.DirectVolume.exists_polynomial_tube_constant
alias prop_tube_explicit := NLQCLean.DirectVolume.polynomial_tube_haar_le

/-- `prop:overlap-derivative`, unitaries: local input and output generators and the
leakage bound `‖Ξ‖_F ≤ dδ (‖Ė‖_op + ‖Ḋ‖_op)`. -/
alias prop_overlap_derivative := NLQCLean.ReverseBlocks.IsValid.local_velocity_decomposition
/-- `prop:overlap-derivative`, measurements: local input generator, diagonal output
generator in `𝔲_diag`, and the same leakage bound. -/
alias prop_overlap_derivative_pvm := NLQCLean.PVMReverseBlocks.IsValid.local_velocity_decomposition

/-- `lem:normal-volume`, group volume: `Vol_F U(d²) ≥ (cd)^N ω_N` with `c = 1/256`,
`N = d⁴`, where `Vol_F` is the Euclidean Hausdorff measure `μHE[N]` in Frobenius coordinates. -/
alias lem_normal_volume_group := NLQCLean.unitaryFrobeniusVolume_ge
/-- `lem:normal-volume`, tube inequality:
`Vol_{2N}(U_t(S)) ≥ c^N ω_N t^N Vol_F U(d²) μ(S)` with `c = 1/1024`, `0 < t ≤ d/64`. -/
alias lem_normal_volume := NLQCLean.volume_unitaryFrobeniusTube_ge
/-- `lem:swap-cutoff`: on the near-SWAP polynomial witness source the normalized overlap
derivative is `T + R` with `rank T ≤ ℓ⋆`, `σ₁ ≤ 4√K/d` and `‖R‖ ≤ 32δ√K/d`. -/
alias lem_swap_cutoff := NLQCLean.SlimReverseBlocks.witnessFormat_sharp_rank_error
/-- `lem:bell-cutoff`: the same split for near-Bell witnesses, with `‖dT̂‖ ≤ 4√K` and
`‖R‖ ≤ 32δ√K` in Frobenius output coordinates (divide by `d` for the normalized norm). -/
alias lem_bell_cutoff := NLQCLean.PVMReverseBlocks.witnessFormat_nearBell_rank_error

end NLQCLean.Results.RobustPaper
