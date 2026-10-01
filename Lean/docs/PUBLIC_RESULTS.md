# Source-to-theorem map

This table maps statements from the exact paper and robust companion to
the supplied Lean declarations. It records the formalized scope and
hypotheses; it does not claim complete coverage of either paper.

Import [Results.Unitary](../NLQCLean/Results/Unitary.lean) or
[Results.PVM](../NLQCLean/Results/PVM.lean). Names below are relative to
`NLQCLean.Results`. “Geometry” means exactly the three propositions in
[Mathematical assumptions](ASSUMPTIONS.md).

| Source statement | Public declarations | Scope and hypotheses |
|---|---|---|
| Exact paper: orbit invariants take algebraic values | `Unitary.{pure,mixed}_orbit_invariant_algebraic`; direct polynomial variants `Unitary.{pure,mixed}_rational_orbit_invariant_algebraic` | Any positive logical dimension; rational polynomial presentation and orbit invariance only on unitary matrices; arbitrary finite original pure/common-map mixed registers; no extra geometry premise |
| Exact paper: controlled-phase gate, necessary condition | `Unitary.{pure,mixed}_first_qubit_phase_algebraic` | Every positive qubit count and any real angle; actual finite pure/common-map mixed exact implementation implies algebraic complex phase |
| Exact paper: named controlled-phase exact example | `Unitary.{pure,mixed}_first_qubit_one{,_local_orbit}_exact_exclusion`; algebraic-angle variants in [BitstringExactExclusion](../NLQCLean/Exact/BitstringExactExclusion.lean) | Unconditional; every positive qubit count, original first-bit source gate with identity spectators, full local-unitary orbits; arbitrary finite original pure/common-map mixed registers |
| Exact paper: operator purity, first-qubit formula | `Unitary.first_qubit_controlled_phase_purity` | Every positive qubit count, normalized purity `(3+cos θ)/4`; basis invariance and spectator factor checked |
| Exact paper: balanced almost-every exact impossibility | `{Unitary,PVM}.ae_no_finite_exact_implementation` | Unconditional; d≥2, arbitrary original finite registers, pure and common-map finite-mixed resources |
| Robust companion: qualitative divergence — attained score optima and fixed-target gaps | `{Unitary,PVM}.{exists_score_maximum_protocol,score_deficit_eq_zero_iff,exists_general_target_gap,ae_general_target_gap}` | Unconditional; attained compact charged score optimum at K≥1 and target-fixed gaps; no attained diamond/TV optimum claim |
| Robust companion: Schmidt-rank floors | `Unitary.{pure,mixed}_spectral_floor`, `PVM.{pure,mixed}_spectral_allocation`, `{Unitary,PVM}.{pure,mixed}_full_spectral_floor` | Unconditional spectral and target-dependent floors |
| SWAP and universal measurement floors | `Unitary.{pure,mixed}_swap_footprint_floor`; `PVM.{pure,mixed}_universal_cubic_floor` | Unconditional charged footprint floors; the measurement bound uses a generalized Bell basis in every positive local dimension |
| Robust companion, Theorem A: Haar volume and precision bounds | `{Unitary,PVM}.exists_full_group_score_haar_bound`, `Unitary.exists_full_group_resource_bound`, `PVM.exists_universal_resource_bound` | Geometry; normalized Choi/PVM score, with operational variants; Haar outer measure where measurability is unavailable |
| Robust companion, Theorem B(i): universal unitary approximation and near-SWAP bounds | `Unitary.{exists_restricted_haar_bound,exists_universal_max_resource_bound_of_external,exists_universal_max_diamond_resource_bound_of_external}` | Geometry; restricted near-SWAP Haar estimate and universal c d² max(1,√ln(1/ε)) lower bound for 0<ε≤1/2 |
| Robust companion: almost-every fixed-target precision bounds | `{Unitary,PVM}.{exists_ae_resource_bound,exists_ae_physical_resource_bound,exists_ae_qubit_bound}` | Geometry; universal constant followed by a target-dependent threshold, then all budgets/errors |
| Regional near-SWAP almost-every precision | `Unitary.{exists_ae_swap_neighborhood_resource_bound_of_external,exists_ae_swap_neighborhood_physical_resource_bound_of_external}` | Geometry; full Haar almost-every target with a near-SWAP implication; one target threshold before all budgets and arbitrary original registers; pure/common-map mixed score and diamond |
| Pure/common-map mixed standard-Borel compression | `{Unitary,PVM}.borel_{classical,mixed_classical}_score_reachable_transfer`, `Unitary.borel_{classical,mixed_classical}_diamond_reachable_transfer`, `PVM.borel_{classical,mixed_classical}_tv_reachable_transfer` | Unconditional; actual original Borel channel and rank-based quantum footprint enter the charged score class at 4d⁴Kq⁵ |
| Robust companion: floors with free classical communication (finite outcomes) | `{Unitary,PVM}.finite_{classical,mixed_classical}_score_spectral_bound`, `Unitary.finite_{classical,mixed_classical}_swap_quantum_footprint_floor`, `PVM.finite_{classical,mixed_classical}_bell_quantum_footprint_floor` | Unconditional; arbitrary original finite registers; unitary top-K and PVM max-column bounds; SWAP d²(1−ε) and Bell d(1−ε); original diamond/joint-TV variants and target-only full-size thresholds |
| Robust companion, Theorem C: free classical communication (finite-outcome rates) | `{Unitary,PVM}.exists_finite_classical_haar_bound_of_external`, `{Unitary,PVM}.exists_ae_arbitrary_finite_classical_log_bound_of_external` | Geometry; actual finite instruments; score compression gives charged footprint≤4d⁴Kq⁵; original operational error transfers through score |
| Finite universal precision | `{Unitary,PVM}.exists_finite_classical_universal_qubit_bound_of_external`, `Unitary.exists_finite_classical_strong_universal_qubit_bound_of_external` | Geometry; quantum-footprint coefficient −3n/5 generally, −2n/5 for unitary universality |
| Robust companion: diagonal gates (finite phase/LOSCC results) | `Unitary.exists_ae_finite_classical_controlled_phase_log_bound_of_external`, `Unitary.exists_ae_finite_loscc_controlled_phase_qubit_bound_of_external` | Geometry; full-circle fixed-phase threshold; initial-resource coefficient 1/5 when both quantum messages have dimension one |
| Rectangular diagonal restriction | `Unitary.finite_rectangular_diagonal_diamond_error_le`, `Unitary.finite_mixed_rectangular_diagonal_diamond_error_le` | Unconditional channel restriction and complete normalized diamond contraction; a phase-distribution theorem is a separate result |

Further checked declarations keep their defining namespaces under
`NLQCLean`. Import `NLQCLean.All` or the linked module directly.

| Source statement | Defining declarations | Scope and hypotheses |
|---|---|---|
| Exact paper: localizable measurements | `ClassicalCommunication.{ae_no_finite_exact_localization,finite_exact_localization_haar_null}` in [FiniteLocalization](../NLQCLean/Bounds/FiniteLocalization.lean) | Unconditional; actual finite local POVMs and joint reporting, every finite shared density matrix; d≥2 |
| Robust companion: finite localization | `ClassicalCommunication.{exists_finite_localization_haar_constant_of_external,exists_ae_finite_localization_rank_constant_of_external}` in [FiniteLocalization](../NLQCLean/Bounds/FiniteLocalization.lean) | Geometry; finite outcomes; outer Haar and rank≥max(d,c d^(−3/5)ln(1/ε)^(1/10)); target threshold before all ranks and original systems |
| Robust companion: rectangular diagonal gates | `exists_ae_{charged,paid,finite}RectangularDiagonal_qubit_bound_of_external`, `exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound_of_external` in [RectangularDiagonalAlmostEvery](../NLQCLean/Bounds/RectangularDiagonalAlmostEvery.lean) | Geometry; independent uniform phases, dA,dB≥2; charged coefficient 1/2, finite quantum coefficient 1/10 and initial-resource LOSCC coefficient 1/5; original diamond error and target-only threshold |
| Robust companion: floors with standard-Borel outcomes and shared randomness | Pure/mixed/random spectral lemmas and `ClassicalCommunication.ae_borel_classical_full_spectral_threshold` in [BorelClassicalSpectralFloors](../NLQCLean/Approx/BorelClassicalSpectralFloors.lean) | Unconditional; actual probability-average channels, branch-dependent systems and a.e. quantum caps; SWAP d² and Bell d floors |
| Robust companion: standard-Borel Haar, universal and fixed-target rates | `ClassicalCommunication.exists_borel_classical_{unitary,pvm}_haar_constant_of_external`, universal-log variants and `exists_ae_borel_classical_log_constant_of_external` in [BorelClassicalRates](../NLQCLean/Bounds/BorelClassicalRates.lean) | Geometry; actual pure/common-map mixed Borel and measurable averaged channels; outer Haar and ln(1/ε)≤Cd⁶Kq¹⁰; Cd⁴Kq¹⁰ only for unitary universality |
| Hermite–Lindemann | `HermiteLindemann.transcendental_exp` in [the compatibility port](../NLQCLean/Vendor/HermiteLindemann/Basic.lean) | Unconditional; exp(a) transcendental over ℤ for nonzero algebraic complex a; pinned upstream proof and import closure |

The actual pure standard-Borel model has a derived CP/TP operational
channel and a same-resource finite realization preserving any real-linear
score. [BorelRankCompression.lean](../NLQCLean/Models/ClassicalCommunication/BorelRankCompression.lean)
composes that realization with rank-sized finite recompression: each final
alphabet is at most (d·SR(resource))²+1, and the charged footprint is at most
4d⁴Kq⁵. Original diamond/joint-TV error implies the required score bound;
score selection does not preserve that channel or operational error.
[BorelMixedCompression.lean](../NLQCLean/Models/ClassicalCommunication/BorelMixedCompression.lean)
proves the actual common-map finite-mixed channel, its CP/TP normalization,
and component selection under the branchwise Schmidt-number/message cap.
The selected score is at least the original mixed score.
[BorelSharedRandomness.lean](../NLQCLean/Models/ClassicalCommunication/BorelSharedRandomness.lean)
derives integrability, CP/TP and exact mean scores for actual channel averages
under arbitrary probability randomness and branch-dependent systems. Selection
retains a.e. rank/message caps; original diamond/joint-TV error enters through
score before selection. Finite-register relabeling also preserves actual
pure/common-map mixed channels and their caps.

Near-Bell strong measurement precision B(ii), the improved universal PVM
coefficient −2n/5, Borel rectangular restriction and measurable localization
postprocessing, effective arithmetic separation, and global finite-orbit
structure remain open. The near-Bell reference contraction and Alice-message
upper estimate are checked ingredients. Checked Hermite–Lindemann, rational
coefficient-preserving projection and actual architecture purity algebraicity
now prove the named controlled-phase exact exclusion with all identity spectators.
The general orbit-invariant algebraicity statement is also checked, using the exact local
differential, scalar Sard and the rational polynomial image for each architecture.

For reproducibility, the complete production target is `NLQCLean.All` and
the maintained audit root is `NLQCTests`. The latter contains statement
checks, full type prints and axiom prints, including
[ResultInventory.lean](../NLQCTests/ResultInventory.lean) and
[QuantitativeResultTypes.lean](../NLQCTests/QuantitativeResultTypes.lean).
