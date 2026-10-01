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
| Robust companion, Theorem D: diagonal gates (finite phase/LOSCC results) | `Unitary.exists_ae_finite_classical_controlled_phase_log_bound_of_external`, `Unitary.exists_ae_finite_loscc_controlled_phase_qubit_bound_of_external` | Geometry; full-circle fixed-phase threshold; initial-resource coefficient 1/5 when both quantum messages have dimension one |
| Rectangular diagonal restriction | `Unitary.finite_rectangular_diagonal_diamond_error_le`, `Unitary.finite_mixed_rectangular_diagonal_diamond_error_le` | Unconditional channel restriction and complete normalized diamond contraction; a phase-distribution theorem is a separate result |

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
The selected score is at least the original mixed score. Full shared
randomness and model-specific transfers remain open.

Near-Bell strong measurement precision B(ii), full standard-Borel/shared-
randomness C/D/localization, named exact C1, effective separation E, and the
exact paper's global finite-orbit structure remain open or partial. The checked
arithmetic polynomials and dimension-box coefficient
bounds do not prove rational quantifier elimination or transcendence.

For reproducibility, the complete production target is `NLQCLean.All` and
the maintained audit root is `NLQCTests`. The latter contains statement
checks, full type prints and axiom prints, including
[ResultInventory.lean](../NLQCTests/ResultInventory.lean) and
[QuantitativeResultTypes.lean](../NLQCTests/QuantitativeResultTypes.lean).
