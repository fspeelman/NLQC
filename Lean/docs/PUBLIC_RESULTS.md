# Source-to-theorem map

This table maps statements from the exact paper and robust companion to
the supplied Lean declarations. It records the formalized scope and
hypotheses; it does not claim complete coverage of either paper.

Import [Results.Unitary](../NLQCLean/Results/Unitary.lean) or
[Results.PVM](../NLQCLean/Results/PVM.lean). Names below are relative to
`NLQCLean.Results`. All results are unconditional except the effective controlled-phase bound in Appendix C at its stated rate (for `C₁` a weaker effective rate is unconditional); see
[Mathematical assumptions](ASSUMPTIONS.md).

| Source statement | Public declarations | Scope and hypotheses |
|---|---|---|
| Exact paper: orbit invariants take algebraic values | `Unitary.{pure,mixed}_orbit_invariant_algebraic`; direct polynomial variants `Unitary.{pure,mixed}_rational_orbit_invariant_algebraic` | Any positive logical dimension; rational polynomial presentation and orbit invariance only on unitary matrices; arbitrary finite original pure/common-map mixed registers |
| Exact paper: necessary condition for controlled-phase implementation | `Unitary.{pure,mixed}_first_qubit_phase_algebraic` | Every positive qubit count and any real angle; actual finite pure/common-map mixed exact implementation implies algebraic complex phase |
| Exact paper: named controlled-phase exact example | `Unitary.{pure,mixed}_first_qubit_one{,_local_orbit}_exact_exclusion`; algebraic-angle variants in [BitstringExactExclusion](../NLQCLean/Exact/BitstringExactExclusion.lean) | every positive qubit count, original first-bit source gate with identity spectators, full local-unitary orbits; arbitrary finite original pure/common-map mixed registers |
| Exact paper: controlled-phase purity formula | `Unitary.first_qubit_controlled_phase_purity` | Every positive qubit count, normalized purity `(3+cos θ)/4`; basis invariance and spectator factor checked |
| Exact paper: balanced almost-every exact impossibility | `{Unitary,PVM}.ae_no_finite_exact_implementation` | d≥2, arbitrary original finite registers, pure and common-map finite-mixed resources |
| Robust companion: qualitative divergence — attained score optima and fixed-target gaps | `{Unitary,PVM}.{exists_score_maximum_protocol,score_deficit_eq_zero_iff,exists_general_target_gap,ae_general_target_gap}` | attained compact charged score optimum at K≥1 and target-fixed gaps; no attained diamond/TV optimum claim |
| Robust companion: Schmidt-rank floors | `Unitary.{pure,mixed}_spectral_floor`, `PVM.{pure,mixed}_spectral_allocation`, `{Unitary,PVM}.{pure,mixed}_full_spectral_floor` | Unconditional spectral and target-dependent floors |
| SWAP and universal measurement floors | `Unitary.{pure,mixed}_swap_footprint_floor`; `PVM.{pure,mixed}_universal_cubic_floor` | Unconditional charged footprint floors; the measurement bound uses a generalized Bell basis in every positive local dimension |
| Robust companion, Theorem A: Haar volume and precision bounds | `{Unitary,PVM}.exists_full_group_score_haar_bound`, `Unitary.exists_full_group_resource_bound`, `PVM.exists_universal_resource_bound` | normalized Choi/PVM score, with operational variants; Haar outer measure where measurability is unavailable |
| Robust companion, Theorem B(i): universal unitary approximation and near-SWAP bounds | `Unitary.{exists_restricted_haar_bound,exists_universal_max_resource_bound,exists_universal_max_diamond_resource_bound}` | restricted near-SWAP Haar estimate and universal c d² max(1,√ln(1/ε)) lower bound for 0<ε≤1/2 |
| Theorem B(i), explicit constants | `Unitary.{universal_explicit_resource_bound,universal_explicit_resource_bound_of_eight}` and diamond forms; `Unitary.{universal_resource_bound_explicit,universal_qubit_bound_explicit,universal_qubit_bound_explicit_of_three,restricted_haar_bound_explicit,restricted_haar_split_bound}` in [StrongUniversalExplicit](../NLQCLean/Bounds/StrongUniversalExplicit.lean) | K ≥ d² max(1−ε, √ln(1/ε)/51, √(ln(1/ε)−420)/46) for d≥2 and max(1−ε, √ln(1/ε)/24, √(ln(1/ε)−92)/22) for d≥8; log₂K ≥ 2n+½log₂ln(1/ε)−6 (−5 for n≥3); restricted Haar constant 336 and split form exp((595/3)K²+(687/20)N)ε^(3N/32); pure/common-map mixed score and diamond, 0<ε≤1/2 |
| Robust companion: almost-every fixed-target precision bounds | `{Unitary,PVM}.{exists_ae_resource_bound,exists_ae_physical_resource_bound,exists_ae_qubit_bound}` | universal constant followed by a target-dependent threshold, then all budgets/errors |
| Regional near-SWAP almost-every precision | `Unitary.{exists_ae_swap_neighborhood_resource_bound,exists_ae_swap_neighborhood_physical_resource_bound}` | full Haar almost-every target with a near-SWAP implication; one target threshold before all budgets and arbitrary original registers; pure/common-map mixed score and diamond |
| Pure/common-map mixed standard-Borel compression | `{Unitary,PVM}.borel_{classical,mixed_classical}_score_reachable_transfer`, `Unitary.borel_{classical,mixed_classical}_diamond_reachable_transfer`, `PVM.borel_{classical,mixed_classical}_tv_reachable_transfer` | actual original Borel channel and rank-based quantum footprint enter the charged score class at d⁴Kq⁵ |
| Robust companion: floors with free classical communication (finite outcomes) | `{Unitary,PVM}.finite_{classical,mixed_classical}_score_spectral_bound`, `Unitary.finite_{classical,mixed_classical}_swap_quantum_footprint_floor`, `PVM.finite_{classical,mixed_classical}_bell_quantum_footprint_floor` | arbitrary original finite registers; unitary top-K and PVM max-column bounds; SWAP d²(1−ε) and Bell d(1−ε); original diamond/joint-TV variants and target-only full-size thresholds |
| Robust companion, Theorem C: free classical communication (finite-outcome rates) | `{Unitary,PVM}.exists_finite_classical_haar_bound`, `{Unitary,PVM}.exists_ae_arbitrary_finite_classical_log_bound` | actual finite instruments; score compression gives charged footprint≤d⁴Kq⁵; original operational error transfers through score |
| Finite universal precision | `{Unitary,PVM}.exists_finite_classical_universal_qubit_bound`, `Unitary.exists_finite_classical_strong_universal_qubit_bound` | quantum-footprint coefficient −3n/5 generally, −2n/5 for unitary universality |
| Robust companion: diagonal gates (finite phase/LOSCC results) | `Unitary.exists_ae_finite_classical_controlled_phase_log_bound`, `Unitary.exists_ae_finite_loscc_controlled_phase_qubit_bound` | full-circle fixed-phase threshold; initial-resource coefficient 1/5 when both quantum messages have dimension one |
| Rectangular diagonal restriction | `Unitary.finite_rectangular_diagonal_diamond_error_le`, `Unitary.finite_mixed_rectangular_diagonal_diamond_error_le` | Unconditional channel restriction and complete normalized diamond contraction; a phase-distribution theorem is a separate result |

Further checked declarations keep their defining namespaces under
`NLQCLean`. Import `NLQCLean.All` or the linked module directly.

| Source statement | Defining declarations | Scope and hypotheses |
|---|---|---|
| Exact paper: localizable measurements | `ClassicalCommunication.{ae_no_finite_exact_localization,finite_exact_localization_haar_null}` in [FiniteLocalization](../NLQCLean/Bounds/FiniteLocalization.lean) | actual finite local POVMs and joint reporting, every finite shared density matrix; d≥2 |
| Robust companion: finite localization | `ClassicalCommunication.{exists_finite_localization_haar_constant,exists_ae_finite_localization_rank_constant}` in [FiniteLocalization](../NLQCLean/Bounds/FiniteLocalization.lean) | finite outcomes; outer Haar and rank≥max(d,c d^(−3/5)ln(1/ε)^(1/10)); target threshold before all ranks and original systems |
| Robust companion: rectangular diagonal gates | `exists_ae_{charged,paid,finite}RectangularDiagonal_qubit_bound`, `exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound` in [RectangularDiagonalAlmostEvery](../NLQCLean/Bounds/RectangularDiagonalAlmostEvery.lean) | independent uniform phases, dA,dB≥2; charged coefficient 1/2, finite quantum coefficient 1/10 and initial-resource LOSCC coefficient 1/5; original diamond error and target-only threshold |
| Robust companion: floors with standard-Borel outcomes and shared randomness | Pure/mixed/random spectral lemmas and `ClassicalCommunication.ae_borel_classical_full_spectral_threshold` in [BorelClassicalSpectralFloors](../NLQCLean/Approx/BorelClassicalSpectralFloors.lean) | actual probability-average channels, branch-dependent systems and a.e. quantum caps; SWAP d² and Bell d floors |
| Robust companion: standard-Borel Haar, universal and fixed-target rates | `ClassicalCommunication.exists_borel_classical_{unitary,pvm}_haar_constant`, universal-log variants and `exists_ae_borel_classical_log_constant` in [BorelClassicalRates](../NLQCLean/Bounds/BorelClassicalRates.lean) | actual pure/common-map mixed Borel and measurable averaged channels; outer Haar and ln(1/ε)≤Cd⁶Kq¹⁰; Cd⁴Kq¹⁰ only for unitary universality |
| Hermite–Lindemann | `HermiteLindemann.transcendental_exp` in [the compatibility port](../NLQCLean/Vendor/HermiteLindemann/Basic.lean) | exp(a) transcendental over ℤ for nonzero algebraic complex a; pinned upstream proof and import closure |

The actual pure standard-Borel model has a derived CP/TP operational
channel and a same-resource finite realization preserving any real-linear
score. [BorelRankCompression.lean](../NLQCLean/Models/ClassicalCommunication/BorelRankCompression.lean)
composes that realization with rank-sized finite recompression: each final
alphabet is at most (d·SR(resource))² (score-nondecreasing pruning), and the charged footprint is at most
d⁴Kq⁵. Original diamond/joint-TV error implies the required score bound;
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

## Further covered statements

The declarations below are in `NLQCLean`, with the additional namespace shown where needed.

| Paper statement | Declaration or source | Scope |
|---|---|---|
| Exact finite-orbit structure for unitary targets | `exists_finset_exactTargets_eq_iUnion_orbits` in [FiniteOrbits](../NLQCLean/Exact/FiniteOrbits.lean); `exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits` in [CompressionFiniteOrbits](../NLQCLean/Exact/CompressionFiniteOrbits.lean) | Fixed architectures, and fixed resource Schmidt rank/message dimensions after compression |
| Exact finite-orbit structure for projective measurements | `exists_finset_pvmExactTargets_eq_iUnion_orbits` in [PVMFiniteOrbits](../NLQCLean/Exact/PVMFiniteOrbits.lean) | Local input unitaries and outcome phases; fixed finite architecture |
| Theorem B(ii): universal measurement precision near a Bell basis | `exists_nearBell_universal_max_constant`, `exists_nearBell_universal_qubit_constant` in [NearBellUniversal](../NLQCLean/Bounds/NearBellUniversal.lean) | Charged footprint and the 2n precision term; near-Bell Haar and regional almost-every bounds are also proved |
| Theorem B(ii), explicit constants | `PVM.{universal_explicit_resource_bound,universal_explicit_resource_bound_of_three,universal_max_resource_bound_explicit,universal_qubit_bound_explicit,universal_qubit_bound_explicit_of_two,near_bell_haar_bound_explicit}` in [NearBellUniversalExplicit](../NLQCLean/Bounds/NearBellUniversalExplicit.lean) | K ≥ max(d³(1−ε)², d²√ln(1/ε)/36) for d≥2 and /27 for d≥3; displayed form (1/36)max(d³, d²√ln(1/ε)); log₂K ≥ max(3n−2, 2n+½log₂ln(1/ε)−6), −5 for n≥2; score and joint TV, pure and common-map mixed |
| Universal measurement precision with free classical messages | `ClassicalCommunication.exists_borel_classical_strong_pvm_universal_qubit_constant` in [BorelClassicalStrongPVM](../NLQCLean/Bounds/BorelClassicalStrongPVM.lean) | The improved −2n/5 dimension term, including standard-Borel and shared-randomness protocols |
| Measurement localization with measurable outcomes and reporting | `ClassicalCommunication.exists_ae_borel_localization_rank_constant` in [BorelLocalization](../NLQCLean/Bounds/BorelLocalization.lean) | Standard Borel local outcomes and measurable reporting; finite shared density matrices |
| Diagonal gates with standard-Borel classical messages | `exists_ae_borelRectangularDiagonal_qubit_bound`, `exists_ae_borelLOSCCRectangularDiagonal_qubit_bound` in [BorelRectangularDiagonal](../NLQCLean/Bounds/BorelRectangularDiagonal.lean) | Rectangular local dimensions, uniform independent phases; normalized diamond error |
| Diagonal gates with measurable shared randomness | `exists_ae_sharedRandomRectangularDiagonal_log_bound`, `exists_ae_mixedSharedRandomRectangularDiagonal_log_bound` in [BorelSharedRandomRectangular](../NLQCLean/Bounds/BorelSharedRandomRectangular.lean) | Branch-dependent systems and almost-everywhere quantum-footprint caps |
| Worst-case diagonal gates | `exists_hard_chargedRectangularDiagonal_qubit_bound`, `exists_hard_borelLOSCCRectangularDiagonal_qubit_bound` in [RectangularDiagonalWorstCase](../NLQCLean/Bounds/RectangularDiagonalWorstCase.lean) | One hard gate per dimension; charged, finite and Borel free-classical variants |
| Appendix C: effective bound for the named controlled-phase gate | `exists_explicit_controlledPhaseLeastDeficit_lower_bound`, `exists_explicit_controlledPhase_protocol_bound`, `exists_explicit_controlledPhase_iterated_log_bound`, `exists_explicit_controlledPhase_quantum_iterated_log_bound` in [ExplicitControlledPhaseAngle](../NLQCLean/Bounds/ExplicitControlledPhaseAngle.lean) | Unconditional, every nonzero real algebraic angle: `g_K(θ) ≥ exp(-exp(C_E K²))`; the epigraph eliminant is proved by deformation (`Deformation.exists_eliminant_of_family`, [DeformationBounds](../NLQCLean/Arithmetic/DeformationBounds.lean)) and the polynomial-type transcendence measure is proved (`polynomialTypeTranscendenceMeasureExpAngle`, Gelfond's method, [GelfondAngleMeasure](../NLQCLean/Arithmetic/GelfondAngleMeasure.lean)); the forms in [ExplicitControlledPhase](../NLQCLean/Bounds/ExplicitControlledPhase.lean) take that measure as an argument; effective computability of constants is not formalized |
| Appendix C for `C₁` with free classical messages (`eq:explicit-quantum-tradeoff`) | `exists_explicit_controlledPhase_one_quantum_tradeoff`, `exists_explicit_controlledPhase_one_borel_quantum_tradeoff`, `exists_explicit_controlledPhase_one_sixth_power`, `exists_explicit_controlledPhase_one_sixth_log_bound`, `exists_explicit_controlledPhase_one_loscc_qubit_bound` in [ExplicitControlledPhaseTranscript](../NLQCLean/Bounds/ExplicitControlledPhaseTranscript.lean); `exists_explicit_controlledPhase_one_sharedRandom_quantum_tradeoff` in [ExplicitControlledPhaseSharedRandom](../NLQCLean/Bounds/ExplicitControlledPhaseSharedRandom.lean) | Unconditional; finite and standard-Borel protocols, pure and common-map mixed resources: `ε ≥ exp(-exp(C R⁴ Kq²))`, `ε ≥ exp(-exp(C Kq⁶))`, `log₂ Kq ≥ ⅙ log₂ ln ln(1/ε) - O(1)`, LOSCC qubits `≥ ⅓ log₂ ln ln(1/ε) - O(1)`; direct transcript parametrization with at most `1090 r⁴ q²` coordinates; also with measurable shared randomness under almost-everywhere Schmidt-number and footprint caps |
| Fixed-budget stability (`cor:fixed-budget-stability`, unitary and PVM targets) | `FixedBudget.exists_fixedBudget_stability`, `FixedBudget.exists_exactSet_eq_iUnion_orbits` in [FixedBudgetStability](../NLQCLean/Bounds/FixedBudgetStability.lean); `FixedBudget.exists_fixedBudget_stability_pvm`, `FixedBudget.exists_pvmExactSet_eq_iUnion_orbits` in [FixedBudgetStabilityPVM](../NLQCLean/Bounds/FixedBudgetStabilityPVM.lean) | Unconditional; `d ≥ 2`, `K ≥ 1`, nonempty exact set (PVMs as basis unitaries, orbits under local basis changes); constants depend on `d, K`; the semialgebraic Łojasiewicz inequality is proved (`lojasiewicz_inequality`) |
| Appendix C for `C₁` with explicit constant, triple exponential | `controlledPhase_one_triple_exp_bound`, `controlledPhase_one_protocol_triple_exp_bound`, `controlledPhase_one_triple_log_bound` in [ExplicitControlledPhaseGelfond](../NLQCLean/Bounds/ExplicitControlledPhaseGelfond.lean) | Unconditional: `g_K(1) ≥ exp(-exp(exp(175 K²)))`, by the proved polynomial-type measure for `e^i` (`Gelfond.norm_eval_exp_I_ge`, Gelfond's method) |
| Appendix C for `C₁` at the stated rate | `exists_explicit_controlledPhase_one_lower_bound`, `exists_explicit_controlledPhase_one_protocol_bound`, `exists_explicit_controlledPhase_one_iterated_log_bound` in [ExplicitControlledPhaseGelfond](../NLQCLean/Bounds/ExplicitControlledPhaseGelfond.lean) | Unconditional: the stated rate `exp(-exp(C K²))` |

## Constants and scope differences

The compression distances agree with the companion: √(21ε/2) near SWAP and √(50ε/9) near a Bell basis. The Bell total environment rank is at most ⌈K/d⌉+d². The image-volume theorem has explicit base 450240, proved by `DirectVolume.polynomialImageVolumeBoundWith` in [Assembly](../NLQCLean/Geometry/DirectVolume/Assembly.lean), and base 35248 for the fixed format, proved by `polynomialImageVolumeBoundWith_imageVolumeConstant` in [ImageVolume](../NLQCLean/ImageVolume/PolynomialImageVolume.lean).

The written geometric estimate retains a general degree/constraint budget and uses the area formula directly; the formal direct proof holds for every format budget, with base `max(4, R+1)(2Δ+1)c'`, and the applications use the budget of twenty constraints, degree one hundred and source radius three. Formal verification of every numerical constant in the general written estimate is not claimed. The Bell derivative-cutoff lemma is proved (`lem_bell_cutoff`), but the formal proof of the near-Bell Haar theorem uses a different sufficient derivative estimate. Attainment is proved for optimal scores, not for minimal diamond or total-variation error.

All bounds retain the physical-model assumptions in their statements. “Unconditional” here means that no additional unproved mathematical theorem is supplied as an argument.

For reproducibility, the complete production target is `NLQCLean.All` and
the maintained audit root is `NLQCTests`. The latter contains statement
checks, full type prints and axiom prints, including
[ResultInventory.lean](../NLQCTests/ResultInventory.lean) and
[QuantitativeResultTypes.lean](../NLQCTests/QuantitativeResultTypes.lean).

## Expository scope and compression

The following notes distinguish proved conclusions from explanations and cited constructions in the companion.

| Companion passage | Lean scope |
|---|---|
| Which error the proof uses | Operational diamond or joint-TV accuracy first implies a score bound. Selecting a pure resource component or compressing classical outcomes preserves or improves the target score; the selected channel need not preserve the original operational error. No such stronger claim is used. |
| Parameters against codimension | The witness coordinate bounds and transverse derivative estimates prove the displayed resource rates. The parameter-to-codimension comparison explains those proofs; no optimality theorem or matching upper bound is claimed. |
| Exceptional gates | Almost-everywhere thresholds depend on the target. Exact exclusion of the named controlled-phase gate is proved; its effective rate at the stated double-exponential shape is unconditional for every nonzero algebraic angle (the epigraph eliminant and the polynomial-type transcendence measure for `e^{iθ}` are proved). The cited construction of exact protocols at all rational multiples of pi, and hence their density, is not formalized here. |
| Reachable-space compression | `PureProtocol.exists_compressed_forward` preserves the operational channel and the relevant dimension bounds. This suffices for the paper's preserved-witness/score use; equality of the written dilation F is not asserted between differently represented registers. |
| Finite-support compression of the score | The Borel finite-outcome construction and charged reachability transfer establish the same target-score consequence at footprint d⁴Kq⁵, with pure rank selection and unchanged quantum-message dimensions. Shared-randomness transfers are also proved. The presentation packages intermediate choices differently; it does not claim preservation of the entire channel. |

See the declarations in the coverage tables above for the formal models. The exact purity result also explicitly supplies `purity_isRationalOrbitInvariant`, exported as `Results.ExactPaper.lem_purity_invariant`.
