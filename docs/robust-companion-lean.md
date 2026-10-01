# Lean coverage of the robust companion

This guide records the formalized statements of [Almost-perfect non-local quantum computation requires high-dimensional resources](../companion-notes.pdf), with their Lean declarations, hypotheses and limitations. It describes the sources supplied in [Lean](../Lean/), using Lean and Mathlib **v4.33.1**. It does not claim complete verification of the companion, including its arithmetic appendix.

The public entry points are [Results.Unitary](../Lean/NLQCLean/Results/Unitary.lean) and [Results.PVM](../Lean/NLQCLean/Results/PVM.lean). Names below are relative to `NLQCLean.Results`, except names beginning with `NLQCLean`. The notation `{Unitary,PVM}.name` means the two declarations `Unitary.name` and `PVM.name`; braces around several suffixes similarly abbreviate a list. Further pure/mixed, operational-error, and arbitrary-register variants are listed in the library's [source-to-theorem map](../Lean/docs/PUBLIC_RESULTS.md). Result names refer to the statements as presented in the companion PDF.

## Models and error conventions

The charged model allows private and garbage registers of arbitrary finite dimension, pure resources and finite mixtures of pure resources with Schmidt rank at most $r$, and footprint $K=r m_A m_B$, charging the full dimension of both messages. Mixed components use common local protocol maps. The free-classical model charges $K_{\mathrm q}=r m_A^{\mathrm q}m_B^{\mathrm q}$; its compression, floor and rate results allow standard Borel outcome spaces, including measurable shared randomness with branch-dependent finite systems and almost-everywhere quantum-footprint caps. The diagonal and localization results retain the more restricted scopes below.

Unitary targets are scored by normalized Choi overlap, and measurements by the average probability that both parties output the correct basis label. Many declarations also have normalized diamond-error and worst-case joint total-variation versions. For these operational errors, and with free classical communication, Haar estimates use outer measure because measurability of the reachable sets is not formalized. Score selection need not preserve the channel or its operational error; operational accuracy is transferred to the score before compression.

Measurement statements use basis matrices $M$ instead of $M^\dagger$. This is equivalent to the companion's convention by inversion invariance of Haar measure and invariance of reachability under $M\mapsto M\Delta$, for diagonal unitary $\Delta$. Constants are chosen before $d$, $K$ and $\epsilon$; almost-everywhere error thresholds depend on the target.

## External mathematical hypotheses

The Lean kernel accepts the proofs using only the standard logical axioms `propext`, `Classical.choice` and `Quot.sound`. Quantitative statements take the following three propositions as **explicit hypotheses**, not additional kernel axioms. “Geometry” in the tables below means all three.

| Hypothesis | Mathematical content | Source |
|---|---|---|
| `LRTTheorem44` | Quantitative approximate definable choice, with its constant chosen before dimensions and degree | Lerario–Rizzi–Tiberio, *Quantitative approximate definable choices*, arXiv:2409.14869v2, Theorem 44 |
| `SemialgebraicSmoothStratificationTheorem` | A finite compatible semialgebraic $C^1$ stratification into embedded pieces semialgebraically $C^1$-diffeomorphic to open cubes, satisfying the frontier condition | Coste, *An Introduction to Semialgebraic Geometry* (2002), Corollary 3.8; Bochnak–Coste–Roy, *Real Algebraic Geometry*, Section 9.1 |
| `SemialgebraicComponentBoundTheorem` | At most $\Delta(2\Delta-1)^{k+s-1}$ connected components for a set defined by $s$ polynomial equations and inequalities of degree at most $\Delta\ge2$ in $k$ real variables | Coste, Proposition 4.13 |

The propositions and supporting definitions are in [LRT44.lean](../Lean/NLQCLean/External/LRT44.lean) and [SemialgebraicTextbook.lean](../Lean/NLQCLean/External/SemialgebraicTextbook.lean). Their formulations were compared by hand with the cited sources. The kernel checks consequences of the propositions, not those published proofs. The Tarski–Seidenberg projection theorem is proved from real quantifier elimination in [ProjectionTheorem.lean](../Lean/NLQCLean/Semialgebraic/ProjectionTheorem.lean). See also the library's [assumptions guide](../Lean/docs/ASSUMPTIONS.md).

## Charged footprint results

| Companion statement | Lean declarations | Hypotheses |
|---|---|---|
| Attained optimal scores, exactness at zero score deficit, compact pure reachability, and fixed-target qualitative gaps | `{Unitary,PVM}.{exists_score_maximum_protocol,score_deficit_eq_zero_iff,isCompact_pure_reachable,exists_general_target_gap}` | None |
| Spectral allocation, exact Schmidt-rank floors, and floors for SWAP, every basis and maximally entangled bases | `Unitary.pure_spectral_floor`; `PVM.pure_spectral_allocation`; `{Unitary,PVM}.pure_exact_schmidt_rank_floor`; `Unitary.pure_swap_footprint_floor`; `PVM.pure_footprint_floor`; `NLQCLean.PureProtocol.maximallyEntangledPVM_footprint_floor` | None |
| Full spectral floors and almost-every target-dependent thresholds | `{Unitary,PVM}.{pure_full_spectral_floor,ae_full_spectral_footprint_threshold}` | None |
| Whole-group Haar-volume bound | `{Unitary,PVM}.exists_full_group_score_haar_bound` | Geometry |
| Common universal precision bound and qubit form | `Unitary.{exists_full_group_resource_bound,exists_full_group_qubit_bound}`; `PVM.{exists_universal_resource_bound,exists_universal_qubit_bound}` | Geometry |
| Almost-every fixed-target precision bound and qubit form | `{Unitary,PVM}.{exists_ae_resource_bound,exists_ae_qubit_bound}` | Geometry |
| Haar mass of the near-SWAP ball, with $e^{-5N}$ in place of $9^{-2N}$ | `NLQCLean.strongSwapPatchMassBound_five` | None |
| Regional Haar bound near SWAP | `Unitary.exists_restricted_haar_bound` | Geometry |
| Stronger universal unitary bound, including its maximum with the rank floor, and its qubit form | `Unitary.{exists_universal_resource_bound,exists_universal_max_resource_bound_of_external,exists_universal_qubit_bound}` | Geometry |
| Universal measurement floor $K\ge d^3(1-\epsilon)^2\ge d^3/4$, hence $\log_2K\ge3n-2$ | `PVM.{pure_universal_cubic_floor,pure_universal_quarter_floor,pure_universal_qubit_floor}` | None |
| Almost-every precision bound within the near-SWAP neighborhood | `Unitary.exists_ae_swap_neighborhood_resource_bound_of_external` | Geometry |

The common universal unitary declaration assumes $K\ge1$, which every protocol satisfies. The almost-everywhere score statement also appears as forbidden errors $\epsilon_K(T)>\exp(-AK^2/d^2)$ for all $K\ge K_0(T)$, in `{Unitary,PVM}.exists_ae_forbidden_error_threshold`.

## Free classical communication

| Companion statement | Lean declarations | Hypotheses |
|---|---|---|
| Standard-Borel transcript compression, as inclusion of score-reachable sets in the charged class at $\overline K=4d^4K_{\mathrm q}^5$ | `{Unitary,PVM}.{borel_classical_score_reachable_transfer,borel_mixed_classical_score_reachable_transfer}` | None |
| Finite-alphabet spectral floors, including SWAP $d^2(1-\epsilon)$, Bell basis $d(1-\epsilon)$, and almost-every full-size floors | `{Unitary,PVM}.finite_classical_score_spectral_bound`; `Unitary.finite_classical_swap_quantum_footprint_floor`; `PVM.finite_classical_bell_quantum_footprint_floor`; `{Unitary,PVM}.{finite_classical_full_spectral_floor,ae_finite_classical_full_spectral_threshold}` | None |
| Finite-alphabet Haar-volume bounds | `{Unitary,PVM}.exists_finite_classical_haar_bound_of_external` | Geometry |
| Finite-alphabet universal unitary precision bound | `Unitary.{exists_finite_classical_strong_universal_log_bound_of_external,exists_finite_classical_strong_universal_qubit_bound_of_external}` | Geometry |
| Finite-alphabet universal measurement precision bound, with $d^{-3/5}$ rather than the companion's $d^{-2/5}$, or $-3n/5$ rather than $-2n/5$ in logarithmic form | `PVM.{exists_finite_classical_universal_log_bound_of_external,exists_finite_classical_universal_qubit_bound_of_external}` | Geometry |
| Finite-alphabet almost-every precision bounds | `{Unitary,PVM}.exists_ae_arbitrary_finite_classical_log_bound_of_external` | Geometry |

The actual standard-Borel channel is defined by a Bochner integral. The formal proof first realizes its score with finitely many outcomes and the same resource, then reduces each alphabet to at most $(dr')^2+1$, where $r'$ is the resource rank. The pure and common-map finite-mixed constructions are in [BorelRankCompression.lean](../Lean/NLQCLean/Models/ClassicalCommunication/BorelRankCompression.lean) and [BorelMixedCompression.lean](../Lean/NLQCLean/Models/ClassicalCommunication/BorelMixedCompression.lean). Complete positivity and trace preservation of the original channels are proved. The selected pure component has score at least the mixed score under the branchwise resource and message cap.

The standard-Borel and shared-randomness extensions are now proved for actual averaged channels. [BorelSharedRandomness](../Lean/NLQCLean/Models/ClassicalCommunication/BorelSharedRandomness.lean) establishes integrability, complete positivity, trace preservation and exact mean scores; selection preserves almost-everywhere resource/message caps.

| Companion statement | Defining declarations under `NLQCLean.ClassicalCommunication` | Hypotheses |
|---|---|---|
| Standard-Borel and shared-randomness spectral floors, including SWAP and Bell targets and almost-every full-size thresholds | Pure/mixed/random spectral lemmas and `ae_borel_classical_full_spectral_threshold` in [BorelClassicalSpectralFloors](../Lean/NLQCLean/Approx/BorelClassicalSpectralFloors.lean) | None |
| Standard-Borel and shared-randomness Haar, universal and almost-every fixed-target rates | `exists_borel_classical_{unitary,pvm}_haar_constant_of_external`, universal-log variants and `exists_ae_borel_classical_log_constant_of_external` in [BorelClassicalRates](../Lean/NLQCLean/Bounds/BorelClassicalRates.lean) | Geometry; the improved universal PVM coefficient is still open |
| Finite-outcome localization: Haar and almost-every rank bounds | `exists_finite_localization_haar_constant_of_external`, `exists_ae_finite_localization_rank_constant_of_external` in [FiniteLocalization](../Lean/NLQCLean/Bounds/FiniteLocalization.lean) | Geometry; finite local outcomes and arbitrary finite shared density matrices |

## Controlled phases and diagonal gates

| Companion statement | Lean declarations | Hypotheses |
|---|---|---|
| Controlled-phase length bounds, charged and with finite classical alphabets | `Unitary.{exists_charged_controlled_phase_length_bound_of_external,exists_finite_classical_controlled_phase_length_bound_of_external}` | Geometry |
| Almost-every controlled phase: charged footprint bound with Choi infidelity | `Unitary.exists_ae_charged_controlled_phase_resource_bound_of_external` | Geometry |
| Almost-every controlled phase: quantum-footprint bound with finite classical alphabets | `Unitary.exists_ae_finite_classical_controlled_phase_log_bound_of_external` | Geometry |
| Almost-every controlled phase: resource-qubit bound with classical messages only and without shared randomness | `Unitary.exists_ae_finite_loscc_controlled_phase_qubit_bound_of_external` | Geometry |
| Worst case over controlled phases with finite classical alphabets | `Unitary.exists_finite_classical_controlled_phase_worst_case_bound_of_external` | Geometry |
| Restriction of a rectangular diagonal gate to two levels per party, preserving quantum footprint and not increasing normalized diamond error | `Unitary.{finite_rectangular_diagonal_diamond_error_le,finite_mixed_rectangular_diagonal_diamond_error_le}` | None |

The restriction and phase-distribution arguments are now combined in [RectangularDiagonalAlmostEvery](../Lean/NLQCLean/Bounds/RectangularDiagonalAlmostEvery.lean). The declarations `NLQCLean.exists_ae_{charged,paid,finite}RectangularDiagonal_qubit_bound_of_external` and `NLQCLean.exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound_of_external` prove almost-every bounds for independent uniform phases in local dimensions at least two. They retain Geometry, use the original normalized diamond error and one target-dependent threshold, and cover charged protocols, finite classical alphabets and finite LOSCC. The logarithmic precision coefficients are respectively 1/2, 1/10 and 1/5 for charged footprint, quantum footprint and initial LOSCC resource qubits. These statements do not yet supply standard-Borel or shared-randomness diagonal coverage.

## Exact-paper results

The following results are unconditional: they do not use Geometry.

| Exact-paper statement | Lean declarations |
|---|---|
| Almost-every finite exact impossibility for unitary and measurement targets | `{Unitary,PVM}.ae_no_finite_exact_implementation` |
| Almost-every impossibility of finite exact localization | `NLQCLean.ClassicalCommunication.ae_no_finite_exact_localization` in [FiniteLocalization](../Lean/NLQCLean/Bounds/FiniteLocalization.lean) |
| Exact first-qubit controlled phase implies an algebraic complex phase, at every real angle | `Unitary.{pure,mixed}_first_qubit_phase_algebraic` |
| Named angle-one exact exclusion and all local-unitary equivalents | `Unitary.{pure,mixed}_first_qubit_one{,_local_orbit}_exact_exclusion` |
| Every nonzero algebraic angle is excluded | Algebraic-angle variants in [BitstringExactExclusion](../Lean/NLQCLean/Exact/BitstringExactExclusion.lean) |
| Normalized first-qubit controlled-phase purity | `Unitary.first_qubit_controlled_phase_purity` |
| Rational polynomial local-unitary invariants take algebraic values | `Unitary.{pure,mixed}_orbit_invariant_algebraic` |

The first-qubit results use the actual bitstring gate, every positive qubit count and identity spectators. The exact protocol statements allow arbitrary finite original registers and pure/common-map finite-mixed resources. The invariant lemma requires rational polynomiality and local-orbit invariance only on unitary matrices. Its proof combines the exact local differential, scalar Sard, rational projection and rational semialgebraic null-set algebraicity, architecture by architecture. This proves the paper's statement without proving its general finite-orbit structure theorem. The checked Hermite–Lindemann theorem supplies the transcendence contradiction for the explicit gate. Exact exclusion does not prove the companion's effective arithmetic separation bound.

## Differences from the written proofs

The formalization proves the listed statements with some different intermediate constructions and constants:

1. It extends the overlap map off the constraint set using explicit cubic polynomial maps with the required linearized derivatives, rather than the companion's polar retraction. The image-volume lemma is formalized for polynomial maps of degree at most $100$, on compact subsets of a radius-$3$ ball defined by at most $20$ polynomial conditions of degree at most $100$. This specialized form suffices for the witness families.
2. It replaces the area formula on strata by an image-volume inequality for coordinate graphs. It proves convergence of volumes under Hausdorff limits of sets of bounded format instead of using the stronger continuity estimate cited in the companion; convergence is sufficient.
3. It proves the normal-volume estimate using elementary nets, caps and a Cayley chart instead of Gaussian estimates. The near-SWAP proof uses an operator-norm form up to $t\le d/64$; the whole-group proof uses a simpler version at Frobenius radius at most $1/2$.
4. Its witness families have $32d^2K^2$ real coordinates for unitaries and $1024d^2K^2$ for measurements. Near SWAP, the dilation error is at most $\sqrt{18\epsilon}$ rather than $4\sqrt\epsilon$, and the ball mass is at least $e^{-5N}$ rather than $9^{-2N}$.
5. Standard-Borel compression proceeds through the actual channel's Bochner integral and a same-resource finite score realization before the rank-sized alphabet reduction described above.

The library also proves almost-every exact impossibility for both models without the three geometry hypotheses, using Sard's theorem rather than finiteness of connected components: `{Unitary,PVM}.ae_no_finite_exact_implementation`. It contains versions of the protocol Schmidt-rank bound, approximate frozen dilation, reachable-space compression, perturbed derivative identity, witness singular-value estimates, near-SWAP compression and spectral cutoff, and normal-volume estimate. The companion's comparison concerns the public statements above rather than a line-by-line identification of these internal lemmas.

## Exclusions and reproduction

The following are outside the coverage claim in the supplied sources:

- The near-Bell measurement argument and its stronger $d^2\sqrt{\ln(1/\epsilon)}$ precision term, including the regional almost-every measurement bound. The universal $d^3$ floor is formalized.
- The improved universal measurement coefficient with free classical communication, and standard-Borel/measurable-postprocessing and shared-randomness extensions of localization. The general Borel/shared-randomness floors and rates, and finite-outcome localization, are formalized.
- The full standard-Borel/shared-randomness diagonal theorem, shared randomness in its resource-qubit bound, and the charged-footprint worst-case diagonal statement. Almost-every rectangular diagonal rates have the finite scope listed above.
- The exact paper's general finite-orbit structure theorem.
- Attainment of minimal diamond or total-variation error. Attainment is proved for optimal scores.
- The image-volume and tube lemmas in their full written generality; only the specialized forms above are formalized.
- The explicit arithmetic separation bound for $C_1$ and its proof in Appendix C of the companion.

The [Lean README](../Lean/README.md) gives build instructions with the pinned dependencies. The production target is `NLQCLean.All`; the maintained audit root is `NLQCTests`. Audits include full statement and axiom prints in [ResultInventory.lean](../Lean/NLQCTests/ResultInventory.lean) and [QuantitativeResultTypes.lean](../Lean/NLQCTests/QuantitativeResultTypes.lean), so the external hypotheses remain visible as well as the standard logical axioms.
