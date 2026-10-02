# Lean coverage of the companion notes

This guide describes the formalization supplied in [Lean](../Lean/) alongside the [companion notes](../companion-notes.pdf). It uses **Lean and Mathlib v4.34.1**. Every theorem, proposition, lemma and corollary of the companion notes has a Lean counterpart, in a few cases in an equivalent or slightly different form (listed below). Apart from Lean's standard axioms, the proofs use one unproved input, real quantifier elimination with degree and height bounds, and only for the effective bound for the named controlled-phase gate in Appendix C. A weaker, triple-exponential version of that bound is proved without it.

The [source-to-theorem map](../Lean/docs/PUBLIC_RESULTS.md) gives declaration names and links to their definitions. [Results.RobustPaper](../Lean/NLQCLean/Results/RobustPaper.lean) has one alias per labelled statement of the notes, named after its label (for example `thm_haar_fraction`, `cor_fixed_budget_stability`, `thm_explicit_one_sixth_power`). Start there, or with [Results.Unitary](../Lean/NLQCLean/Results/Unitary.lean) and [Results.PVM](../Lean/NLQCLean/Results/PVM.lean); import `NLQCLean` for the complete library. Statement names below refer to the PDF; the TeX source is not needed to use this guide.

## Coverage

| Paper statement | Formalized scope | Unproved inputs |
|---|---|---|
| Exact paper: almost-everywhere impossibility | Unitaries and ordered rank-one projective measurements, with arbitrary finite original registers | None |
| Exact paper: finite-orbit structure | Exact unitary and measurement targets for fixed architectures; compressed fixed-rank/message unitary families | None |
| Exact paper: algebraic invariants and the named controlled-phase example | Rational polynomial local-unitary invariants take algebraic values; exact exclusion for nonzero algebraic angles, identity spectators and local-unitary equivalents | None |
| Qualitative gaps, optimal scores and Schmidt-rank floors | Both unitary and measurement models | None |
| Fixed-budget stability (Corollary 2.3) | Unitary targets and PVMs (as basis unitaries): power-law distance to the exact set, and the exact set as a finite union of orbits; the semialgebraic Łojasiewicz inequality is proved | None |
| Frozen dilations, witness families, overlap derivative | Lemmas 3.1–3.2 and 4.1, Proposition 4.2 (unitaries and measurements), Proposition 5.1 | None |
| Image volume, tube estimate, normal volume | Lemma 5.3 and Proposition 5.4 for every polynomial format, and Lemma A.2 | None |
| Theorem A: Haar volume and precision bounds | Full-group unitary and measurement bounds, universal and almost-every fixed-target consequences | None |
| Theorem B: universal approximation near SWAP and a maximally entangled basis | Both parts, the compression and cutoff lemmas, their qubit forms, and regional almost-every consequences | None |
| Theorem C and the free-classical corollaries | Score compression to at most (dr')² outcomes per party and charged footprint d⁴Kq⁵; finite and standard-Borel classical outcomes, measurable shared randomness and branch-dependent finite systems; the improved universal dimension term is −2n/5 for both unitaries and measurements | None |
| Measurement localization | Standard Borel local outcomes, measurable reporting and finite shared density matrices | None |
| Diagonal gates | Rectangular local dimensions with independent uniform phases; charged, free-classical and shared-randomness versions; resource-qubit bounds; two-qubit Choi-infidelity version | None |
| Worst-case diagonal gates | A single hard gate per dimension, with the corresponding charged and free-classical bounds | None |
| Controlled-phase length bound | Charged and standard-Borel free-classical models | None |
| Appendix C, the gate C₁ at the stated rate | All conclusions of the theorem: ε ≥ exp(−exp(C K²)) for charged footprint K; ε ≥ exp(−exp(C R⁴ Kq²)) and ε ≥ exp(−exp(C Kq⁶)) with free classical messages; the ½, ⅙ and LOSCC ⅓ iterated-log forms. Free-classical versions cover finite and standard-Borel outcomes, pure and mixed resources and measurable shared randomness | Quantifier elimination only |
| Appendix C, the gate C₁ without any input | ε ≥ exp(−exp(exp(175 K²))), with protocol, free-classical and iterated-log forms | None |
| Appendix C, other nonzero algebraic angles | Charged-footprint bound at the stated double-exponential rate, with its iterated-log forms | Quantifier elimination only |

## Models and quantifiers

The charged footprint is $K=r m_A m_B$: resource Schmidt rank (or the specified finite-mixture Schmidt-number bound) times both message dimensions. Private and garbage registers may have arbitrary finite dimensions. Mixed resources use common local protocol maps.

The free-classical model charges only the quantum footprint. Its results include standard Borel outcome spaces and measurable shared randomness with branch-dependent systems and almost-everywhere footprint caps. A score-preserving compression need not preserve the complete channel or its operational error; operational accuracy is transferred to the score first.

Unitary errors use normalized Choi infidelity, with diamond-error variants. Measurement errors use average joint-label failure, with worst-case joint total-variation variants. Formal measurement targets are basis matrices $M$, rather than the paper's $M^\dagger$; inversion invariance of Haar measure and outcome-phase invariance give the equivalent formulation.

Universal constants are chosen before the dimensions and budgets. Almost-everywhere error thresholds depend on the fixed target, before quantifying over budgets and protocols. Haar bounds use outer measure where measurability of reachable sets is not formalized. The fixed-budget stability constants depend on the dimension and the budget, as in the paper.

## Geometry and constants

The polynomial image-volume estimate is proved directly using generic level perturbations, Sard's theorem, Lagrange multipliers, coordinate charts and an elementary isolated-zero count. It does not assume approximate definable choice, smooth stratification or a general component-count theorem. It holds for every polynomial format, with an explicit base depending only on the radius, the number of constraints and the degree.

For sources in a ball of radius three, at most twenty polynomial constraints and degree at most one hundred, which suffices for all applications, the direct proof gives base **450240** (`NLQCLean.DirectVolume.polynomialImageVolumeBoundWith` in [Assembly.lean](../Lean/NLQCLean/Geometry/DirectVolume/Assembly.lean)), and an independent barrier-function proof gives base **35248** (`NLQCLean.polynomialImageVolumeBoundWith_imageVolumeConstant` in [PolynomialImageVolume.lean](../Lean/NLQCLean/ImageVolume/PolynomialImageVolume.lean)). Downstream theorems only use the existence of a constant.

The written and formal compression bounds agree:

| Quantity | Bound |
|---|---|
| Distance after compression near SWAP | √(21ε/2), for ε≤1/16 |
| Distance after compression near a Bell basis | √(50ε/9), for ε≤1/256 |
| Total Bell environment rank | ⌈K/d⌉+d²≤4K/d |
| Free-classical outcomes per party after score compression | (dr')² |
| Charged footprint after coherent copying of the outcomes | d⁴Kq⁵ |
| Coordinates of the direct transcript parametrization for C₁ | at most 1090 r⁴q² |

Differences between the written and formal proofs:

- The singular-value hypotheses of the tube estimate (Proposition 5.4) are stated in the equivalent variational form: the derivative is the sum of a map of rank at most ℓ and a map of norm at most λ.
- The Bell derivative-cutoff lemma (Lemma 6.6) is proved, but the formal proof of Theorem 6.7 uses a cruder sufficient derivative estimate instead.
- The written general image-volume constant keeps the degree and constraint count explicit and uses the area formula directly. The formal proof uses coordinate charts; formal verification of every intermediate constant in the written formula is not claimed.
- Reachable-space compression is formalized in a stronger form that preserves the operational channel, rather than the dilation F. The free-classical score compression is packaged as a transfer into the charged class at d⁴Kq⁵.
- For C₁ the formal proof uses the transcendence measure of exponent 33 described below instead of Cijsouw's measure, so the intermediate gap estimate of Appendix C is formalized as g ≥ exp(−202 (6L+τ+128)³³) for a boundary polynomial of degree L and bit size τ. The final bounds have the stated form.
- Attainment is proved for optimal scores, not for minimal diamond or total-variation errors.

The three explanatory remarks (which error the proof uses, parameters against codimension, exceptional gates) have [scope notes](../Lean/docs/PUBLIC_RESULTS.md#expository-scope-and-compression); the cited exact protocols at rational multiples of π are not formalized.

## Arithmetic inputs

The effective bound of Appendix C was first proved from the following two propositions. The second is now proved, so quantifier elimination is the only remaining input:

| Lean proposition | Content | Status |
|---|---|---|
| `BasuPollackRoyExistentialElimination` | One-block real quantifier elimination with degree $d^{O(k)}$ and bit size $\tau d^{O(k)}$, for two free variables | Not proved; the only remaining input, used for the stated rate at every angle |
| `PolynomialTypeTranscendenceMeasureExpAngle` | A polynomial-type transcendence measure for $e^{i\theta}$, for nonzero real algebraic θ | Proved for every nonzero real algebraic θ by Gelfond's method: `polynomialTypeTranscendenceMeasureExpAngle` in [GelfondAngleMeasure.lean](../Lean/NLQCLean/Arithmetic/GelfondAngleMeasure.lean), exponent 50, and for θ = 1 (C₁) with exponent 33, `Gelfond.norm_eval_exp_I_ge` in [GelfondMeasure.lean](../Lean/NLQCLean/Arithmetic/GelfondMeasure.lean). The library also proves that Cijsouw's measure implies it |

The theorems for every nonzero algebraic angle with quantifier elimination only are in [ExplicitControlledPhaseAngle.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseAngle.lean). The C₁ theorems with quantifier elimination only are in [ExplicitControlledPhaseGelfond.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseGelfond.lean) (charged footprint), [ExplicitControlledPhaseTranscript.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseTranscript.lean) and [ExplicitControlledPhaseSharedRandom.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseSharedRandom.lean) (free classical messages). The input-free triple-exponential bound replaces quantifier elimination by iterated resultants on the Lagrange system of the least-deficit problem; it is `controlledPhase_one_protocol_bound_free_triple` in the same Gelfond file. Earlier, weaker variants based on a Hermite-type measure are kept in [ExplicitControlledPhaseQE.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseQE.lean) and [ExplicitControlledPhaseFree.lean](../Lean/NLQCLean/Bounds/ExplicitControlledPhaseFree.lean).

The precise definitions and sources of both propositions are in [EffectiveArithmetic.lean](../Lean/NLQCLean/External/EffectiveArithmetic.lean) and the [assumptions guide](../Lean/docs/ASSUMPTIONS.md). Quantifier elimination enters as an explicit hypothesis, not as an additional kernel axiom; the original theorems that take both propositions are kept. Apart from the explicit constant 175 of the input-free bound, the formalization proves existence of the constants in the effective bounds; their effective computability is not formalized.

The non-effective real quantifier-elimination theorem, semialgebraic projection closure, rational coefficient preservation, the semialgebraic Łojasiewicz inequality and the Hermite–Lindemann theorem needed for exact exclusion are proved. Kernel audits use only Lean's standard logical axioms `propext`, `Classical.choice` and `Quot.sound`; full theorem types display any explicit premises.

## Building

From the `Lean` directory, with Elan installed on Linux:

```sh
lake exe cache get
lake build NLQCLean.All NLQCTests
```

Keep the supplied toolchain and dependency manifest. The [audit root](../Lean/NLQCTests.lean) checks statements and prints their axiom dependencies. The file-hash manifest in `Lean/PUBLIC_MANIFEST.json` describes the exported source files without including private repository history.
