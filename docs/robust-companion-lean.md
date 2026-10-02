# Lean coverage of the companion notes

This guide describes the formalization supplied in [Lean](../Lean/) alongside the [companion notes](../companion-notes.pdf). It uses **Lean and Mathlib v4.34.1**. The exact impossibility and finite-orbit results, the main robust resource bounds, and the diagonal-gate application have proofs without additional unproved mathematical hypotheses. The effective bound for the named controlled-phase gate in Appendix C retains two arithmetic inputs.

The [source-to-theorem map](../Lean/docs/PUBLIC_RESULTS.md) gives declaration names and links to their definitions. Start with [Results.Unitary](../Lean/NLQCLean/Results/Unitary.lean) and [Results.PVM](../Lean/NLQCLean/Results/PVM.lean), or import `NLQCLean` for the complete library. Statement names below refer to the PDF; the TeX source is not needed to use this guide.

## Coverage

| Paper statement | Formalized scope | Additional unproved inputs |
|---|---|---|
| Exact paper: almost-everywhere impossibility | Unitaries and ordered rank-one projective measurements, with arbitrary finite original registers | None |
| Exact paper: finite-orbit structure | Exact unitary and measurement targets for fixed architectures; compressed fixed-rank/message unitary families | None |
| Exact paper: algebraic invariants and the named controlled-phase example | Rational polynomial local-unitary invariants take algebraic values; exact exclusion for nonzero algebraic angles, identity spectators and local-unitary equivalents | None |
| Qualitative gaps, optimal scores and Schmidt-rank floors | Both unitary and measurement models | None |
| Theorem A: Haar volume and precision bounds | Full-group unitary and measurement bounds, universal and almost-every fixed-target consequences | None |
| Theorem B: universal approximation near SWAP and a maximally entangled basis | Both parts, their qubit forms, and regional almost-every consequences | None |
| Theorem C and the free-classical corollaries | Finite and standard-Borel classical outcomes, measurable shared randomness and branch-dependent finite systems; the improved universal dimension term is −2n/5 for both unitaries and measurements | None |
| Measurement localization | Standard Borel local outcomes, measurable reporting and finite shared density matrices | None |
| Diagonal gates | Rectangular local dimensions with independent uniform phases; charged, free-classical and shared-randomness versions; resource-qubit bounds; two-qubit Choi-infidelity version | None |
| Worst-case diagonal gates | A single hard gate per dimension, with the corresponding charged and free-classical bounds | None |
| Controlled-phase length bound | Charged and standard-Borel free-classical models | None |
| Appendix C: effective bound for the named controlled-phase gate | Charged and quantum-footprint iterated-log bounds | The two arithmetic propositions below |

## Models and quantifiers

The charged footprint is $K=r m_A m_B$: resource Schmidt rank (or the specified finite-mixture Schmidt-number bound) times both message dimensions. Private and garbage registers may have arbitrary finite dimensions. Mixed resources use common local protocol maps.

The free-classical model charges only the quantum footprint. Its results include standard Borel outcome spaces and measurable shared randomness with branch-dependent systems and almost-everywhere footprint caps. A score-preserving compression need not preserve the complete channel or its operational error; operational accuracy is transferred to the score first.

Unitary errors use normalized Choi infidelity, with diamond-error variants. Measurement errors use average joint-label failure, with worst-case joint total-variation variants. Formal measurement targets are basis matrices $M$, rather than the paper's $M^\dagger$; inversion invariance of Haar measure and outcome-phase invariance give the equivalent formulation.

Universal constants are chosen before the dimensions and budgets. Almost-everywhere error thresholds depend on the fixed target, before quantifying over budgets and protocols. Haar bounds use outer measure where measurability of reachable sets is not formalized.

## Geometry and constants

The polynomial image-volume estimate is proved directly using generic level perturbations, Sard's theorem, Lagrange multipliers, coordinate charts and an elementary isolated-zero count. It does not assume approximate definable choice, smooth stratification or a general component-count theorem.

The explicit formal image-volume base is **450240**, for sources in a ball of radius three, at most twenty polynomial constraints, and degree at most one hundred. See `NLQCLean.DirectVolume.polynomialImageVolumeBoundWith` in [Assembly.lean](../Lean/NLQCLean/Geometry/DirectVolume/Assembly.lean).

The written and formal compression bounds agree:

| Quantity | Bound |
|---|---|
| Distance after compression near SWAP | √(21ε/2), for ε≤1/16 |
| Distance after compression near a Bell basis | √(50ε/9), for ε≤1/256 |
| Total Bell environment rank | ⌈K/d⌉+d²≤4K/d |

The general written image-volume estimate keeps the degree and number of constraints explicit and uses the area formula directly. The formal proof uses a fixed format budget and coordinate-chart estimates. Formal verification of every constant in the general written formula is not claimed. The Bell derivative-cutoff lemma is not separately formalized; a different sufficient estimate proves the final results. Attainment is proved for optimal scores, not for minimal diamond or total-variation errors.

## Remaining arithmetic inputs

Only the effective bound in Appendix C takes the following unproved propositions as explicit arguments:

| Lean proposition | Content |
|---|---|
| `BasuPollackRoyExistentialElimination` | One-block real quantifier elimination with degree $d^{O(k)}$ and bit size $\tau d^{O(k)}$, for two free variables |
| `PolynomialTypeTranscendenceMeasureExpAngle` | A polynomial-type transcendence measure for $e^{i\theta}$, for nonzero real algebraic θ |

Their precise definitions and sources are in [EffectiveArithmetic.lean](../Lean/NLQCLean/External/EffectiveArithmetic.lean) and the [assumptions guide](../Lean/docs/ASSUMPTIONS.md). They are hypotheses, not additional kernel axioms. The formalization proves existence of the constants in the effective bound; their effective computability is not formalized.

The non-effective real quantifier-elimination theorem, rational coefficient preservation, and the Hermite–Lindemann theorem needed for exact exclusion are proved. Kernel audits use only Lean's standard logical axioms `propext`, `Classical.choice` and `Quot.sound`; full theorem types display any explicit premises.

## Building

From the `Lean` directory, with Elan installed on Linux:

```sh
lake exe cache get
lake build NLQCLean.All NLQCTests
```

Keep the supplied toolchain and dependency manifest. The [audit root](../Lean/NLQCTests.lean) checks statements and prints their axiom dependencies. The file-hash manifest in `Lean/PUBLIC_MANIFEST.json` describes the exported source files without including private repository history.

See also the [scope notes for the explanatory remarks and compression statements](../Lean/docs/PUBLIC_RESULTS.md#expository-scope-and-compression). The exact purity result now explicitly includes its rational orbit-invariant hypotheses.
