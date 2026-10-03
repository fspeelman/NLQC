# Mathematical assumptions

All results are unconditional, including the effective controlled-phase bound of Appendix C at
its stated rate `g_K(θ) ≥ exp(-exp(C_E K²))` for every nonzero real algebraic angle. This covers
the exact impossibility and finite-orbit results, compact score optima, qualitative gaps,
spectral floors, generic rank conclusions, and all quantitative Haar and precision estimates
(Theorems A–C, the diagonal-gate theorem and their corollaries in the robust companion). The
kernel audits show only the standard logical axioms `propext`, `Classical.choice` and
`Quot.sound`.

The effective bound once took two external propositions. Both are now discharged:

| Lean proposition | Mathematical content | Status |
|---|---|---|
| `BasuPollackRoyExistentialElimination` | One-block real quantifier elimination for two free variables with degree `d^{O(k)}` and bit size `τ d^{O(k)}` (Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed., Theorem 14.16) | **Not used; deleted from the Lean sources.** The only consequence needed, a nonzero integer polynomial `A(g, cos θ) = 0` of degree `12^{4(k+2)}` and bit size `τ 12^{4(k+2)}`, is proved directly: `Deformation.exists_eliminant_of_family` ([DeformationBounds.lean](../NLQCLean/Arithmetic/DeformationBounds.lean)) |
| `PolynomialTypeTranscendenceMeasureExpAngle` | A transcendence measure `exp(-C (N + log H)^c)` for `e^{iθ}`, `θ ≠ 0` real algebraic (the form cited in Appendix C) | **Proved**: `polynomialTypeTranscendenceMeasureExpAngle` (exponent `50`, Gelfond's method, [GelfondAngleMeasure.lean](../NLQCLean/Arithmetic/GelfondAngleMeasure.lean)); also implied by Cijsouw, Compositio Math. 28 (1974), Theorem 1 (`CijsouwTranscendenceMeasureExp.polynomialType`) |

The eliminant is proved by deformation. With `Q = Cst² + (y − Sc)²`, the function
`Q_λ = Σ z²⁶ − R₀ + λ Q` has, for large `λ`, a maximizer of `y` on its zero set that solves a
square pure-power critical system. The determinant trick (Cayley–Hamilton on the multiplication
matrix over the monomial basis) gives an eliminant of controlled size in `(y, λ, c, s)`; the
norm in `s`, the leading coefficient in `λ` and a compactness limit `λ → ∞` give `A(y, c)`.
The argument uses that feasible points have coordinates in `[−1, 1]`, which holds for unit
vectors, isometries and normalized Kraus families
([ControlledPhaseEliminant.lean](../NLQCLean/Bounds/ControlledPhaseEliminant.lean)).

Hence `exists_explicit_controlledPhaseLeastDeficit_lower_bound` and its protocol
and iterated-logarithm forms
([ExplicitControlledPhaseAngle.lean](../NLQCLean/Bounds/ExplicitControlledPhaseAngle.lean))
give `g_K(θ) ≥ exp(-exp(C_E K²))` for every nonzero real algebraic `θ` with no hypothesis. For
`C₁`, `exists_explicit_controlledPhase_one_lower_bound` gives the same rate,
and the free-classical refinements (`exp(-exp(C R⁴ Kq²))`, the `Kq⁶` form and the LOSCC qubit
count) are unconditional too. The theorems ending in `_of_transcendenceMeasure` derive the
bound from any polynomial-type transcendence measure, taken as an explicit argument. For `C₁`
the bound `exp(-exp(exp(175 K²)))` with an explicit constant (iterated resultants) is kept.

The precise propositions are in
[EffectiveArithmetic.lean](../NLQCLean/External/EffectiveArithmetic.lean).
Where a theorem takes one, it is an explicit hypothesis, not an axiom or a typeclass instance.

The quantitative estimates rest on the polynomial image-volume bound, proved
by `NLQCLean.DirectVolume.polynomialImageVolumeBound`
([Assembly.lean](../NLQCLean/Geometry/DirectVolume/Assembly.lean)) with an
explicit base 450240 for the fixed polynomial format used by the library, and independently by `NLQCLean.polynomialImageVolumeBound` ([ImageVolume](../NLQCLean/ImageVolume/PolynomialImageVolume.lean), barrier route) with base 35248. Semialgebraic projection closure is proved by
`NLQCLean.semialgebraicProjectionTheorem` in
[ProjectionTheorem.lean](../NLQCLean/Semialgebraic/ProjectionTheorem.lean),
using the vendored Sundog real quantifier-elimination development. The
almost-every exact-impossibility results use vector Sard.

The maintained audits print full theorem types as well as axioms, so explicit
hypotheses remain visible.

The universal bounds of Theorem B also have proved explicit constants, with no premise: K ≥ d² max(1−ε, √ln(1/ε)/51, √(ln(1/ε)−420)/46) for universal unitary approximation and K ≥ max(d³(1−ε)², d²√ln(1/ε)/36) for universal measurement approximation (`strongUniversal_explicit`, `pvmUniversal_explicit`). Other quantitative constants remain existential. The formal effective bound proves existence of its constants; their effective computability is not formalized. The source-to-theorem map describes other scope differences.
