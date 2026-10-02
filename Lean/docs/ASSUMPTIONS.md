# Mathematical assumptions

All results are unconditional except the effective controlled-phase bound
in Appendix C at its stated rate, which needs quantifier elimination only (for `C₁` a weaker
effective bound is unconditional). This covers the exact impossibility and finite-orbit results,
compact score optima, qualitative gaps, spectral floors, generic rank
conclusions, and all quantitative Haar and precision estimates (Theorems A–C, the diagonal-gate theorem and their corollaries in
the robust companion). The kernel audits show only the
standard logical axioms `propext`, `Classical.choice` and `Quot.sound`.

The effective bound takes one explicit proposition argument, quantifier elimination. The
transcendence measure that the conditional theorems also take as an argument is proved:

| Lean proposition | Mathematical content | Source |
|---|---|---|
| `BasuPollackRoyExistentialElimination` | One-block real quantifier elimination for two free variables with degree `d^{O(k)}` and bit size `τ d^{O(k)}` | Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed., Theorem 14.16 |
| `PolynomialTypeTranscendenceMeasureExpAngle` | A transcendence measure `exp(-C (N + log H)^c)` for `e^{iθ}`, `θ ≠ 0` real algebraic (the form cited in Appendix C) | **Proved**: `polynomialTypeTranscendenceMeasureExpAngle` (exponent `50`, Gelfond's method, [GelfondAngleMeasure.lean](../NLQCLean/Arithmetic/GelfondAngleMeasure.lean)); also implied by Cijsouw, Compositio Math. 28 (1974), Theorem 1 (`CijsouwTranscendenceMeasureExp.polynomialType`) |

Hence `exists_explicit_controlledPhaseLeastDeficit_lower_bound_of_QE` and its protocol and
iterated-logarithm forms (`..._of_QE` in
[ExplicitControlledPhaseAngle.lean](../NLQCLean/Bounds/ExplicitControlledPhaseAngle.lean))
give `g_K(θ) ≥ exp(-exp(C_E K²))` for every nonzero real algebraic `θ` with
`BasuPollackRoyExistentialElimination` only. The proof of the measure runs Gelfond's method
over `ℤ[i][aθ]` (`aθ` a root of a monic integer polynomial); the Liouville step uses the
characteristic polynomial of multiplication by `Σ_e (aθ)^e Q_e(β₀)`
(`Gelfond.eq_zero_of_norm_small_angle`).

For the named gate `C₁` (angle `1`) a sharper weak transcendence input was proved first: a
polynomial-type measure for `e^i`, `Gelfond.norm_eval_exp_I_ge`, follows from Gelfond's
method ([GelfondMeasure.lean](../NLQCLean/Arithmetic/GelfondMeasure.lean)). Hence, with
`BasuPollackRoyExistentialElimination` only,
`exists_explicit_controlledPhase_one_double_exp_bound_of_QE` gives the stated rate
`g_K(1) ≥ exp(-exp(C K²))`, and with no input at all,
`controlledPhase_one_lower_bound_free_triple` gives `g_K(1) ≥ exp(-exp(exp(175 K²)))`
([ExplicitControlledPhaseGelfond.lean](../NLQCLean/Bounds/ExplicitControlledPhaseGelfond.lean));
the unconditional bound replaces quantifier elimination by iterated resultants. The earlier
theorems with the weaker Hermite measure (`exp(-exp(exp(C K²)))` with E-QE only,
`exp(-exp(exp(exp(171 K²))))` with no input) are kept.

The precise propositions are in
[EffectiveArithmetic.lean](../NLQCLean/External/EffectiveArithmetic.lean).
They are explicit hypotheses, rather than axioms or typeclass instances.
The kernel verifies the consequences of these hypotheses; it does not
verify the cited published proofs.

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

The formal effective bound proves existence of its constants; their effective computability is not formalized. The source-to-theorem map describes other scope differences.
