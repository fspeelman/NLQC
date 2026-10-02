# Mathematical assumptions

All results are unconditional except the effective controlled-phase bound
in Appendix C. This covers the exact impossibility and finite-orbit results,
compact score optima, qualitative gaps, spectral floors, generic rank
conclusions, and all quantitative Haar and precision estimates (Theorems A–C, the diagonal-gate theorem and their corollaries in
the robust companion). The kernel audits show only the
standard logical axioms `propext`, `Classical.choice` and `Quot.sound`.

The effective bound takes two explicit proposition arguments:

| Lean proposition | Mathematical content | Source |
|---|---|---|
| `BasuPollackRoyExistentialElimination` | One-block real quantifier elimination for two free variables with degree `d^{O(k)}` and bit size `τ d^{O(k)}` | Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed., Theorem 14.16 |
| `PolynomialTypeTranscendenceMeasureExpAngle` | A transcendence measure `exp(-C (N + log H)^c)` for `e^{iθ}`, `θ ≠ 0` real algebraic (the form cited in Appendix C) | Implied by Cijsouw, Compositio Math. 28 (1974), Theorem 1 (`CijsouwTranscendenceMeasureExp.polynomialType`) |

The precise propositions are in
[EffectiveArithmetic.lean](../NLQCLean/External/EffectiveArithmetic.lean).
They are explicit hypotheses, rather than axioms or typeclass instances.
The kernel verifies the consequences of these hypotheses; it does not
verify the cited published proofs.

The quantitative estimates rest on the polynomial image-volume bound, proved
by `NLQCLean.DirectVolume.polynomialImageVolumeBound`
([Assembly.lean](../NLQCLean/Geometry/DirectVolume/Assembly.lean)) with an
explicit base 450240 for the fixed polynomial format used by the library. Semialgebraic projection closure is proved by
`NLQCLean.semialgebraicProjectionTheorem` in
[ProjectionTheorem.lean](../NLQCLean/Semialgebraic/ProjectionTheorem.lean),
using the vendored Sundog real quantifier-elimination development. The
almost-every exact-impossibility results use vector Sard.

The maintained audits print full theorem types as well as axioms, so explicit
hypotheses remain visible.

The formal effective bound proves existence of its constants; their effective computability is not formalized. The source-to-theorem map describes other scope differences.
