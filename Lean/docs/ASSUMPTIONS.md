# Mathematical assumptions

The exact impossibility, compact score optima, qualitative gaps, spectral
floors and generic rank conclusions are unconditional. The quantitative
Haar and precision estimates take three separate proposition arguments:

| Lean proposition | Mathematical content | Source |
|---|---|---|
| `LRTTheorem44` | Approximate low-dimensional definable selection for a bounded closed semialgebraic set under a coordinate projection; the constant is selected before ambient dimensions and degree | Lerario–Rizzi–Tiberio, *Quantitative approximate definable choices*, arXiv:2409.14869v2, Theorem 44 |
| `SemialgebraicSmoothStratificationTheorem` | A finite compatible semialgebraic C¹ stratification with embedded pieces diffeomorphic to open cubes and a frontier condition relative to the original set | Coste, *An Introduction to Semialgebraic Geometry* (2002), Corollary 3.8; Bochnak–Coste–Roy, *Real Algebraic Geometry*, §9.1 |
| `SemialgebraicComponentBoundTheorem` | Finitely many connected components for a conjunction of s polynomial conditions in k variables, bounded by Δ(2Δ−1)^(k+s−1), for degree Δ≥2 | Coste, Proposition 4.13 |

The precise propositions and their supporting definitions are in
[LRT44.lean](../NLQCLean/External/LRT44.lean) and
[SemialgebraicTextbook.lean](../NLQCLean/External/SemialgebraicTextbook.lean).
They are explicit hypotheses, rather than axioms or typeclass instances.
The kernel verifies the consequences of these hypotheses; it does not
verify the cited published proofs.

Semialgebraic projection closure is proved by
`NLQCLean.semialgebraicProjectionTheorem` in
[ProjectionTheorem.lean](../NLQCLean/Semialgebraic/ProjectionTheorem.lean),
using the vendored Sundog real quantifier-elimination development. Older
four-input compatibility theorems still accept projection explicitly.
The narrower coordinate-dimension and finite-fiber results used in the
volume argument do not establish the general textbook dimension theorems.

The two almost-every exact-impossibility results use vector Sard and need
none of the three geometry hypotheses. Standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound` may occur in kernel axiom
prints. The maintained audits print full theorem types as well as axioms,
so explicit external hypotheses remain visible.
