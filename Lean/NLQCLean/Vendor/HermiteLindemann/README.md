# Hermite–Lindemann compatibility port

Required missing-module closure from [Mathlib PR 28013](https://github.com/leanprover-community/mathlib4/pull/28013) at pinned commit
`5a0057ccc26b13a4e361f503f5f765bf56a8d353`, retrieved 1 October 2026.
The original source paths and SHA-256 hashes are in
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json). Upstream licenses and genuine
copyright/author notices are preserved. The project toolchain remains
Lean/Mathlib v4.33.1.

Initial compatibility modifications: redirect the four missing module
imports to this directory; remove newer module-system commands and import
visibility markers; place the final transcendence declarations in
`NLQCLean.HermiteLindemann`. The existing pinned analytic Lindemann proof
and all other imports are reused unchanged. Pinned API repairs: replace the renamed Finsupp map-domain lemma and
imaginary-unit integrality lemma; prove the missing multiset zero/oversized
symmetric identities directly from `powersetCard`; prove the scaleRoots
scalar evaluation identity from the pinned `scaleRoots_eval₂_mul`.
The port is checked by `NLQCTests.HermiteLindemannAudit`, which prints full
statements and guards the standard logical axioms of all six public
transcendence/independence declarations. No toolchain update or external
transcendence premise is used. This port alone does not prove the project’s
named exact controlled-phase obstruction.

The four source hashes were checked against the pinned upstream commit; the
Apache license matches upstream byte-for-byte. The missing import closure is
`Basic` → `AlgebraicPart` and `SymmetricEval`, with `AlgebraicPart` →
`FinsuppQuotient`. All remaining imports are supplied by pinned Mathlib.
