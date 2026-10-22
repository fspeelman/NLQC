# Hermite–Lindemann compatibility port

Required missing-module closure from [Mathlib PR 28013](https://github.com/leanprover-community/mathlib4/pull/28013) at pinned commit
`5a0057ccc26b13a4e361f503f5f765bf56a8d353`, retrieved 1 October 2026.
The original source paths and SHA-256 hashes are in
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json). Upstream licenses and genuine
copyright/author notices are preserved. The project toolchain is now
Lean/Mathlib v4.35.0.

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

Compatibility update for Lean/Mathlib v4.34.1 (2 October 2026), retaining
the same upstream pin and source manifest: `AlgebraicPart.lean` uses
`Finsupp.mapDomain_apply_of_injective`; `SymmetricEval.lean` reuses Mathlib's
`Multiset.esymm_zero` and `Multiset.esymm_of_card_lt` instead of declaring
the v4.33.1 compatibility copies; `Basic.lean` supplies the explicit base
ring to `Complex.isIntegral_I`. The original upstream notices remain.

Compatibility update for Lean/Mathlib v4.35.0 (22 October 2026), retaining
the same upstream pin and source manifest: in
`coeff_single_mul_single_zero_ne_zero_iff`, `AlgebraicPart.lean` states the
local torsion-freeness fact as `HasUniqueDiv R` (Mathlib renamed
`IsAddTorsionFree.of_isTorsionFree` to `HasUniqueDiv.of_isTorsionFree`; the
`IsAddTorsionFree` instance is derived from it). No other vendored file changed.

Module system (22 October 2026): each vendored file again starts with
`module`, makes all its imports `public` and opens `@[expose] public section`
(a uniform project form, not the upstream visibility markers removed
initially), because module files cannot import non-module files. In
`AlgebraicPart.lean` the theorem `toFinsuppAux_apply_apply_mk` is no longer
`private`, since the exposed definition `toFinsupp` uses it. Statements,
proofs and notices are otherwise unchanged.
