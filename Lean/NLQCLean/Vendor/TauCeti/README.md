# Tau Ceti scalar and full vector Sard port

These seven Lean files are derived from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/667541263c3e16f69fc437c58415745e202ef0db)
at immutable commit `667541263c3e16f69fc437c58415745e202ef0db`.
The scalar-Sard interface is [ScalarSard.lean](../../Geometry/ScalarSard.lean).
The full vector-valued Morse–Sard interface is
[VectorSard.lean](../../Geometry/VectorSard.lean), for smooth maps between
finite-dimensional real normed spaces of arbitrary dimensions.

## License and provenance

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. The copied material is Apache-2.0 licensed;
the upstream license is reproduced in [LICENSE](LICENSE). Original copyright
and attribution headers remain in every copied source. The complete upstream
Git tree at this revision contains no `NOTICE` file.

The upstream files, relative to `TauCeti/`, and their unmodified SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `Analysis/Calculus/Sard/FlatStratum.lean` | `ee6c29d1920f3cfddaa96c1cb9140ed0d7f3509257a1750ac8658424fb12e767` |
| `Analysis/Calculus/Sard/IntermediateStratum.lean` | `471be7f560d0a223824c23ab81c6421c7b2520e09b3b56fedccf4098535fe67e` |
| `Analysis/Calculus/Sard/VanishingDerivative.lean` | `ca2c1910fe1a86463289ab6175df45d912541d1013dd3f2c16c2322679aef47d` |
| `MeasureTheory/Measure/LocallyNull.lean` | `fa4dd35690822e6f8bc92aaf1667c3d38dbfa23e3bea6e0b4f695f8df00704d0` |
| `Analysis/Calculus/Sard/OutermostStratum.lean` | `d70b372941a4f1c46c4ddfce46ccc2c19aca3f99a071d0ca1d644e0ae3969d13` |
| `Analysis/Normed/Operator/Surjective.lean` | `bacfd8e5904e0698e17b33eb7244ecb66cac3bd802ead917652cbeabe44b906c` |
| `MeasureTheory/Measure/Haar/NormedSpace.lean` | `f3bb700d10ab353acc6fe55fea76909ff1a27d0001d50b574e75a4157652d960` |

The four scalar-Sard files total 774 original lines. They are the entire
transitive Tau Ceti import closure of the vanishing-derivative theorem.
The three full-Sard files add 539 original lines (412, 83 and 44), for 1313
original lines in all. The seven files are the entire transitive Tau Ceti
import closure of `OutermostStratum.lean`, and hence of the full Morse--Sard
theorem `TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero`; all other
dependencies are Mathlib. No full Tau Ceti package dependency is introduced.

## Pins and local adaptations

Upstream uses Lean `v4.34.0-rc2` and Mathlib
`369aeb92f434826041d430d3b015d6ab0006bf72`. This port targets the unchanged
project Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

Local modules and declaration namespaces replace the prefix `TauCeti` with
`NLQCLean.Vendor.TauCeti`; source headers identify the modification.
No theorem statement, proof body or docstring was changed. The only changes
are the namespace opening/closing names, the local imports (three in
`VanishingDerivative.lean`, four in `OutermostStratum.lean`), and the
modification notice in each header. In particular, the existing
`ImplicitContDiff`, iterated-derivative, inverse-function, Haar-uniqueness and
Hausdorff-dimension APIs suffice without a Mathlib or toolchain migration, and
no compatibility edit was needed.

Two consequences of keeping the bodies unchanged:

* Docstrings and a few proof terms in `OutermostStratum.lean` still write
  `TauCeti.`-qualified names. Inside the renamed namespace these resolve to
  the local declarations, for example to
  `NLQCLean.Vendor.TauCeti.addHaar_image_criticalPoints_eq_zero`.
* `MeasureTheory/Measure/Haar/NormedSpace.lean` declares its lemma with
  `_root_`, so it is the root-namespace name
  `ContinuousLinearEquiv.quasiMeasurePreserving_addHaar`, as upstream.
  The pinned Mathlib has no declaration of that name. A future Mathlib
  declaration with the same name would require renaming this vendored lemma.

## Interfaces and audits

The scalar wrapper is `NLQCLean.scalarCriticalImage_volume_eq_zero`.
It requires smoothness and vanishing full derivative on an arbitrary
subset of a finite-dimensional real normed source.

The vector wrappers are `NLQCLean.criticalImage_addHaar_eq_zero`,
`NLQCLean.criticalImage_volume_eq_zero` and
`NLQCLean.rankDeficientImage_addHaar_eq_zero`. They require smoothness
and a nonsurjective full derivative or derivative rank below the target
dimension on the specified subset. No relation between the two finite
dimensions is assumed. The smoothness assumption exceeds the upstream
finite regularity threshold.

[VectorSardAudit.lean](../../../NLQCTests/VectorSardAudit.lean) checks the
theorem types, examples and axiom dependencies. The wrappers depend only
on `propext`, `Classical.choice` and `Quot.sound`.
The vendor modules and maintained audits are included in the complete
`NLQCLean.All` and `NLQCTests` build targets.
