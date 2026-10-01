/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.Sundog.SemialgebraicProjection
import NLQCLean.Semialgebraic.SundogBridge

/-!
# Semialgebraic projection theorem

The coordinate projection `RealEuclidean (n + 1) → RealEuclidean n` forgetting
the last coordinate maps finite polynomial sign descriptions to finite
polynomial sign descriptions. This is the proposition
`SemialgebraicProjectionTheorem`, for every dimension `n` (including `n = 0`),
every set (including `∅`) and arbitrary real coefficients.

The proof transports the question along the coordinate isomorphism to Sundog's
Boolean closure `Sundog.TarskiQE.SADef` of strict polynomial inequalities
(`semialgebraic_iff_sadef`), identifies the Euclidean projection with Sundog's
elimination of the last variable through `Fin.snoc`
(`toLp_preimage_image_coordinateProjection_castAdd`), and applies the
vendored real quantifier-elimination step `Sundog.TarskiQE.sadef_proj`.
-/

namespace NLQCLean

/-- Projection closure of finite real polynomial sign descriptions, proved from
Sundog's one-variable elimination. There are no hypotheses. -/
theorem semialgebraicProjectionTheorem : SemialgebraicProjectionTheorem :=
  semialgebraicProjectionTheorem_of_sadef_projection fun _ _ => Sundog.TarskiQE.sadef_proj

end NLQCLean
