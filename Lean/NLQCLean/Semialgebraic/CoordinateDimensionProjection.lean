/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.DimensionDef

/-!
# Coordinate projections do not increase coordinate dimension

For an injective coordinate selection `I`, every
selection `J` witnessing interior for `coordinateProjection I '' S` composes to
the injective selection `I ∘ J` witnessing the same interior for `S`. This holds
for arbitrary sets and uses no external input; it is not the general
semialgebraic image-dimension theorem.
-/

section

namespace NLQCLean

theorem HasCoordinateInterior.of_image_coordinateProjection {n a k : ℕ} {I : Fin a → Fin n}
    (hI : Function.Injective I) {S : Set (RealEuclidean n)}
    (h : HasCoordinateInterior (coordinateProjection I '' S) k) : HasCoordinateInterior S k := by
  obtain ⟨J, hJ, hint⟩ := h
  refine ⟨I ∘ J, hI.comp hJ, ?_⟩
  rwa [← coordinateProjection_comp, Set.image_comp]

theorem coordinateInteriorDimension_image_coordinateProjection_le {n a : ℕ}
    (I : Fin a → Fin n) (hI : Function.Injective I) (S : Set (RealEuclidean n)) :
    coordinateInteriorDimension (coordinateProjection I '' S) ≤ coordinateInteriorDimension S := by
  classical
  apply Finset.sup_le
  intro k hk
  exact le_coordinateInteriorDimension
    ((Finset.mem_filter.mp hk).2.of_image_coordinateProjection hI)

end NLQCLean
end
