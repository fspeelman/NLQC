/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.AffineSlices
import NLQCLean.Semialgebraic.RegularCoordinateFibers

/-!
# Lifted fiber-cardinality bound without the fiber-dimension input

Projection closure makes the projected source semialgebraic,
stratification makes almost every coordinate fiber finite, and
`card_projected_coordinateFiber_le` bounds each finite fiber by
`componentFormatBase (2*c) (max D 2) ^ n`, with n the original lifted
dimension. The cube decomposition enters only the qualitative finiteness.
-/

section

open Set MeasureTheory

namespace NLQCLean

theorem HasSemialgebraicFormat.ae_card_projected_coordinateFiber_le_of_stratification
    (hComponents : SemialgebraicComponentBoundTheorem)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n a m c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (J : Fin a → Fin n) (I : Fin m → Fin a)
    (hd : coordinateInteriorDimension (coordinateProjection J '' S) ≤ m) :
    ∀ᵐ y, (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y) ≤
        componentFormatBase (2 * c) (max D 2) ^ n := by
  have hC := (hS.semialgebraic.coordinate_graph J).image hProjection
  filter_upwards [ae_finite_coordinateFiber_of_stratification hStratification hC I hd] with y hy
  exact ⟨hy, hS.card_projected_coordinateFiber_le hComponents hc J I y hy⟩

end NLQCLean
end
