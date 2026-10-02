/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.C1Decomposition
import NLQCLean.LinearAlgebra.CoordinateRank
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Coordinate dimension agrees with smooth cube dimension

An injective derivative admits an invertible
coordinate selection. The inverse function theorem gives interior for that
projection. Combined with C1 Hausdorff dimension bounds, this proves the
audited dimension dictionary without the general image-dimension or fiber-dimension theorem.
-/

section

open Set Filter
open scoped Topology

namespace NLQCLean

theorem SemialgebraicSmoothCube.hasCoordinateInterior {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) :
    HasCoordinateInterior C d := by
  obtain ⟨_, _, _, φ, hφ, _, hdiff, hinj, _⟩ := hC
  obtain ⟨x, hx⟩ := openUnitCube_nonempty d
  have hnhds := (isOpen_openUnitCube d).mem_nhds hx
  have hAt := (hdiff x hx).contDiffAt hnhds
  obtain ⟨I, hI, e, he⟩ := exists_equiv_coordinateProjection_comp (fderiv ℝ φ x) (hinj x hx)
  have hstrict := (coordinateProjectionL I).hasStrictFDerivAt.comp x
    (hAt.hasStrictFDerivAt one_ne_zero)
  rw [← he] at hstrict
  have hmem : (coordinateProjection I ∘ φ) '' openUnitCube d ∈
      𝓝 ((coordinateProjection I ∘ φ) x) := by
    change (fun z => coordinateProjectionL I (φ z)) '' openUnitCube d ∈
      𝓝 (coordinateProjectionL I (φ x))
    rw [← hstrict.map_nhds_eq_of_equiv]
    exact image_mem_map hnhds
  refine ⟨I, hI, ?_⟩
  rw [← hφ, ← image_comp]
  exact ⟨_, mem_interior_iff_mem_nhds.mpr hmem⟩

theorem SemialgebraicSmoothCube.coordinateInteriorDimension_eq {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) :
    coordinateInteriorDimension C = d :=
  le_antisymm hC.coordinateInteriorDimension_le
    (le_coordinateInteriorDimension hC.hasCoordinateInterior)

theorem SmoothCubeDecomposition.coordinateInteriorDimension_eq {n : ℕ}
    {S : Set (RealEuclidean n)} (P : SmoothCubeDecomposition S) :
    coordinateInteriorDimension S = Finset.univ.sup P.dimension := by
  classical
  apply le_antisymm
  · exact P.coordinateInteriorDimension_le fun i => Finset.le_sup (Finset.mem_univ i)
  · apply Finset.sup_le
    intro i _
    rw [← (P.smoothCube i).coordinateInteriorDimension_eq]
    exact coordinateInteriorDimension_mono (P.piece_subset i)

/-- Coordinate-interior dimension equals the maximal chart dimension in a
smooth cube decomposition, without any external premise. -/
theorem semialgebraicDimensionStrataTheorem : SemialgebraicDimensionStrataTheorem := by
  intro n S _ _ P
  exact P.coordinateInteriorDimension_eq

theorem SmoothCubeDecomposition.dimension_le {n : ℕ} {S : Set (RealEuclidean n)}
    (P : SmoothCubeDecomposition S) (i : Fin P.count) :
    P.dimension i ≤ coordinateInteriorDimension S := by
  classical
  rw [P.coordinateInteriorDimension_eq]
  exact Finset.le_sup (Finset.mem_univ i)

/-- The three dimension statements with the coordinate/chart dictionary supplied. -/
theorem semialgebraicDimensionTheorems_of_image_fiber
    (hImage : SemialgebraicDimensionImageTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem) : SemialgebraicDimensionTheorems :=
  ⟨semialgebraicDimensionStrataTheorem, hImage, hFiber⟩

end NLQCLean
end
