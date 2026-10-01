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

theorem Semialgebraic.exists_smoothCubeDecomposition
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S) :
    Nonempty (SmoothCubeDecomposition S) := by
  obtain ⟨P, _⟩ := hStratification n S hS 0 Fin.elim0 (fun i => Fin.elim0 i)
  exact ⟨P⟩

theorem Semialgebraic.finite_of_dimension_zero
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S)
    (hd : coordinateInteriorDimension S = 0) : S.Finite := by
  obtain ⟨P⟩ := hS.exists_smoothCubeDecomposition hStratification
  exact P.finite_of_dimensions_zero fun i => Nat.eq_zero_of_le_zero (hd ▸ P.dimension_le i)

theorem Semialgebraic.dimH_le_dimension
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S) :
    dimH S ≤ coordinateInteriorDimension S := by
  obtain ⟨P⟩ := hS.exists_smoothCubeDecomposition hStratification
  exact P.dimH_le P.dimension_le

theorem Semialgebraic.volume_eq_zero_of_dimension_lt
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S)
    (hd : coordinateInteriorDimension S < n) : MeasureTheory.volume S = 0 :=
  volume_eq_zero_of_dimH_lt
    ((hS.dimH_le_dimension hStratification).trans_lt (by exact_mod_cast hd))

theorem Semialgebraic.volume_image_eq_zero_of_dimension_lt
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n m : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiffOn ℝ 1 f S)
    (hd : coordinateInteriorDimension S < m) : MeasureTheory.volume (f '' S) = 0 := by
  obtain ⟨P⟩ := hS.exists_smoothCubeDecomposition hStratification
  exact P.volume_image_eq_zero hf fun i => (P.dimension_le i).trans_lt hd

/-- The three dimension statements with the coordinate/chart dictionary supplied. -/
theorem semialgebraicDimensionTheorems_of_image_fiber
    (hImage : SemialgebraicDimensionImageTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem) : SemialgebraicDimensionTheorems :=
  ⟨semialgebraicDimensionStrataTheorem, hImage, hFiber⟩

end NLQCLean
end
