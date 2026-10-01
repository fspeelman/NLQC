/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.CountableFinite
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Almost every coordinate fiber is finite, from stratification alone

Decompose `A` into smooth cubes of dimension at
most m. A cube of smaller dimension has null image. For a cube of dimension m,
the image of the critical points of `f ∘ φ` on the open parameter cube is null
by Mathlib's equal-dimensional Jacobian theorem, and every other fiber of the
cube is countable. Outside the finite union of these null sets, the
fiber in `A` is a countable semialgebraic set, hence finite.

This theorem sits beside `ae_finite_coordinateFiber`; it uses neither the
general image-dimension nor general fiber-dimension contract, assumes no injectivity of `I`,
and claims no semialgebraicity of
the exceptional set.
-/

section

open Set MeasureTheory

namespace NLQCLean

/-- Per cube: outside an explicit null set, the fiber of a C1 map into a space
of dimension at least the cube dimension is countable. -/
theorem SemialgebraicSmoothCube.exists_null_countable_fiber {n k m : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C k) (hk : k ≤ m)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiff ℝ 1 f) :
    ∃ N : Set (RealEuclidean m), volume N = 0 ∧
      ∀ y ∉ N, (semialgebraicMapFiber C f y).Countable := by
  rcases hk.lt_or_eq with hlt | rfl
  · refine ⟨f '' C, hC.volume_image_eq_zero hf.contDiffOn hlt, fun y hy => ?_⟩
    refine Set.countable_empty.mono ?_
    rintro x ⟨hxC, rfl⟩
    exact hy ⟨x, hxC, rfl⟩
  · obtain ⟨_, _, _, φ, rfl, _, hφ, _⟩ := hC
    have hAt (x : RealEuclidean k) (hx : x ∈ openUnitCube k) : ContDiffAt ℝ 1 (f ∘ φ) x :=
      hf.contDiffAt.comp x ((hφ x hx).contDiffAt ((isOpen_openUnitCube k).mem_nhds hx))
    let crit : Set (RealEuclidean k) :=
      {x | x ∈ openUnitCube k ∧ (fderiv ℝ (f ∘ φ) x).det = 0}
    refine ⟨(f ∘ φ) '' crit, ?_, fun y hy => ?_⟩
    · exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
        (fun x hx => ((hAt x hx.1).hasStrictFDerivAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
        (fun x hx => hx.2)
    · apply countable_semialgebraicMapFiber_image_of_det_ne_zero hφ hf
      intro x hx hxy hdet
      exact hy ⟨x, ⟨hx, hdet⟩, hxy⟩

/-- Finite coordinate fibers: for semialgebraic A of coordinate-interior dimension at most m,
almost every fiber of an arbitrary coordinate selection into `RealEuclidean m`
is finite. The only external input is smooth stratification. -/
theorem ae_finite_coordinateFiber_of_stratification
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    (I : Fin m → Fin n) (hd : coordinateInteriorDimension A ≤ m) :
    ∀ᵐ y, (semialgebraicMapFiber A (coordinateProjection I) y).Finite := by
  obtain ⟨P⟩ := hA.exists_smoothCubeDecomposition hStratification
  have hcube (i : Fin P.count) := (P.smoothCube i).exists_null_countable_fiber
    ((P.dimension_le i).trans hd) (contDiff_coordinateProjection I)
  choose N hN hNc using hcube
  filter_upwards [compl_mem_ae_iff.mpr (measure_iUnion_null hN)] with y hy
  apply ((hA.coordinate_graph I).fiber y).finite_of_countable hStratification
  refine (Set.countable_iUnion fun i => hNc i y fun h => hy (mem_iUnion.mpr ⟨i, h⟩)).mono ?_
  rintro x ⟨hxA, hxy⟩
  rw [← P.covers] at hxA
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
  exact mem_iUnion.mpr ⟨i, hi, hxy⟩

end NLQCLean
end
