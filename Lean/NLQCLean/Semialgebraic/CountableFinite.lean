/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Fibers
import NLQCLean.Geometry.RegularFibers

/-!
# Countable semialgebraic sets are finite; regular chart fibers are countable

A smooth cube of dimension d has
a coordinate projection with nonempty interior in `RealEuclidean d` (by the coordinate
dictionary), whose Hausdorff dimension is d; a countable set has Hausdorff
dimension zero. Hence every cube of a decomposition of a countable set has
dimension zero, and stratification makes the set finite. No other input is used.

The chart transport keeps the parametrization on the open unit cube and
an arbitrary C1 target map; no global chart inverse is assumed.
-/

section

open Set

namespace NLQCLean

theorem SemialgebraicSmoothCube.dimension_eq_zero_of_countable {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) (hc : C.Countable) :
    d = 0 := by
  obtain ⟨I, _, hI⟩ := hC.hasCoordinateInterior
  have h := (hc.image (coordinateProjection I)).dimH_zero
  rw [Real.dimH_of_nonempty_interior hI] at h
  simpa using h

/-- A countable semialgebraic set is finite, using smooth stratification. -/
theorem Semialgebraic.finite_of_countable
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S) (hc : S.Countable) :
    S.Finite := by
  obtain ⟨P⟩ := hS.exists_smoothCubeDecomposition hStratification
  exact P.finite_of_dimensions_zero fun i =>
    (P.smoothCube i).dimension_eq_zero_of_countable (hc.mono (P.piece_subset i))

/-- Regular fibers through a chart: for a C1 parametrization of the open unit
cube and a C1 map into the same dimension, the fiber of the image over a value
at which the composite has invertible derivative is countable. -/
theorem countable_semialgebraicMapFiber_image_of_det_ne_zero {m n : ℕ}
    {φ : RealEuclidean m → RealEuclidean n} (hφ : ContDiffOn ℝ 1 φ (openUnitCube m))
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiff ℝ 1 f) {y : RealEuclidean m}
    (hreg : ∀ x ∈ openUnitCube m, f (φ x) = y → (fderiv ℝ (f ∘ φ) x).det ≠ 0) :
    (semialgebraicMapFiber (φ '' openUnitCube m) f y).Countable := by
  have hcount : (openUnitCube m ∩ (f ∘ φ) ⁻¹' {y}).Countable := by
    apply countable_inter_preimage_singleton_of_det_ne_zero (f' := fderiv ℝ (f ∘ φ))
    intro x hx hxy
    have hAt : ContDiffAt ℝ 1 (f ∘ φ) x :=
      hf.contDiffAt.comp x ((hφ x hx).contDiffAt ((isOpen_openUnitCube m).mem_nhds hx))
    exact ⟨hAt.hasStrictFDerivAt one_ne_zero, hreg x hx hxy⟩
  refine (hcount.image φ).mono ?_
  rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
  exact ⟨x, ⟨hx, hy⟩, rfl⟩

end NLQCLean
end
