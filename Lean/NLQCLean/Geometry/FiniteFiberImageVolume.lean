/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.GraphFiberMultiplicity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Image volume from square Jacobians and finite fibers

Apply the equal-dimensional image-Jacobian inequality to the
graph maps and sum their domain volumes using fiber multiplicities.
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

theorem volume_image_le_of_det_le {m : ℕ} {D : Set (RealEuclidean m)}
    (hD : MeasurableSet D) (f : RealEuclidean m → RealEuclidean m)
    (f' : RealEuclidean m → RealEuclidean m →L[ℝ] RealEuclidean m)
    (hder : ∀ x ∈ D, HasFDerivWithinAt f (f' x) D x)
    {K : ℝ} (hdet : ∀ x ∈ D, |(f' x).det| ≤ K) :
    volume (f '' D) ≤ ENNReal.ofReal K * volume D := by
  calc
    _ ≤ ∫⁻ x in D, ENNReal.ofReal |(f' x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hD hder
    _ ≤ ∫⁻ _ in D, ENNReal.ofReal K :=
      setLIntegral_mono' hD (fun x hx => ENNReal.ofReal_le_ofReal (hdet x hx))
    _ = _ := by simp

theorem volume_iUnion_graphImages_le {a m : ℕ} {ι : Type*} [Countable ι]
    (D : ι → Set (RealEuclidean m)) (g : ι → RealEuclidean m → RealEuclidean a)
    (C : Set (RealEuclidean a)) (I : Fin m → Fin a) (hI : Function.Injective I)
    (hDm : ∀ j, MeasurableSet (D j))
    (hsub : ∀ j, g j '' D j ⊆ C)
    (hproj : ∀ j, ∀ y ∈ D j, coordinateProjection I (g j y) = y)
    (hdis : Pairwise (fun i j => Disjoint (g i '' D i) (g j '' D j)))
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M)
    (p : RealEuclidean a → RealEuclidean m)
    (q : ι → RealEuclidean m → RealEuclidean m →L[ℝ] RealEuclidean m)
    (hder : ∀ j, ∀ y ∈ D j, HasFDerivWithinAt (p ∘ g j) (q j y) (D j) y)
    {K : ℝ} (hdet : ∀ j, ∀ y ∈ D j, |(q j y).det| ≤ K) :
    volume (⋃ j, (p ∘ g j) '' D j) ≤
      ENNReal.ofReal K * (M : ℝ≥0∞) * volume (closedBall (0 : RealEuclidean m) R) := by
  calc
    _ ≤ ∑' j, volume ((p ∘ g j) '' D j) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal K * volume (D j) :=
      ENNReal.tsum_le_tsum (fun j => volume_image_le_of_det_le (hDm j) _ (q j) (hder j) (hdet j))
    _ = ENNReal.ofReal K * ∑' j, volume (D j) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal K * ((M : ℝ≥0∞) * volume (closedBall (0 : RealEuclidean m) R)) := by
      gcongr
      exact sum_volume_graphDomains_le D g C I hI hDm hsub hproj hdis hR M hfib
    _ = _ := (mul_assoc _ _ _).symm

theorem volume_iUnion_smoothGraphImages_le {a m : ℕ} {ι : Type*} [Countable ι]
    (D O : ι → Set (RealEuclidean m)) (g : ι → RealEuclidean m → RealEuclidean a)
    (C : Set (RealEuclidean a)) (I : Fin m → Fin a) (hI : Function.Injective I)
    (hDm : ∀ j, MeasurableSet (D j)) (hO : ∀ j, IsOpen (O j)) (hDO : ∀ j, D j ⊆ O j)
    (hg : ∀ j, ContDiffOn ℝ 1 (g j) (O j))
    (hsub : ∀ j, g j '' D j ⊆ C)
    (hproj : ∀ j, ∀ y ∈ D j, coordinateProjection I (g j y) = y)
    (hdis : Pairwise (fun i j => Disjoint (g i '' D i) (g j '' D j)))
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M)
    (p : RealEuclidean a → RealEuclidean m) {U : Set (RealEuclidean a)}
    (hU : IsOpen U) (hCU : C ⊆ U) (hp : ContDiffOn ℝ 1 p U)
    {b : ℝ} (hb : 0 ≤ b) (hJ : ∀ x ∈ C, topRealJacobian (fderiv ℝ p x) ≤ b)
    (hslope : ∀ j, ∀ y ∈ D j,
      Real.sqrt (((fderiv ℝ (g j) y).adjoint).comp (fderiv ℝ (g j) y)).det ≤ (2 : ℝ) ^ a) :
    volume (⋃ j, (p ∘ g j) '' D j) ≤
      ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
        volume (closedBall (0 : RealEuclidean m) R) := by
  apply volume_iUnion_graphImages_le D g C I hI hDm hsub hproj hdis hR M hfib p
    (fun j y => (fderiv ℝ p (g j y)).comp (fderiv ℝ (g j) y))
  · intro j y hy
    have hgy := hCU (hsub j ⟨y, hy, rfl⟩)
    exact (((hp _ hgy).contDiffAt (hU.mem_nhds hgy)).differentiableAt_one.hasFDerivAt.comp y
      (((hg j y (hDO j hy)).contDiffAt ((hO j).mem_nhds (hDO j hy))).differentiableAt_one.hasFDerivAt)).hasFDerivWithinAt
  · intro j y hy
    exact (rectangular_det_le _ _).trans (mul_le_mul (hJ _ (hsub j ⟨y, hy, rfl⟩))
      (hslope j y hy) (Real.sqrt_nonneg _) hb)

end NLQCLean
end
