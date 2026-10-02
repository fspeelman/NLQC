/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.MaximalCoordinateGraphs
import NLQCLean.Geometry.CoordinateProjectionNorms
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# graph-domain multiplicities

Active chart indices inject into the coordinate fiber
because their source images are disjoint. Tonelli then bounds the sum of
base-domain volumes without any bound on the number of charts.
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

theorem graphDomain_indicator_sum_le_fiber {a m : ℕ} {ι : Type*}
    (D : ι → Set (RealEuclidean m)) (g : ι → RealEuclidean m → RealEuclidean a)
    (C : Set (RealEuclidean a)) (I : Fin m → Fin a)
    (hsub : ∀ j, g j '' D j ⊆ C)
    (hproj : ∀ j, ∀ y ∈ D j, coordinateProjection I (g j y) = y)
    (hdis : Pairwise (fun i j => Disjoint (g i '' D i) (g j '' D j)))
    (y : RealEuclidean m) (hfin : (semialgebraicMapFiber C (coordinateProjection I) y).Finite) :
    (∑' j, (D j).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      (Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) : ℝ≥0∞) := by
  classical
  let active : Set ι := {j | y ∈ D j}
  let f : active → semialgebraicMapFiber C (coordinateProjection I) y := fun j =>
    ⟨g j.val y, hsub j.val ⟨y, j.prop, rfl⟩, hproj j.val y j.prop⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have heq : g i.val y = g j.val y := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdis hne) ⟨y, i.prop, rfl⟩ ⟨y, j.prop, heq.symm⟩
  have : Finite (semialgebraicMapFiber C (coordinateProjection I) y) := hfin.to_subtype
  calc
    _ = ∑' _ : active, (1 : ℝ≥0∞) := by
      rw [tsum_subtype active (fun _ : ι => (1 : ℝ≥0∞))]
      congr 1
    _ ≤ ∑' _ : semialgebraicMapFiber C (coordinateProjection I) y, (1 : ℝ≥0∞) :=
      ENNReal.tsum_comp_le_tsum_of_injective hf (fun _ => 1)
    _ = _ := by rw [ENNReal.tsum_one, ENat.card_eq_coe_natCard]; rfl

theorem graphDomain_subset_closedBall {a m : ℕ} {ι : Type*}
    (D : ι → Set (RealEuclidean m)) (g : ι → RealEuclidean m → RealEuclidean a)
    (C : Set (RealEuclidean a)) (I : Fin m → Fin a) (hI : Function.Injective I)
    (hsub : ∀ j, g j '' D j ⊆ C)
    (hproj : ∀ j, ∀ y ∈ D j, coordinateProjection I (g j y) = y)
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (j : ι) : D j ⊆ closedBall 0 R := by
  intro y hy
  have hnorm := norm_coordinateProjection_le I hI (g j y)
  rw [hproj j y hy] at hnorm
  have hb := hR (hsub j ⟨y, hy, rfl⟩)
  simpa only [mem_closedBall, dist_zero_right] using
    hnorm.trans (show ‖g j y‖ ≤ R by simpa only [mem_closedBall, dist_zero_right] using hb)

theorem sum_volume_graphDomains_le {a m : ℕ} {ι : Type*} [Countable ι]
    (D : ι → Set (RealEuclidean m)) (g : ι → RealEuclidean m → RealEuclidean a)
    (C : Set (RealEuclidean a)) (I : Fin m → Fin a) (hI : Function.Injective I)
    (hDm : ∀ j, MeasurableSet (D j))
    (hsub : ∀ j, g j '' D j ⊆ C)
    (hproj : ∀ j, ∀ y ∈ D j, coordinateProjection I (g j y) = y)
    (hdis : Pairwise (fun i j => Disjoint (g i '' D i) (g j '' D j)))
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M) :
    (∑' j, volume (D j)) ≤ (M : ℝ≥0∞) * volume (closedBall (0 : RealEuclidean m) R) := by
  classical
  have hbound : ∀ᵐ y, (∑' j, (D j).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      (closedBall (0 : RealEuclidean m) R).indicator (fun _ => (M : ℝ≥0∞)) y := by
    filter_upwards [hfib] with y hy
    by_cases hball : y ∈ closedBall (0 : RealEuclidean m) R
    · rw [Set.indicator_of_mem hball]
      exact (graphDomain_indicator_sum_le_fiber D g C I hsub hproj hdis y hy.1).trans
        (by exact_mod_cast hy.2)
    · rw [Set.indicator_of_notMem hball]
      have hout (j : ι) : y ∉ D j := fun hj =>
        hball (graphDomain_subset_closedBall D g C I hI hsub hproj hR j hj)
      simp only [Set.indicator_of_notMem (hout _), tsum_zero, le_refl]
  calc
    _ = ∑' j, ∫⁻ y, (D j).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      congr 1
      funext j
      rw [lintegral_indicator (hDm j)]
      simp
    _ = ∫⁻ y, ∑' j, (D j).indicator (fun _ => (1 : ℝ≥0∞)) y :=
      (lintegral_tsum (fun j => (measurable_const.indicator (hDm j)).aemeasurable)).symm
    _ ≤ ∫⁻ y, (closedBall (0 : RealEuclidean m) R).indicator (fun _ => (M : ℝ≥0∞)) y :=
      lintegral_mono_ae hbound
    _ = _ := by rw [lintegral_indicator isClosed_closedBall.measurableSet]; simp

end NLQCLean
end
