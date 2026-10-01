/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.LRTGraphSelections
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Ambient Jacobian bounds near the original source

Continuity of the top Jacobian and compactness give a
B+eta bound in a neighborhood of X. The source selections eventually
lie there. There is no additional off-X Jacobian assumption or division by B.
-/

section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace NLQCLean

theorem continuous_topRealJacobian (a m : ℕ) :
    Continuous (topRealJacobian : (RealEuclidean a →L[ℝ] RealEuclidean m) → ℝ) := by
  have ha : Continuous (fun L : RealEuclidean a →L[ℝ] RealEuclidean m => L.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp (continuous_id.clm_comp ha))

theorem ContDiff.continuous_topRealJacobian_fderiv {a m : ℕ}
    {p : RealEuclidean a → RealEuclidean m} (hp : ContDiff ℝ 1 p) :
    Continuous (fun x => topRealJacobian (fderiv ℝ p x)) :=
  (continuous_topRealJacobian a m).comp (hp.continuous_fderiv one_ne_zero)

theorem IsCompact.exists_closedNeighborhood_function_le {a : ℕ}
    {S : Set (RealEuclidean a)} (hS : IsCompact S) {f : RealEuclidean a → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ x ∈ S, f x ≤ B)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ closedEuclideanNeighborhood S r, f x ≤ B + η := by
  have hsub : S ⊆ f ⁻¹' Iio (B + η) := by
    intro x hx
    have h := hB x hx
    change f x < B + η
    linarith
  obtain ⟨r, hr, hnb⟩ := hS.exists_cthickening_subset_open (isOpen_Iio.preimage hf) hsub
  refine ⟨r, hr, ?_⟩
  rintro x ⟨s, hs, hxs⟩
  have hm : x ∈ cthickening r S := mem_cthickening_of_dist_le x s r S hs
    (by simpa only [dist_eq_norm] using hxs)
  exact (hnb hm).le

theorem PolynomialGraphSelections.eventually_topRealJacobian_le {a m κ : ℕ}
    {F : PolynomialBasicClosedFormat a} {p : BoundedPolynomialMap a m}
    (P : PolynomialGraphSelections F p κ) (hF : IsCompact F.source)
    {B : ℝ} (hB : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, ∀ x ∈ P.source j, topRealJacobian (fderiv ℝ p.eval x) ≤ B + η := by
  obtain ⟨r, hr, hnb⟩ := NLQCLean.IsCompact.exists_closedNeighborhood_function_le hF
    (NLQCLean.ContDiff.continuous_topRealJacobian_fderiv p.contDiff_eval) hB hη
  filter_upwards [tendsto_lrtTolerance.eventually (gt_mem_nhds hr)] with j hj
  intro x hx
  obtain ⟨s, hs, hxs⟩ := P.source_proximity j hx
  exact hnb x ⟨s, hs, hxs.trans hj.le⟩

end NLQCLean
end
