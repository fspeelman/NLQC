/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.LRTGraphSelections
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Hausdorff convergence of the selection images

Graph proximity controls the defect between evaluating the source
coordinate and taking the output coordinate. The symmetric Hausdorff triangle
then gives both directions of convergence. No definability of the sequence is used.
-/

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace NLQCLean

theorem hausdorffEDist_images_le_of_dist_le {α β : Type*} [PseudoMetricSpace β]
    (S : Set α) (f g : α → β) {r : ℝ} (h : ∀ x ∈ S, dist (f x) (g x) ≤ r) :
    hausdorffEDist (f '' S) (g '' S) ≤ ENNReal.ofReal r := by
  apply hausdorffEDist_le_of_mem_edist
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (h x hx)⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by rw [edist_comm, edist_dist]; exact ENNReal.ofReal_le_ofReal (h x hx)⟩

namespace PolynomialGraphSelections

variable {a m κ : ℕ} {F : PolynomialBasicClosedFormat a} {p : BoundedPolynomialMap a m}
  (P : PolynomialGraphSelections F p κ)

theorem eventually_output_defect_le (hFbound : F.source ⊆ closedBall 0 3)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ z ∈ P.selection j,
      dist (p.eval (coordinateProjection (Fin.castAdd m) z))
        (coordinateProjection (Fin.natAdd a) z) ≤ ε := by
  have hu := (isCompact_closedBall (0 : RealEuclidean a) 4).uniformContinuousOn_of_continuous
    p.contDiff_eval.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu (ε / 2) (by positivity)
  have ht : ∀ᶠ j in atTop, lrtTolerance j < min δ (ε / 2) :=
    tendsto_lrtTolerance.eventually (gt_mem_nhds (lt_min hδ (by positivity)))
  filter_upwards [ht] with j hj
  intro z hz
  obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := P.proximity j hz
  have hfirst := dist_coordinateProjection_le (Fin.castAdd m) (Fin.castAdd_injective _ _) z
    (euclideanPair s (p.eval s))
  have hlast := dist_coordinateProjection_le (Fin.natAdd a) (Fin.natAdd_injective _ _) z
    (euclideanPair s (p.eval s))
  simp only [coordinateProjection_pair_left, dist_eq_norm] at hfirst
  simp only [coordinateProjection_pair_right, dist_eq_norm] at hlast
  have hs4 : s ∈ closedBall (0 : RealEuclidean a) 4 :=
    (closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 4)) (hFbound hs)
  have hp := hmod (coordinateProjection (Fin.castAdd m) z) (P.sourceBound j ⟨z, hz, rfl⟩)
    s hs4 (by rw [dist_eq_norm]; exact (hfirst.trans hzs).trans (lt_min_iff.mp hj).1.le)
  calc
    _ ≤ dist (p.eval (coordinateProjection (Fin.castAdd m) z)) (p.eval s) +
        dist (p.eval s) (coordinateProjection (Fin.natAdd a) z) := dist_triangle _ _ _
    _ ≤ ε / 2 + lrtTolerance j := add_le_add hp (by rw [dist_comm, dist_eq_norm]; exact hlast.trans hzs)
    _ ≤ ε := by have := (lt_min_iff.mp hj).2; linarith

theorem tendsto_image_output_hausdorffEDist (hFbound : F.source ⊆ closedBall 0 3) :
    Tendsto (fun j => hausdorffEDist (p.eval '' P.source j)
      (coordinateProjection (Fin.natAdd a) '' P.selection j)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  filter_upwards [P.eventually_output_defect_le hFbound hrpos] with j hj
  have h := hausdorffEDist_images_le_of_dist_le (P.selection j)
    (p.eval ∘ coordinateProjection (Fin.castAdd m)) (coordinateProjection (Fin.natAdd a)) hj
  have hre : ENNReal.ofReal (r : ℝ) ≤ ε := by simpa using hrε.le
  simpa only [source, image_image, Function.comp_def] using h.trans hre

theorem tendsto_image_hausdorffEDist (hFbound : F.source ⊆ closedBall 0 3) :
    Tendsto (fun j => hausdorffEDist (p.eval '' P.source j) (p.eval '' F.source)) atTop (𝓝 0) := by
  have hτ : Tendsto (fun j => ENNReal.ofReal (lrtTolerance j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_lrtTolerance
  have hsum := (P.tendsto_image_output_hausdorffEDist hFbound).add hτ
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun j => ?_)
  exact hausdorffEDist_triangle.trans (add_le_add le_rfl (P.outputApprox j))

end PolynomialGraphSelections

end NLQCLean
end
