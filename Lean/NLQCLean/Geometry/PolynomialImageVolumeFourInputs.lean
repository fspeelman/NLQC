/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.LRTVolumeConstants
import NLQCLean.Geometry.LRTImageConvergence
import NLQCLean.Geometry.JacobianNeighborhood
import NLQCLean.Semialgebraic.ProjectedFiberCards

/-!
# Polynomial image-volume bounds from four external inputs

Apply the coordinate-graph volume estimate to compact polynomial graph
selections with almost-everywhere finite coordinate fibers, then pass to
the limit. The constant `lrtSelectionVolumeBase κ` is uniform in the
dimensions. The explicit inputs are LRT, projection closure, smooth
stratification and the component bound.
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

namespace PolynomialGraphSelections

variable {a m κ : ℕ} {F : PolynomialBasicClosedFormat a} {p : BoundedPolynomialMap a m}
  (P : PolynomialGraphSelections F p κ)

theorem ae_card_coordinateFiber_le_of_external
    (hComponents : SemialgebraicComponentBoundTheorem)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem) (hκ : 1 ≤ κ)
    (j : ℕ) (I : Fin m → Fin a) :
    ∀ᵐ y, (semialgebraicMapFiber (P.source j) (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber (P.source j) (coordinateProjection I) y) ≤
        componentFormatBase (2 * κ) (max (κ * 200) 2) ^ (a + m) :=
  (P.format j).ae_card_projected_coordinateFiber_le_of_stratification hComponents hProjection
    hStratification hκ (Fin.castAdd m) I (P.sourceDimension j)

include P in
theorem image_volume_le (hκ : 1 ≤ κ)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem)
    (hF : IsCompact F.source) (hFbound : F.source ⊆ closedBall 0 3)
    {B : ℝ} (hB : 0 ≤ B)
    (hJ : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B) :
    volume (p.eval '' F.source) ≤
      ENNReal.ofReal (lrtSelectionVolumeBase κ ^ (a + m)) * euclideanUnitBallVolume m * ENNReal.ofReal B := by
  have hη (η : ℝ) (hη : 0 < η) : volume (p.eval '' F.source) ≤
      ENNReal.ofReal (lrtSelectionVolumeBase κ ^ (a + m)) * euclideanUnitBallVolume m *
        ENNReal.ofReal (B + η) := by
    apply le_of_tendsto (P.tendsto_image_volume hProjection hF hFbound)
    filter_upwards [P.eventually_topRealJacobian_le hF hJ hη] with j hj
    have hvol := semialgebraic_image_volume_le hStratification (P.sourceSemialgebraic j)
      (P.sourceDimension j) (by norm_num : (0 : ℝ) ≤ 4) (P.sourceBound j)
      (lrtSelectionComponentBase κ ^ (a + m))
      (fun I _ => P.ae_card_coordinateFiber_le_of_external hComponents hProjection hStratification hκ j I)
      p.eval isOpen_univ (subset_univ _) p.contDiff_eval.contDiffOn (add_nonneg hB hη.le) hj
    exact hvol.trans_eq (lrt_selection_volume_constant_eq κ a m (B + η))
  have hK : ENNReal.ofReal (lrtSelectionVolumeBase κ ^ (a + m)) * euclideanUnitBallVolume m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (euclideanUnitBallVolume_ne_top m)
  have hlim : Tendsto (fun j => ENNReal.ofReal (B + lrtTolerance j)) atTop (𝓝 (ENNReal.ofReal B)) := by
    have hT : Tendsto (fun j => B + lrtTolerance j) atTop (𝓝 B) := by
      simpa only [add_zero] using tendsto_lrtTolerance.const_add B
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto B).comp hT
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr hK))
    (fun j => hη (lrtTolerance j) (lrtTolerance_pos j))

end PolynomialGraphSelections

/-- The canonical image-volume consequence of the four audited external contracts. -/
theorem polynomialImageVolumeBound_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) : PolynomialImageVolumeBound := by
  obtain ⟨κ, hκ, hchoices⟩ := exists_polynomialGraphSelections hLRT hProjection
  refine ⟨lrtSelectionVolumeBase κ, lrtSelectionVolumeBase_ge_one κ, ?_⟩
  intro a m _ha hm F p hF hFbound B hB hJ
  by_cases hne : F.source.Nonempty
  · by_cases ham : m ≤ a
    · obtain ⟨P⟩ := hchoices a m hm F p hF hne hFbound
      exact P.image_volume_le hκ hProjection hStratification hComponents hF hFbound hB hJ
    · rw [p.volume_image_eq_zero_of_dimension_lt F.source (Nat.lt_of_not_ge ham)]
      exact bot_le
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty, measure_empty]
    exact bot_le

end NLQCLean
end
