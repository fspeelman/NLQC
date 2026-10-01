/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.LRTSelectionHausdorff
import NLQCLean.Semialgebraic.ParametricFormat
import NLQCLean.Semialgebraic.FormatVolumeContinuity

/-!
# Volume convergence of the LRT selection images

Retain coefficient parameters before projection to obtain
one format bound for the fixed polynomial image sequence, then apply volume continuity.
Neither joint definability nor coefficient bounds are required.
-/

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace NLQCLean

theorem polynomialMap_source_lift {a m : ℕ} (p : BoundedPolynomialMap a m)
    (z : RealEuclidean (a + m)) :
    PolynomialSignDNF.polynomialMap (fun j => MvPolynomial.rename (Fin.castAdd m) (p.coordinates j)) z =
      p.eval (coordinateProjection (Fin.castAdd m) z) := by
  ext j
  simp only [PolynomialSignDNF.polynomialMap, BoundedPolynomialMap.eval,
    MvPolynomial.eval_rename, coordinateProjection_apply, Function.comp_def]

namespace PolynomialGraphSelections

variable {a m κ : ℕ} {F : PolynomialBasicClosedFormat a} {p : BoundedPolynomialMap a m}
  (P : PolynomialGraphSelections F p κ)

theorem exists_uniform_image_format (hProjection : SemialgebraicProjectionTheorem) :
    ∃ c D : ℕ, ∀ j, HasSemialgebraicFormat (p.eval '' P.source j) c D := by
  obtain ⟨c, D, hfmt⟩ := NLQCLean.exists_uniform_image_format hProjection κ (κ * 200)
    (fun j => MvPolynomial.rename (Fin.castAdd m) (p.coordinates j))
  refine ⟨c, D, fun j => ?_⟩
  have heq : PolynomialSignDNF.polynomialMap
      (fun j => MvPolynomial.rename (Fin.castAdd m) (p.coordinates j)) '' P.selection j =
        p.eval '' P.source j := by
    simp only [source, image_image, polynomialMap_source_lift]
  rw [← heq]
  exact hfmt (P.selection j) (P.format j)

theorem exists_image_ball : ∃ R : ℝ, ∀ j, p.eval '' P.source j ⊆ closedBall 0 R := by
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : RealEuclidean a) 4).image
    p.contDiff_eval.continuous).isBounded.exists_norm_le
  refine ⟨R, ?_⟩
  rintro j y ⟨x, hx, rfl⟩
  simpa only [mem_closedBall, dist_zero_right] using hR _ ⟨x, P.sourceBound j hx, rfl⟩

theorem tendsto_image_volume (hProjection : SemialgebraicProjectionTheorem)
    (hF : IsCompact F.source) (hFbound : F.source ⊆ closedBall 0 3) :
    Tendsto (fun j => volume (p.eval '' P.source j)) atTop (𝓝 (volume (p.eval '' F.source))) := by
  obtain ⟨c, D, hfmt⟩ := P.exists_uniform_image_format hProjection
  obtain ⟨R, hR⟩ := P.exists_image_ball
  exact tendsto_volume_of_bounded_format_hausdorff _ _
    (fun j => (P.source_isCompact j).image p.contDiff_eval.continuous)
    (hF.image p.contDiff_eval.continuous).isClosed hfmt R hR (P.tendsto_image_hausdorffEDist hFbound)

theorem tendsto_image_realVolume (hProjection : SemialgebraicProjectionTheorem)
    (hF : IsCompact F.source) (hFbound : F.source ⊆ closedBall 0 3) :
    Tendsto (fun j => (volume (p.eval '' P.source j)).toReal) atTop
      (𝓝 (volume (p.eval '' F.source)).toReal) :=
  (ENNReal.continuousAt_toReal (hF.image p.contDiff_eval.continuous).measure_lt_top.ne).tendsto.comp
    (P.tendsto_image_volume hProjection hF hFbound)

end PolynomialGraphSelections

end NLQCLean
end
