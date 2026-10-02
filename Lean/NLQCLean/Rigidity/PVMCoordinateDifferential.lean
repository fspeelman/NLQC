import NLQCLean.Rigidity.PVMExtendedDifferential

/-!
# PVM ambient rank and leakage in padded Euclidean coordinates

Transport the explicit real-linear terms through the fixed
coordinate maps. The full ambient derivative has rank-(3d²−2) motion plus
error of operator norm at most δP, with no rank hypothesis.
-/

namespace NLQCLean
namespace PVMReverseBlocks
open Matrix
open scoped Matrix.Norms.Frobenius
variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

/-- Transport the explicit local term by the fixed coordinate maps. -/
noncomputable def coordinateLocalTerm (x : RealEuclidean P) :
    RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd hfloor hP x)).comp (decodeCoordinates s hd hfloor hP))).toContinuousLinearMap

/-- Transport the explicit error term by the same fixed coordinate maps. -/
noncomputable def coordinateResidual (x : RealEuclidean P) :
    RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedResidual (decodeCoordinates s hd hfloor hP x)).comp (decodeCoordinates s hd hfloor hP))).toContinuousLinearMap

theorem fderiv_coordinateOverlap_decomposition (x : RealEuclidean P) :
    fderiv ℝ (coordinateOverlap s hd hfloor hP) x = coordinateLocalTerm s hd hfloor hP x + coordinateResidual s hd hfloor hP x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_coordinateOverlap_apply]
  change overlapOutputCoordinates d (fderiv ℝ extendedOverlap (decodeCoordinates s hd hfloor hP x)
    (decodeCoordinates s hd hfloor hP v)) =
      overlapOutputCoordinates d (extendedLocalTerm (decodeCoordinates s hd hfloor hP x) (decodeCoordinates s hd hfloor hP v)) +
        overlapOutputCoordinates d (extendedResidual (decodeCoordinates s hd hfloor hP x) (decodeCoordinates s hd hfloor hP v))
  rw [← map_add]
  congr 1
  exact congrArg (fun L => L (decodeCoordinates s hd hfloor hP v))
    (fderiv_extendedOverlap_decomposition (decodeCoordinates s hd hfloor hP x))

theorem finrank_coordinateLocalTerm_le {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) :
    Module.finrank ℝ (LinearMap.range (coordinateLocalTerm s hd hfloor hP x).toLinearMap) ≤ 3 * d ^ 2 - 2 := by
  change Module.finrank ℝ (LinearMap.range ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd hfloor hP x)).comp (decodeCoordinates s hd hfloor hP)))) ≤ _
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (finrank_extendedLocalTerm_le hx hd))

theorem norm_coordinateResidual_le_budget (hd2 : 2 ≤ d)
    {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ‖coordinateResidual s hd hfloor hP x‖ ≤ δ * P := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (Nat.cast_nonneg _))
  intro v
  change ‖overlapOutputCoordinates d
    (extendedResidual (decodeCoordinates s hd hfloor hP x) (decodeCoordinates s hd hfloor hP v))‖ ≤ _
  rw [norm_overlapOutputCoordinates]
  exact (norm_extendedResidual_le_budget hx hd2 hfloor hP hδ hdef _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd hfloor hP v)
      (mul_nonneg hδ (Nat.cast_nonneg _)))

/-- TP7's ambient rank-plus-small-error statement on the common Euclidean spaces. -/
theorem exists_coordinateOverlap_rank_error_decomposition (hd2 : 2 ≤ d)
    {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlap s hd hfloor hP) x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 3 * d ^ 2 - 2 ∧
      ‖fderiv ℝ (coordinateOverlap s hd hfloor hP) x‖ ≤ (P : ℝ) ∧
      ‖R‖ ≤ δ * P :=
  ⟨coordinateLocalTerm s hd hfloor hP x, coordinateResidual s hd hfloor hP x, fderiv_coordinateOverlap_decomposition s hd hfloor hP x,
    finrank_coordinateLocalTerm_le s hd hfloor hP hx, norm_fderiv_coordinateOverlap_le_budget s hd hfloor hP hd2 hx,
    norm_coordinateResidual_le_budget s hd hfloor hP hd2 hx hδ hdef⟩

end PVMReverseBlocks
end NLQCLean
