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
variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)

/-- Transport the explicit local term by the fixed coordinate maps. -/
noncomputable def coordinateLocalTerm (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    RealEuclidean (pvmWitnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd hfloor x)).comp (decodeCoordinates s hd hfloor))).toContinuousLinearMap

/-- Transport the explicit error term by the same fixed coordinate maps. -/
noncomputable def coordinateResidual (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    RealEuclidean (pvmWitnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedResidual (decodeCoordinates s hd hfloor x)).comp (decodeCoordinates s hd hfloor))).toContinuousLinearMap

theorem fderiv_coordinateOverlap_decomposition (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    fderiv ℝ (coordinateOverlap s hd hfloor) x = coordinateLocalTerm s hd hfloor x + coordinateResidual s hd hfloor x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_coordinateOverlap_apply]
  change overlapOutputCoordinates d (fderiv ℝ extendedOverlap (decodeCoordinates s hd hfloor x)
    (decodeCoordinates s hd hfloor v)) =
      overlapOutputCoordinates d (extendedLocalTerm (decodeCoordinates s hd hfloor x) (decodeCoordinates s hd hfloor v)) +
        overlapOutputCoordinates d (extendedResidual (decodeCoordinates s hd hfloor x) (decodeCoordinates s hd hfloor v))
  rw [← map_add]
  congr 1
  exact congrArg (fun L => L (decodeCoordinates s hd hfloor v))
    (fderiv_extendedOverlap_decomposition (decodeCoordinates s hd hfloor x))

theorem finrank_coordinateLocalTerm_le {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor x))) :
    Module.finrank ℝ (LinearMap.range (coordinateLocalTerm s hd hfloor x).toLinearMap) ≤ 3 * d ^ 2 - 2 := by
  change Module.finrank ℝ (LinearMap.range ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd hfloor x)).comp (decodeCoordinates s hd hfloor)))) ≤ _
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (finrank_extendedLocalTerm_le hx hd))

theorem norm_coordinateResidual_le_budget (hd2 : 2 ≤ d)
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ‖coordinateResidual s hd hfloor x‖ ≤ δ * pvmWitnessCoordinateBudget d K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (Nat.cast_nonneg _))
  intro v
  change ‖overlapOutputCoordinates d
    (extendedResidual (decodeCoordinates s hd hfloor x) (decodeCoordinates s hd hfloor v))‖ ≤ _
  rw [norm_overlapOutputCoordinates]
  exact (norm_extendedResidual_le_budget hx hd2 hfloor hδ hdef _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd hfloor v)
      (mul_nonneg hδ (Nat.cast_nonneg _)))

/-- TP7's ambient rank-plus-small-error statement on the common Euclidean spaces. -/
theorem exists_coordinateOverlap_rank_error_decomposition (hd2 : 2 ≤ d)
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : RealEuclidean (pvmWitnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlap s hd hfloor) x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 3 * d ^ 2 - 2 ∧
      ‖fderiv ℝ (coordinateOverlap s hd hfloor) x‖ ≤ (pvmWitnessCoordinateBudget d K : ℝ) ∧
      ‖R‖ ≤ δ * pvmWitnessCoordinateBudget d K :=
  ⟨coordinateLocalTerm s hd hfloor x, coordinateResidual s hd hfloor x, fderiv_coordinateOverlap_decomposition s hd hfloor x,
    finrank_coordinateLocalTerm_le s hd hfloor hx, norm_fderiv_coordinateOverlap_le_budget s hd hfloor hd2 hx,
    norm_coordinateResidual_le_budget s hd hfloor hd2 hx hδ hdef⟩

end PVMReverseBlocks
end NLQCLean
