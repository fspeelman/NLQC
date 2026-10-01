import NLQCLean.Approx.PVMWitnessJacobianBound
import NLQCLean.Geometry.SingularValueRankBound

/-!
# Singular values of the ambient PVM witness derivative

Mathlib indexes singular values from zero: index 0 is σ₁,
and index 3d²−2 is σ_(3d²−1). The bounds hold at every point of the
exact polynomial source, for the full Euclidean ambient derivative.
-/

namespace NLQCLean.PVMReverseBlocks

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)

/-- The first singular value of the evaluated polynomial derivative. -/
theorem witnessFormat_singularValues_zero_le (hd2 : 2 ≤ d) {δ : ℝ}
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd hfloor δ).source) :
    (fderiv ℝ (coordinateOverlapPolynomial s hd hfloor).eval x).toLinearMap.singularValues 0 ≤
      pvmWitnessCoordinateBudget d K :=
  (singularValues_zero_le_norm _).trans (witnessFormat_ambient_norm_le s hd hfloor hd2 hx)

/-- The first transverse singular value, following all 3d²−2 motion directions. -/
theorem witnessFormat_singularValues_tail_le (hd2 : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd hfloor δ).source) :
    (fderiv ℝ (coordinateOverlapPolynomial s hd hfloor).eval x).toLinearMap.singularValues
      (3 * d ^ 2 - 2) ≤ δ * pvmWitnessCoordinateBudget d K := by
  obtain ⟨T, R, he, ht, _, hr⟩ := witnessFormat_ambient_rank_error s hd hfloor hd2 hδ hx
  exact singularValues_le_of_eq_add_of_finrank_range_le _ T R he ht hr (by positivity)

end NLQCLean.PVMReverseBlocks
