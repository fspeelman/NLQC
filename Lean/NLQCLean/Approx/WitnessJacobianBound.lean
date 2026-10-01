import NLQCLean.Approx.PolynomialWitnessFamily
import NLQCLean.Geometry.ThickenedJacobian

/-!
# The thickened witness Jacobian bound

The polynomial witness derivative
has the claimed full target-dimensional Jacobian bound after thickening.
The image-volume property is not an argument to this theorem.
-/

namespace NLQCLean

theorem localMotionRank_le_ambientDimension {d : ℕ} (hd : 2 ≤ d) :
    4 * d ^ 2 - 3 ≤ 2 * d ^ 4 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have hp : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  rw [hp]
  have hm : 4 * d ^ 2 ≤ 2 * (d ^ 2 * d ^ 2) := by nlinarith
  exact (Nat.sub_le _ _).trans hm

namespace ReverseBlocks

/-- The Jacobian bound on every source point, in the top-Jacobian convention. -/
theorem witnessFormat_thickenedJacobian_le {d K : ℕ} (s : ReverseShape d K)
    (hd : 0 < d) (hd2 : 2 ≤ d) {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd δ).source) :
    topRealJacobian (thickenedLinearMap (fderiv ℝ (coordinateOverlapPolynomial s hd).eval x) c) ≤
      ((witnessCoordinateBudget d K : ℝ) + c) ^ (4 * d ^ 2 - 3) *
        (δ * witnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (4 * d ^ 2 - 3)) := by
  obtain ⟨T, R, he, ht, hn, hr⟩ := witnessFormat_ambient_rank_error s hd hd2 hδ hx
  exact topRealJacobian_thickenedLinearMap_le _ T R he
    (Λ := (witnessCoordinateBudget d K : ℝ)) (μ := δ * witnessCoordinateBudget d K)
    (by positivity) (by nlinarith [show 0 ≤ (witnessCoordinateBudget d K : ℝ) by positivity]) hc hn hr ht
    (localMotionRank_le_ambientDimension hd2)

end ReverseBlocks
end NLQCLean
