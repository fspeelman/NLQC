import NLQCLean.Geometry.PolynomialThickening
import NLQCLean.Approx.WitnessJacobianBound

/-!
# The thickened witness family

Nine constraints of degree at most twelve, a map of degree at most
eighteen, and the full ambient Jacobian on the exact compact source.
These facts are unconditional; the geometric input is applied separately.
-/

namespace NLQCLean.ReverseBlocks

variable {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d)

noncomputable def thickenedWitnessFormat (δ : ℝ) :
    PolynomialBasicClosedFormat (witnessCoordinateBudget d K + 2 * d ^ 4) :=
  (witnessFormat s hd δ).thicken (2 * d ^ 4) (by change 7 + 1 + 1 ≤ 20; decide)

noncomputable def thickenedWitnessPolynomial (c : ℝ) :
    BoundedPolynomialMap (witnessCoordinateBudget d K + 2 * d ^ 4) (2 * d ^ 4) :=
  (coordinateOverlapPolynomial s hd).thicken c

theorem thickenedWitnessFormat_constraint_count (δ : ℝ) :
    (thickenedWitnessFormat s hd δ).numEquations +
      (thickenedWitnessFormat s hd δ).numInequalities = 9 := rfl

theorem thickenedWitnessFormat_equations_degree (δ : ℝ) (i) :
    ((thickenedWitnessFormat s hd δ).equations i).totalDegree ≤ 12 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans
    (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).1

theorem thickenedWitnessFormat_inequalities_degree (δ : ℝ)
    (i : Fin (thickenedWitnessFormat s hd δ).numInequalities) :
    ((thickenedWitnessFormat s hd δ).inequalities i).totalDegree ≤ 12 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (thickeningBallPolynomial_degree _ _).trans (by decide)
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).1

theorem thickenedWitnessPolynomial_degree (c : ℝ) (j) :
    ((thickenedWitnessPolynomial s hd c).coordinates j).totalDegree ≤ 18 :=
  (coordinateOverlapPolynomial s hd).thicken_degree c (by decide)
    (fun i => (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd i)).1) j

theorem isCompact_thickenedWitnessFormat_source (δ : ℝ) :
    IsCompact (thickenedWitnessFormat s hd δ).source :=
  (witnessFormat s hd δ).isCompact_thicken_source _
    (fun _ hx => (norm_mem_witnessFormat_source s hd δ hx).le)

theorem thickenedWitnessFormat_source_radius (δ : ℝ) :
    (thickenedWitnessFormat s hd δ).source ⊆ Metric.closedBall 0 3 :=
  (witnessFormat s hd δ).thicken_source_radius _
    (fun _ hx => (norm_mem_witnessFormat_source s hd δ hx).le)

theorem norm_mem_thickenedWitnessFormat_source_le (δ : ℝ)
    {z : RealEuclidean (witnessCoordinateBudget d K + 2 * d ^ 4)}
    (hz : z ∈ (thickenedWitnessFormat s hd δ).source) : ‖z‖ ≤ Real.sqrt 7 :=
  (witnessFormat s hd δ).norm_mem_thicken_source_le_sqrt_seven _
    (fun _ hx => (norm_mem_witnessFormat_source s hd δ hx).le) hz

theorem hasFDerivAt_thickenedWitnessPolynomial (c : ℝ)
    (z : RealEuclidean (witnessCoordinateBudget d K + 2 * d ^ 4)) :
    HasFDerivAt (thickenedWitnessPolynomial s hd c).eval
      (thickenedLinearMap (fderiv ℝ (coordinateOverlapPolynomial s hd).eval
        (euclideanProductCoordinates _ _ z).fst) c) z := by
  apply BoundedPolynomialMap.hasFDerivAt_thicken
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact ((contDiff_coordinateOverlap s hd).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- The top Jacobian of the thickened polynomial. -/
theorem thickenedWitnessPolynomial_jacobian_le (hd2 : 2 ≤ d)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    {z : RealEuclidean (witnessCoordinateBudget d K + 2 * d ^ 4)}
    (hz : z ∈ (thickenedWitnessFormat s hd δ).source) :
    topRealJacobian (fderiv ℝ (thickenedWitnessPolynomial s hd c).eval z) ≤
      ((witnessCoordinateBudget d K : ℝ) + c) ^ (4 * d ^ 2 - 3) *
        (δ * witnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (4 * d ^ 2 - 3)) := by
  rw [(hasFDerivAt_thickenedWitnessPolynomial s hd c z).fderiv]
  exact witnessFormat_thickenedJacobian_le s hd hd2 hδ hδ1 hc
    (((witnessFormat s hd δ).mem_thicken_source _ z).mp hz).1

end NLQCLean.ReverseBlocks
