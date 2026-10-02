import NLQCLean.Geometry.PolynomialThickening
import NLQCLean.Approx.PVMWitnessJacobianBound

/-!
# The thickened witness family

Nine constraints of degree at most twelve, a map of degree at most
eighteen, and the full ambient Jacobian on the exact compact source.
These facts are unconditional; the geometric input is applied separately.
-/

namespace NLQCLean.PVMReverseBlocks

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

noncomputable def thickenedWitnessFormat (δ : ℝ) :
    PolynomialBasicClosedFormat (P + 2 * d ^ 4) :=
  (witnessFormat s hd hfloor hP δ).thicken (2 * d ^ 4) (by change 7 + 1 + 1 ≤ 20; decide)

noncomputable def thickenedWitnessPolynomial (c : ℝ) :
    BoundedPolynomialMap (P + 2 * d ^ 4) (2 * d ^ 4) :=
  (coordinateOverlapPolynomial s hd hfloor hP).thicken c

theorem thickenedWitnessFormat_constraint_count (δ : ℝ) :
    (thickenedWitnessFormat s hd hfloor hP δ).numEquations +
      (thickenedWitnessFormat s hd hfloor hP δ).numInequalities = 9 := rfl

theorem thickenedWitnessFormat_equations_degree (δ : ℝ) (i) :
    ((thickenedWitnessFormat s hd hfloor hP δ).equations i).totalDegree ≤ 12 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans
    (Classical.choose_spec (polynomialDegree_witnessEquations s hd hfloor hP i)).1

theorem thickenedWitnessFormat_inequalities_degree (δ : ℝ)
    (i : Fin (thickenedWitnessFormat s hd hfloor hP δ).numInequalities) :
    ((thickenedWitnessFormat s hd hfloor hP δ).inequalities i).totalDegree ≤ 12 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (thickeningBallPolynomial_degree _ _).trans (by decide)
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (Classical.choose_spec (polynomialDegree_witnessInequality s hd hfloor hP δ)).1

theorem thickenedWitnessPolynomial_degree (c : ℝ) (j) :
    ((thickenedWitnessPolynomial s hd hfloor hP c).coordinates j).totalDegree ≤ 18 :=
  (coordinateOverlapPolynomial s hd hfloor hP).thicken_degree c (by decide)
    (fun i => (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd hfloor hP i)).1) j

theorem isCompact_thickenedWitnessFormat_source (δ : ℝ) :
    IsCompact (thickenedWitnessFormat s hd hfloor hP δ).source :=
  (witnessFormat s hd hfloor hP δ).isCompact_thicken_source _
    (fun _ hx => (norm_mem_witnessFormat_source s hd hfloor hP δ hx).le)

theorem thickenedWitnessFormat_source_radius (δ : ℝ) :
    (thickenedWitnessFormat s hd hfloor hP δ).source ⊆ Metric.closedBall 0 3 :=
  (witnessFormat s hd hfloor hP δ).thicken_source_radius _
    (fun _ hx => (norm_mem_witnessFormat_source s hd hfloor hP δ hx).le)

theorem norm_mem_thickenedWitnessFormat_source_le (δ : ℝ)
    {z : RealEuclidean (P + 2 * d ^ 4)}
    (hz : z ∈ (thickenedWitnessFormat s hd hfloor hP δ).source) : ‖z‖ ≤ Real.sqrt 7 :=
  (witnessFormat s hd hfloor hP δ).norm_mem_thicken_source_le_sqrt_seven _
    (fun _ hx => (norm_mem_witnessFormat_source s hd hfloor hP δ hx).le) hz

theorem hasFDerivAt_thickenedWitnessPolynomial (c : ℝ)
    (z : RealEuclidean (P + 2 * d ^ 4)) :
    HasFDerivAt (thickenedWitnessPolynomial s hd hfloor hP c).eval
      (thickenedLinearMap (fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval
        (euclideanProductCoordinates _ _ z).fst) c) z := by
  apply BoundedPolynomialMap.hasFDerivAt_thicken
  have he : (coordinateOverlapPolynomial s hd hfloor hP).eval = coordinateOverlap s hd hfloor hP :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor hP)
  rw [he]
  exact ((contDiff_coordinateOverlap s hd hfloor hP).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- The top Jacobian of the thickened polynomial. -/
theorem thickenedWitnessPolynomial_jacobian_le (hd2 : 2 ≤ d)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    {z : RealEuclidean (P + 2 * d ^ 4)}
    (hz : z ∈ (thickenedWitnessFormat s hd hfloor hP δ).source) :
    topRealJacobian (fderiv ℝ (thickenedWitnessPolynomial s hd hfloor hP c).eval z) ≤
      ((P : ℝ) + c) ^ (3 * d ^ 2 - 2) *
        (δ * P + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2)) := by
  rw [(hasFDerivAt_thickenedWitnessPolynomial s hd hfloor hP c z).fderiv]
  exact witnessFormat_thickenedJacobian_le s hd hfloor hP hd2 hδ hδ1 hc
    (((witnessFormat s hd hfloor hP δ).mem_thicken_source _ z).mp hz).1

end NLQCLean.PVMReverseBlocks
