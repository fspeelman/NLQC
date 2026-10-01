import NLQCLean.Invariants.PurityEstimates
import NLQCLean.Approx.PolynomialWitnessCoverage
import NLQCLean.Models.MixedReachability
import NLQCLean.Geometry.PolynomialThickening

/-!
# A scalar purity witness for two-qubit targets

The full ambient derivative uses the local-motion term of the cubic
extension. Purity kills that term at arbitrary overlap matrices; only the
bounded leakage residual remains.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- One Euclidean coordinate for a real scalar. -/
noncomputable def scalarEuclidean : ℝ →ₗ[ℝ] RealEuclidean 1 where
  toFun t := WithLp.toLp 2 (fun _ => t)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] theorem scalarEuclidean_apply (t : ℝ) (i : Fin 1) : scalarEuclidean t i = t := rfl

@[simp] theorem norm_scalarEuclidean (t : ℝ) : ‖scalarEuclidean t‖ = ‖t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]

namespace ReverseBlocks

variable {K : ℕ} (s : ReverseShape 2 K)

/-- The normalized purity of the globally extended overlap. -/
noncomputable def coordinatePurity (x : RealEuclidean (witnessCoordinateBudget 2 K)) : ℝ :=
  purity (1 / 16) (extendedOverlap (decodeCoordinates s (by decide) x))

theorem contDiff_coordinatePurity :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coordinatePurity s) := by
  let D := (decodeCoordinates s (by decide)).toContinuousLinearMap
  exact ContDiff.purity (1 / 16) (contDiff_extendedOverlap.comp D.contDiff)

theorem polynomialDegree_coordinatePurity : RealPolynomialDegreeLE 72 (coordinatePurity s) :=
  polynomialDegree_purity (polynomialDegree_extendedOverlap s (by decide)) (1 / 16)

theorem fderiv_coordinatePurity_apply
    (x v : RealEuclidean (witnessCoordinateBudget 2 K)) :
    fderiv ℝ (coordinatePurity s) x v =
      fderiv ℝ (purity (1 / 16)) (extendedOverlap (decodeCoordinates s (by decide) x))
        (fderiv ℝ extendedOverlap (decodeCoordinates s (by decide) x)
          (decodeCoordinates s (by decide) v)) := by
  let D := (decodeCoordinates s (by decide)).toContinuousLinearMap
  have hH := (contDiff_extendedOverlap.differentiable (by simp)).differentiableAt
    (x := D x)
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (purity (ι := Fin 2) (1 / 16)) :=
    ContDiff.purity (1 / 16) contDiff_id
  have hP := (hc.differentiable (by simp)).differentiableAt (x := extendedOverlap (D x))
  have h := congrArg (fun L => L v) (hP.hasFDerivAt.comp x (hH.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

/-- The overlap of two isometries is inside the radius-two Frobenius ball. -/
theorem IsValid.qubit_norm_overlap_le {x : ReverseBlocks s} (hx : IsValid x) :
    ‖overlap x‖ ≤ 2 := by
  have hA : ‖forward x‖ = 2 := by
    have h := hx.isIsometry_forward.frobNorm_sq_eq_card
    norm_num [Fintype.card_prod] at h
    nlinarith [norm_nonneg (forward x)]
  calc
    ‖overlap x‖ ≤ opNorm (reverse x)ᴴ * ‖forward x‖ := frobNorm_mul_le _ _
    _ ≤ 1 * ‖forward x‖ := by
      rw [opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right hx.isIsometry_reverse.opNorm_le_one (norm_nonneg _)
    _ = 2 := by rw [one_mul, hA]

/-- Local-motion cancellation for every ambient projected direction. -/
theorem fderiv_purity_extendedLocalTerm_eq_zero {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (v : ReverseBlocks s) :
    fderiv ℝ (purity (1 / 16)) (extendedOverlap x) (extendedLocalTerm x v) = 0 := by
  have ht := isTangent_rescaled_fderiv_normalizedCubicBlocks hx (by decide) v
  rw [extendedOverlap_eq_overlap hx (by decide), extendedLocalTerm_apply]
  exact fderiv_purity_localSkew_eq_zero (1 / 16) _
    (hx.forward_generator_mem_localSkew ht) (hx.reverse_generator_mem_localSkew ht)

/-- The full derivative depends only on the explicit leakage residual. -/
theorem fderiv_coordinatePurity_eq_residual
    {x : RealEuclidean (witnessCoordinateBudget 2 K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s (by decide) x)))
    (v : RealEuclidean (witnessCoordinateBudget 2 K)) :
    fderiv ℝ (coordinatePurity s) x v =
      fderiv ℝ (purity (1 / 16)) (extendedOverlap (decodeCoordinates s (by decide) x))
        (extendedResidual (decodeCoordinates s (by decide) x) (decodeCoordinates s (by decide) v)) := by
  rw [fderiv_coordinatePurity_apply]
  have he := congrArg (fun L => L (decodeCoordinates s (by decide) v))
    (fderiv_extendedOverlap_decomposition (decodeCoordinates s (by decide) x))
  change fderiv ℝ extendedOverlap _ _ = extendedLocalTerm _ _ + extendedResidual _ _ at he
  rw [he, map_add, fderiv_purity_extendedLocalTerm_eq_zero s hx, zero_add]

/-- A small scalar leakage bounds the full ambient scalar derivative. -/
theorem norm_fderiv_coordinatePurity_apply_le {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean (witnessCoordinateBudget 2 K)}
    (hx : x ∈ (witnessFormat s (by decide) δ).source)
    (v : RealEuclidean (witnessCoordinateBudget 2 K)) :
    ‖fderiv ℝ (coordinatePurity s) x v‖ ≤
      2 * δ * (witnessCoordinateBudget 2 K : ℝ) * ‖v‖ := by
  obtain ⟨hv, _, hdef⟩ := (mem_witnessFormat_source_iff s (by decide) δ x).mp hx
  rw [fderiv_coordinatePurity_eq_residual s hv]
  have hn : ‖extendedOverlap (decodeCoordinates s (by decide) x)‖ ≤ 2 := by
    rw [extendedOverlap_eq_overlap hv (by decide)]
    exact hv.qubit_norm_overlap_le
  have hr := (norm_extendedResidual_le_budget hv (by decide) hδ hdef
    (decodeCoordinates s (by decide) v)).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s (by decide) v)
      (by positivity : 0 ≤ δ * (witnessCoordinateBudget 2 K : ℝ)))
  exact (norm_fderiv_qubit_purity_apply_le _ _ hn).trans
    ((mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- An one-coordinate polynomial, of degree at most seventy-two. -/
noncomputable def scalarPurityPolynomial :
    BoundedPolynomialMap (witnessCoordinateBudget 2 K) 1 where
  coordinates _ := Classical.choose (polynomialDegree_coordinatePurity s)
  degree_le _ := (Classical.choose_spec (polynomialDegree_coordinatePurity s)).1.trans (by decide)

theorem scalarPurityPolynomial_degree (i : Fin 1) :
    ((scalarPurityPolynomial s).coordinates i).totalDegree ≤ 72 :=
  (Classical.choose_spec (polynomialDegree_coordinatePurity s)).1

theorem scalarPurityPolynomial_eval (x : RealEuclidean (witnessCoordinateBudget 2 K)) :
    (scalarPurityPolynomial s).eval x = scalarEuclidean (coordinatePurity s x) := by
  ext i
  exact (Classical.choose_spec (polynomialDegree_coordinatePurity s)).2 x

theorem hasFDerivAt_scalarPurityPolynomial (x : RealEuclidean (witnessCoordinateBudget 2 K)) :
    HasFDerivAt (scalarPurityPolynomial s).eval
      (scalarEuclidean.toContinuousLinearMap.comp (fderiv ℝ (coordinatePurity s) x)) x := by
  have h := scalarEuclidean.toContinuousLinearMap.hasFDerivAt.comp x
    (((contDiff_coordinatePurity s).differentiable (by simp)) x).hasFDerivAt
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (scalarPurityPolynomial_eval s))

theorem norm_fderiv_scalarPurityPolynomial_le {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean (witnessCoordinateBudget 2 K)}
    (hx : x ∈ (witnessFormat s (by decide) δ).source) :
    ‖fderiv ℝ (scalarPurityPolynomial s).eval x‖ ≤
      2 * δ * (witnessCoordinateBudget 2 K : ℝ) := by
  rw [(hasFDerivAt_scalarPurityPolynomial s x).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖scalarEuclidean (fderiv ℝ (coordinatePurity s) x v)‖ ≤ _
  rw [norm_scalarEuclidean]
  exact norm_fderiv_coordinatePurity_apply_le s hδ hx v

/-- Add one unit-interval coordinate, retaining the exact witness constraints. -/
noncomputable def scalarPurityWitnessFormat (δ : ℝ) :
    PolynomialBasicClosedFormat (witnessCoordinateBudget 2 K + 1) :=
  (witnessFormat s (by decide) δ).thicken 1 (by change 7 + 1 + 1 ≤ 20; decide)

noncomputable def thickenedScalarPurityPolynomial (c : ℝ) :
    BoundedPolynomialMap (witnessCoordinateBudget 2 K + 1) 1 :=
  (scalarPurityPolynomial s).thicken c

theorem scalarPurityWitnessFormat_constraint_count (δ : ℝ) :
    (scalarPurityWitnessFormat s δ).numEquations +
      (scalarPurityWitnessFormat s δ).numInequalities = 9 := rfl

theorem thickenedScalarPurityPolynomial_degree (c : ℝ) (i : Fin 1) :
    ((thickenedScalarPurityPolynomial s c).coordinates i).totalDegree ≤ 72 :=
  (scalarPurityPolynomial s).thicken_degree c (by decide) (scalarPurityPolynomial_degree s) i

theorem isCompact_scalarPurityWitnessFormat_source (δ : ℝ) :
    IsCompact (scalarPurityWitnessFormat s δ).source :=
  (witnessFormat s (by decide) δ).isCompact_thicken_source _
    (fun _ hx => (norm_mem_witnessFormat_source s (by decide) δ hx).le)

theorem scalarPurityWitnessFormat_source_radius_lt_three (δ : ℝ)
    {z : RealEuclidean (witnessCoordinateBudget 2 K + 1)}
    (hz : z ∈ (scalarPurityWitnessFormat s δ).source) : ‖z‖ < 3 := by
  have h := (witnessFormat s (by decide) δ).norm_mem_thicken_source_le_sqrt_seven _
    (fun _ hx => (norm_mem_witnessFormat_source s (by decide) δ hx).le) hz
  have hs : Real.sqrt 7 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_nonneg (7 : ℝ)]
  exact h.trans_lt hs

theorem scalarPurityWitnessFormat_source_radius (δ : ℝ) :
    (scalarPurityWitnessFormat s δ).source ⊆ Metric.closedBall 0 3 := by
  intro z hz
  simpa using (scalarPurityWitnessFormat_source_radius_lt_three s δ hz).le

theorem thickenedScalarPurityPolynomial_jacobian_le {δ c : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    {z : RealEuclidean (witnessCoordinateBudget 2 K + 1)}
    (hz : z ∈ (scalarPurityWitnessFormat s δ).source) :
    topRealJacobian (fderiv ℝ (thickenedScalarPurityPolynomial s c).eval z) ≤
      2 * δ * (witnessCoordinateBudget 2 K : ℝ) + c := by
  let x := (euclideanProductCoordinates (witnessCoordinateBudget 2 K) 1 z).fst
  have hx : x ∈ (witnessFormat s (by decide) δ).source :=
    (((witnessFormat s (by decide) δ).mem_thicken_source _ z).mp hz).1
  have hd := (scalarPurityPolynomial s).hasFDerivAt_thicken c z
    (hasFDerivAt_scalarPurityPolynomial s x)
  change topRealJacobian (fderiv ℝ ((scalarPurityPolynomial s).thicken c).eval z) ≤ _
  rw [hd.fderiv]
  have hn := norm_fderiv_scalarPurityPolynomial_le s hδ hx
  rw [(hasFDerivAt_scalarPurityPolynomial s x).fderiv] at hn
  simpa using topRealJacobian_thickenedLinearMap_le
    (scalarEuclidean.toContinuousLinearMap.comp (fderiv ℝ (coordinatePurity s) x)) 0
    (scalarEuclidean.toContinuousLinearMap.comp (fderiv ℝ (coordinatePurity s) x))
    (by simp) (by positivity) le_rfl hc hn hn (t := 0) (by simp) (by decide)

end ReverseBlocks

/-- Charged pure reachability places every target purity in one scalar image.
The scalar thickening has radius `8 sqrt(2 epsilon)`; the extra factor permits
use of the closed unit interval even at the freezing-distance endpoint. -/
theorem pureReachable_purity_mem_scalarWitness {K : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ} (hU : U ∈ pureReachable 2 K ε) :
    scalarEuclidean (purity (1 / 16) (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ∈
      ⋃ s : ReverseShape 2 K,
        (ReverseBlocks.thickenedScalarPurityPolynomial s (8 * Real.sqrt (2 * ε))).eval ''
          (ReverseBlocks.scalarPurityWitnessFormat s (Real.sqrt (2 * ε))).source := by
  obtain ⟨t, P, hP, hscore⟩ := hU
  obtain ⟨s, x, hx, hclose⟩ := P.exists_polynomial_witness_approximation (by decide)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) U.property.1 hP hε0.le hε1 hscore
  let H := ReverseBlocks.extendedOverlap (ReverseBlocks.decodeCoordinates s (by decide) x)
  have hclose' : ‖H - (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ 2 * Real.sqrt (2 * ε) := by
    rw [ReverseBlocks.coordinateOverlapPolynomial_eval, ReverseBlocks.coordinateOverlap,
      ← map_sub, norm_overlapOutputCoordinates] at hclose
    exact hclose
  obtain ⟨hv, _, _⟩ := (ReverseBlocks.mem_witnessFormat_source_iff s (by decide) _ x).mp hx
  have hH : ‖H‖ ≤ 2 := by
    dsimp only [H]
    rw [ReverseBlocks.extendedOverlap_eq_overlap hv (by decide)]
    exact hv.qubit_norm_overlap_le
  have hUn : ‖(U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ 2 := by
    have hUi : IsIsometry (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := U.property.1
    have h := hUi.frobNorm_sq_eq_card
    norm_num [Fintype.card_prod] at h
    nlinarith [norm_nonneg (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)]
  have hp : |purity (1 / 16) (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - ReverseBlocks.coordinatePurity s x| ≤
      4 * Real.sqrt (2 * ε) := by
    have h := qubit_purity_sub_le H (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) hH hUn
    rw [norm_sub_rev] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hclose' (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hδ : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (by positivity)
  apply Set.mem_iUnion.mpr
  refine ⟨s, (ReverseBlocks.scalarPurityPolynomial s).tube_subset_thicken_image
    (ReverseBlocks.witnessFormat s (by decide) (Real.sqrt (2 * ε))) _
    (by positivity : 0 < 8 * Real.sqrt (2 * ε)) ?_⟩
  refine ⟨x, hx, ?_⟩
  rw [dist_eq_norm, ReverseBlocks.scalarPurityPolynomial_eval, ← map_sub,
    norm_scalarEuclidean, Real.norm_eq_abs]
  exact hp.trans_lt (by nlinarith)

/-- Common-map finite mixtures use the proved high-score pure-component bridge. -/
theorem mixedReachable_purity_mem_scalarWitness {K : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ} (hU : U ∈ mixedReachable 2 K ε) :
    scalarEuclidean (purity (1 / 16) (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ∈
      ⋃ s : ReverseShape 2 K,
        (ReverseBlocks.thickenedScalarPurityPolynomial s (8 * Real.sqrt (2 * ε))).eval ''
          (ReverseBlocks.scalarPurityWitnessFormat s (Real.sqrt (2 * ε))).source := by
  rw [mixedReachable_eq_pureReachable] at hU
  exact pureReachable_purity_mem_scalarWitness hε0 hε1 hU

end NLQCLean
