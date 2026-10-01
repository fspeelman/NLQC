import NLQCLean.Approx.PolynomialWitnessFamily
import NLQCLean.Geometry.ThickenedJacobian

/-!
# Polynomial thickening in Euclidean coordinates


The source, map and derivative are explicit in the fixed polynomial format.
-/

namespace NLQCLean

open MvPolynomial

theorem euclideanProductCoordinates_fst_apply {a m : ℕ}
    (z : RealEuclidean (a + m)) (i : Fin a) :
    (euclideanProductCoordinates a m z).fst i = z (i.castAdd m) := rfl

theorem euclideanProductCoordinates_snd_apply {a m : ℕ}
    (z : RealEuclidean (a + m)) (i : Fin m) :
    (euclideanProductCoordinates a m z).snd i = z (i.natAdd a) := rfl

/-- The extra constraint is exactly one minus the squared Euclidean norm. -/
noncomputable def thickeningBallPolynomial (a m : ℕ) : MvPolynomial (Fin (a + m)) ℝ :=
  C 1 - ∑ j : Fin m, X (j.natAdd a) ^ 2

theorem thickeningBallPolynomial_degree (a m : ℕ) :
    (thickeningBallPolynomial a m).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply (totalDegree_finsetSum _ _).trans
    simp only [Finset.sup_le_iff, Finset.mem_univ, true_implies]
    intro i
    exact (totalDegree_pow _ _).trans (by simp)

theorem thickeningBallPolynomial_eval {a m : ℕ} (z : RealEuclidean (a + m)) :
    eval (fun i => z i) (thickeningBallPolynomial a m) =
      1 - ‖(euclideanProductCoordinates a m z).snd‖ ^ 2 := by
  simp [thickeningBallPolynomial, EuclideanSpace.real_norm_sq_eq,
    euclideanProductCoordinates_snd_apply]

/-- Append the unit-ball inequality; all original constraints are retained. -/
noncomputable def PolynomialBasicClosedFormat.thicken {a : ℕ}
    (F : PolynomialBasicClosedFormat a) (m : ℕ)
    (hcount : F.numEquations + F.numInequalities + 1 ≤ 20) :
    PolynomialBasicClosedFormat (a + m) where
  numEquations := F.numEquations
  numInequalities := F.numInequalities + 1
  constraint_count := by omega
  equations i := rename (Fin.castAdd m) (F.equations i)
  inequalities := Fin.cases (thickeningBallPolynomial a m)
    (fun i => rename (Fin.castAdd m) (F.inequalities i))
  equations_degree i := (totalDegree_rename_le _ _).trans (F.equations_degree i)
  inequalities_degree := Fin.cases ((thickeningBallPolynomial_degree a m).trans (by decide))
    (fun i => (totalDegree_rename_le _ _).trans (F.inequalities_degree i))

theorem PolynomialBasicClosedFormat.mem_thicken_source {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (hcount)
    (z : RealEuclidean (a + m)) :
    z ∈ (F.thicken m hcount).source ↔
      (euclideanProductCoordinates a m z).fst ∈ F.source ∧
        ‖(euclideanProductCoordinates a m z).snd‖ ≤ 1 := by
  simp only [PolynomialBasicClosedFormat.source, Set.mem_ofPred_eq,
    PolynomialBasicClosedFormat.thicken, Fin.forall_fin_succ, Fin.cases_zero,
    Fin.cases_succ, eval_rename, thickeningBallPolynomial_eval, Function.comp_def]
  simp only [← euclideanProductCoordinates_fst_apply]
  have hb : 0 ≤ 1 - ‖(euclideanProductCoordinates a m z).snd‖ ^ 2 ↔
      ‖(euclideanProductCoordinates a m z).snd‖ ≤ 1 := by
    have hn := norm_nonneg (euclideanProductCoordinates a m z).snd
    constructor <;> intro h <;> nlinarith
  rw [hb]
  tauto

theorem PolynomialBasicClosedFormat.thicken_source_radius {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (hcount)
    (hF : ∀ x ∈ F.source, ‖x‖ ≤ Real.sqrt 6) :
    (F.thicken m hcount).source ⊆ Metric.closedBall 0 3 := by
  intro z hz
  obtain ⟨hx, hy⟩ := (F.mem_thicken_source hcount z).mp hz
  have hx' := hF _ hx
  have he := WithLp.prod_norm_sq_eq_of_L2 (euclideanProductCoordinates a m z)
  rw [(euclideanProductCoordinates a m).norm_map] at he
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg z, norm_nonneg (euclideanProductCoordinates a m z).fst,
    norm_nonneg (euclideanProductCoordinates a m z).snd,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg (6 : ℝ)]

theorem PolynomialBasicClosedFormat.norm_mem_thicken_source_le_sqrt_seven {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (hcount)
    (hF : ∀ x ∈ F.source, ‖x‖ ≤ Real.sqrt 6)
    {z : RealEuclidean (a + m)} (hz : z ∈ (F.thicken m hcount).source) :
    ‖z‖ ≤ Real.sqrt 7 := by
  obtain ⟨hx, hy⟩ := (F.mem_thicken_source hcount z).mp hz
  have hx' := hF _ hx
  have he := WithLp.prod_norm_sq_eq_of_L2 (euclideanProductCoordinates a m z)
  rw [(euclideanProductCoordinates a m).norm_map] at he
  nlinarith [norm_nonneg z, norm_nonneg (euclideanProductCoordinates a m z).fst,
    norm_nonneg (euclideanProductCoordinates a m z).snd,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg (6 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_nonneg (7 : ℝ)]

theorem PolynomialBasicClosedFormat.isCompact_thicken_source {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (hcount)
    (hF : ∀ x ∈ F.source, ‖x‖ ≤ Real.sqrt 6) :
    IsCompact (F.thicken m hcount).source :=
  Metric.isCompact_of_isClosed_isBounded (F.thicken m hcount).isClosed_source
    (Metric.isBounded_closedBall.subset (F.thicken_source_radius hcount hF))

/-- The explicit coordinate polynomial for `(x,Y) ↦ p(x)+cY`. -/
noncomputable def BoundedPolynomialMap.thicken {a m : ℕ}
    (p : BoundedPolynomialMap a m) (c : ℝ) : BoundedPolynomialMap (a + m) m where
  coordinates j := rename (Fin.castAdd m) (p.coordinates j) + C c * X (j.natAdd a)
  degree_le j := (totalDegree_add _ _).trans (max_le
    ((totalDegree_rename_le _ _).trans (p.degree_le j))
    ((totalDegree_mul _ _).trans (by simp)))

theorem BoundedPolynomialMap.thicken_eval {a m : ℕ}
    (p : BoundedPolynomialMap a m) (c : ℝ) (z : RealEuclidean (a + m)) :
    (p.thicken c).eval z = p.eval (euclideanProductCoordinates a m z).fst +
      c • (euclideanProductCoordinates a m z).snd := by
  ext j
  simp [BoundedPolynomialMap.eval, BoundedPolynomialMap.thicken, eval_rename,
    Function.comp_def, euclideanProductCoordinates_fst_apply,
    euclideanProductCoordinates_snd_apply]

theorem BoundedPolynomialMap.thicken_degree {a m D : ℕ}
    (p : BoundedPolynomialMap a m) (c : ℝ)
    (hD : 1 ≤ D) (hp : ∀ j, (p.coordinates j).totalDegree ≤ D) (j : Fin m) :
    ((p.thicken c).coordinates j).totalDegree ≤ D :=
  (totalDegree_add _ _).trans (max_le ((totalDegree_rename_le _ _).trans (hp j))
    ((totalDegree_mul _ _).trans (by simpa using hD)))

/-- Every point in the open c-neighborhood is in the thickened image. -/
theorem BoundedPolynomialMap.tube_subset_thicken_image {a m : ℕ}
    (p : BoundedPolynomialMap a m) (F : PolynomialBasicClosedFormat a) (hcount)
    {c : ℝ} (hc : 0 < c) :
    {y | ∃ x ∈ F.source, dist y (p.eval x) < c} ⊆
      (p.thicken c).eval '' (F.thicken m hcount).source := by
  rintro y ⟨x, hx, hy⟩
  let v : RealEuclidean m := c⁻¹ • (y - p.eval x)
  let z := (euclideanProductCoordinates a m).symm (WithLp.toLp 2 (x, v))
  have he : euclideanProductCoordinates a m z = WithLp.toLp 2 (x, v) :=
    (euclideanProductCoordinates a m).apply_symm_apply _
  refine ⟨z, (F.mem_thicken_source hcount z).mpr ?_, ?_⟩
  · rw [he]
    refine ⟨hx, ?_⟩
    change ‖v‖ ≤ 1
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_eq_div]
    exact (div_le_one hc).mpr (by simpa only [dist_eq_norm] using hy.le)
  · rw [p.thicken_eval, he]
    change p.eval x + c • (c⁻¹ • (y - p.eval x)) = y
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, add_sub_cancel]

theorem BoundedPolynomialMap.hasFDerivAt_thicken {a m : ℕ}
    (p : BoundedPolynomialMap a m) (c : ℝ) (z : RealEuclidean (a + m))
    {L : RealEuclidean a →L[ℝ] RealEuclidean m}
    (hL : HasFDerivAt p.eval L (euclideanProductCoordinates a m z).fst) :
    HasFDerivAt (p.thicken c).eval (thickenedLinearMap L c) z := by
  let e := (euclideanProductCoordinates a m).toContinuousLinearEquiv.toContinuousLinearMap
  let f := (WithLp.fstL 2 ℝ (RealEuclidean a) (RealEuclidean m)).comp e
  let g := (WithLp.sndL 2 ℝ (RealEuclidean a) (RealEuclidean m)).comp e
  have h := (hL.comp z f.hasFDerivAt).add (g.hasFDerivAt.const_smul c)
  have he : L.comp f + c • g = thickenedLinearMap L c := by
    apply ContinuousLinearMap.ext
    intro v
    exact (thickenedLinearMap_apply L c v).symm
  rw [he] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun v =>
    p.thicken_eval c v))

end NLQCLean
