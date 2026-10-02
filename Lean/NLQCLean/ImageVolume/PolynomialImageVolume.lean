/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.ImageVolume.BarrierImageVolume
import NLQCLean.Geometry.PolynomialImageVolumeHypothesis

/-!
# Proof of the polynomial image-volume bound

`polynomialImageVolumeBound` proves `PolynomialImageVolumeBound`: one constant `C ≥ 1` such
that for every compact basic closed source `S` of the bounded format inside the radius-three
ball, and every polynomial map `p` of degree at most one hundred whose top Jacobian is at
most `B` on `S`,

  `vol p(S) ≤ C^(a+m) · vol(B^m) · B`.

By continuity and compactness the Jacobian bound `B + η` holds on a basic open neighborhood
`U = {t - ∑ fᵢ² > 0, gⱼ + t > 0, 10 - ‖x‖² > 0}` of `S`. The product of the defining
polynomials is a barrier for `U`, so `LagrangeCharts.volume_polyMap_image_le` applies with
degree bound `2202`. Letting `η → 0` gives the bound.

The proof uses only Mathlib and results proved in this library; no geometric hypothesis
remains.
-/

namespace NLQCLean

open MvPolynomial MeasureTheory Set Filter LagrangeCharts
open scoped ENNReal Topology

theorem continuous_topRealJacobian (a m : ℕ) :
    Continuous (topRealJacobian : (RealEuclidean a →L[ℝ] RealEuclidean m) → ℝ) := by
  have ha : Continuous (fun L : RealEuclidean a →L[ℝ] RealEuclidean m => L.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  exact Real.continuous_sqrt.comp
    (ContinuousLinearMap.continuous_det.comp (continuous_id.clm_comp ha))

theorem ContDiff.continuous_topRealJacobian_fderiv {a m : ℕ}
    {p : RealEuclidean a → RealEuclidean m} (hp : ContDiff ℝ 1 p) :
    Continuous (fun x => topRealJacobian (fderiv ℝ p x)) :=
  (continuous_topRealJacobian a m).comp (hp.continuous_fderiv one_ne_zero)

theorem euclideanUnitBallVolume_ne_top (m : ℕ) : euclideanUnitBallVolume m ≠ ∞ :=
  measure_ball_lt_top.ne

namespace BoundedPolynomialMap

variable {a m : ℕ}

theorem eval_eq_polyMap (P : BoundedPolynomialMap a m) (x : RealEuclidean a) :
    P.eval x = WithLp.toLp 2 (polyMap P.coordinates (WithLp.ofLp x)) := rfl

theorem hasFDerivAt_eval (P : BoundedPolynomialMap a m) (x : RealEuclidean a) :
    HasFDerivAt P.eval
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm :
          (Fin m → ℝ) →L[ℝ] RealEuclidean m).comp
        ((fderiv ℝ (polyMap P.coordinates) (WithLp.ofLp x)).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ) :
            RealEuclidean a →L[ℝ] (Fin a → ℝ)))) x := by
  have h1 := ((contDiff_polyMap (n := 1) P.coordinates).differentiable one_ne_zero
    (WithLp.ofLp x)).hasFDerivAt
  have h2 := h1.comp x (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).hasFDerivAt
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.hasFDerivAt.comp x h2)

theorem contDiff_eval' (P : BoundedPolynomialMap a m) : ContDiff ℝ 1 P.eval := by
  have h : P.eval = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm ∘
      polyMap P.coordinates ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)) := rfl
  rw [h]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.contDiff.comp
    ((contDiff_polyMap P.coordinates).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).contDiff)

theorem fderiv_eval_basisFun (P : BoundedPolynomialMap a m) (x : RealEuclidean a) (c : Fin a)
    (k : Fin m) :
    fderiv ℝ P.eval x (EuclideanSpace.basisFun (Fin a) ℝ c) k =
      MvPolynomial.eval (WithLp.ofLp x) (pderiv c (P.coordinates k)) := by
  rw [(P.hasFDerivAt_eval x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    EuclideanSpace.basisFun_apply]
  rw [← fderiv_polyMap_single]
  rfl

/-- The top Jacobian in Euclidean coordinates is the Gram volume of the gradients. -/
theorem topRealJacobian_fderiv_eval (P : BoundedPolynomialMap a m) (x : RealEuclidean a) :
    topRealJacobian (fderiv ℝ P.eval x) = gradJacobian P.coordinates (WithLp.ofLp x) := by
  have hrows : gradRows P.coordinates (WithLp.ofLp x) =
      fun k => (fderiv ℝ P.eval x).adjoint (EuclideanSpace.basisFun (Fin m) ℝ k) := by
    funext k
    ext c
    change MvPolynomial.eval (WithLp.ofLp x) (pderiv c (P.coordinates k)) = _
    rw [← EuclideanSpace.basisFun_inner (Fin a) ℝ
        ((fderiv ℝ P.eval x).adjoint (EuclideanSpace.basisFun (Fin m) ℝ k)) c,
      ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_basisFun_real,
      fderiv_eval_basisFun]
  unfold topRealJacobian gradJacobian
  rw [hrows, gram_det_eq_adjoint_comp_det (fderiv ℝ P.eval x).adjoint,
    ContinuousLinearMap.adjoint_adjoint]

end BoundedPolynomialMap

/-! ### The barrier neighborhood of a basic closed source -/

namespace PolynomialBasicClosedFormat

variable {a : ℕ}

/-- `∑ᵢ fᵢ²` for the equations of the format. -/
noncomputable def equationSquares (F : PolynomialBasicClosedFormat a) : MvPolynomial (Fin a) ℝ :=
  ∑ i, F.equations i ^ 2

/-- `∑ᵢ xᵢ²`. -/
noncomputable def normSquare (a : ℕ) : MvPolynomial (Fin a) ℝ := ∑ i, X i ^ 2

/-- The barrier polynomial of the neighborhood with parameter `t`. -/
noncomputable def barrier (F : PolynomialBasicClosedFormat a) (t : ℝ) : MvPolynomial (Fin a) ℝ :=
  (C t - F.equationSquares) * (∏ j, (F.inequalities j + C t)) * (C 10 - normSquare a)

/-- The open neighborhood with parameter `t`, in coordinates. -/
def openNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) : Set (Fin a → ℝ) :=
  {x | 0 < t - eval x F.equationSquares ∧ (∀ j, 0 < eval x (F.inequalities j) + t) ∧
    0 < 10 - ∑ i, x i ^ 2}

/-- The closed neighborhood with parameter `t`, in coordinates. -/
def closedNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) : Set (Fin a → ℝ) :=
  {x | 0 ≤ t - eval x F.equationSquares ∧ (∀ j, 0 ≤ eval x (F.inequalities j) + t) ∧
    0 ≤ 10 - ∑ i, x i ^ 2}

theorem eval_normSquare (x : Fin a → ℝ) : eval x (normSquare a) = ∑ i, x i ^ 2 := by
  simp [normSquare]

theorem eval_barrier (F : PolynomialBasicClosedFormat a) (t : ℝ) (x : Fin a → ℝ) :
    eval x (F.barrier t) = (t - eval x F.equationSquares) *
      (∏ j, (eval x (F.inequalities j) + t)) * (10 - ∑ i, x i ^ 2) := by
  simp [barrier, eval_normSquare, map_prod]

theorem totalDegree_barrier_le (F : PolynomialBasicClosedFormat a) (t : ℝ) :
    (F.barrier t).totalDegree ≤ 2202 := by
  unfold barrier
  have hsq : (C t - F.equationSquares).totalDegree ≤ 200 := by
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    exact (totalDegree_pow _ _).trans (by have := F.equations_degree i; omega)
  have hprod : (∏ j, (F.inequalities j + C t)).totalDegree ≤ 2000 := by
    refine (totalDegree_finsetProd _ _).trans ?_
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin F.numInequalities)),
        (F.inequalities j + C t).totalDegree ≤ 100 := fun j _ =>
      (totalDegree_add _ _).trans (max_le (F.inequalities_degree j) (by simp))
    refine (Finset.sum_le_sum hle).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have := F.constraint_count
    nlinarith
  have hnorm : (C 10 - normSquare a).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    exact (totalDegree_pow _ _).trans (by simp)
  refine (totalDegree_mul _ _).trans ?_
  have h1 := totalDegree_mul (C t - F.equationSquares) (∏ j, (F.inequalities j + C t))
  omega

theorem openNbhd_subset_closedNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) :
    F.openNbhd t ⊆ F.closedNbhd t := fun _ hx =>
  ⟨hx.1.le, fun j => (hx.2.1 j).le, hx.2.2.le⟩

theorem continuous_eval_pi (P : MvPolynomial (Fin a) ℝ) :
    Continuous (fun x : Fin a → ℝ => eval x P) :=
  (contDiff_eval_pi (n := 0) P).continuous

theorem continuous_sum_sq : Continuous (fun x : Fin a → ℝ => ∑ i, x i ^ 2) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

theorem setOf_forall_inequalities (F : PolynomialBasicClosedFormat a) (t : ℝ)
    (r : ℝ → ℝ → Prop) :
    {x : Fin a → ℝ | ∀ j, r 0 (eval x (F.inequalities j) + t)} =
      ⋂ j, {x : Fin a → ℝ | r 0 (eval x (F.inequalities j) + t)} := by
  ext x
  simp

theorem isOpen_openNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) :
    IsOpen (F.openNbhd t) := by
  have h1 : IsOpen {x : Fin a → ℝ | 0 < t - eval x F.equationSquares} :=
    isOpen_lt continuous_const (continuous_const.sub (continuous_eval_pi _))
  have h2 : IsOpen {x : Fin a → ℝ | ∀ j, 0 < eval x (F.inequalities j) + t} := by
    rw [setOf_forall_inequalities F t (· < ·)]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const ((continuous_eval_pi _).add continuous_const)
  have h3 : IsOpen {x : Fin a → ℝ | 0 < 10 - ∑ i, x i ^ 2} :=
    isOpen_lt continuous_const (continuous_const.sub continuous_sum_sq)
  exact h1.inter (h2.inter h3)

theorem isClosed_closedNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) :
    IsClosed (F.closedNbhd t) := by
  have h1 : IsClosed {x : Fin a → ℝ | 0 ≤ t - eval x F.equationSquares} :=
    isClosed_le continuous_const (continuous_const.sub (continuous_eval_pi _))
  have h2 : IsClosed {x : Fin a → ℝ | ∀ j, 0 ≤ eval x (F.inequalities j) + t} := by
    rw [setOf_forall_inequalities F t (· ≤ ·)]
    exact isClosed_iInter fun j =>
      isClosed_le continuous_const ((continuous_eval_pi _).add continuous_const)
  have h3 : IsClosed {x : Fin a → ℝ | 0 ≤ 10 - ∑ i, x i ^ 2} :=
    isClosed_le continuous_const (continuous_const.sub continuous_sum_sq)
  exact h1.inter (h2.inter h3)

theorem sq_le_of_sum_sq_le {x : Fin a → ℝ} (hx : ∑ i, x i ^ 2 ≤ 10) (i : Fin a) :
    x i ^ 2 ≤ 10 :=
  (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hx

theorem isCompact_closedNbhd (F : PolynomialBasicClosedFormat a) (t : ℝ) :
    IsCompact (F.closedNbhd t) := by
  refine Metric.isCompact_of_isClosed_isBounded (F.isClosed_closedNbhd t) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin a → ℝ)) (r := 4)).subset fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have h := sq_le_of_sum_sq_le (by linarith [hx.2.2]) i
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

theorem barrier_pos (F : PolynomialBasicClosedFormat a) (t : ℝ) {x : Fin a → ℝ}
    (hx : x ∈ F.openNbhd t) : 0 < eval x (F.barrier t) := by
  rw [eval_barrier]
  exact mul_pos (mul_pos hx.1 (Finset.prod_pos fun j _ => hx.2.1 j)) hx.2.2

theorem mem_openNbhd_of_barrier_pos (F : PolynomialBasicClosedFormat a) (t : ℝ)
    {x : Fin a → ℝ} (hx : x ∈ F.closedNbhd t) (hφ : 0 < eval x (F.barrier t)) :
    x ∈ F.openNbhd t := by
  rw [eval_barrier] at hφ
  have hne := hφ.ne'
  simp only [ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨h1, h2⟩, h3⟩ := hne
  rw [Finset.prod_eq_zero_iff] at h2
  push Not at h2
  refine ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), fun j => ?_, lt_of_le_of_ne hx.2.2 (Ne.symm h3)⟩
  exact lt_of_le_of_ne (hx.2.1 j) (Ne.symm (h2 j (Finset.mem_univ j)))

theorem openNbhd_sum_sq_le (F : PolynomialBasicClosedFormat a) (t : ℝ) {x : Fin a → ℝ}
    (hx : x ∈ F.openNbhd t) : ∑ i, x i ^ 2 ≤ Real.sqrt 10 ^ 2 := by
  rw [Real.sq_sqrt (by norm_num)]
  linarith [hx.2.2]

theorem mem_source_iff (F : PolynomialBasicClosedFormat a) (x : Fin a → ℝ) :
    WithLp.toLp 2 x ∈ F.source ↔
      (∀ i, eval x (F.equations i) = 0) ∧ (∀ i, 0 ≤ eval x (F.inequalities i)) := Iff.rfl

theorem sum_sq_ofLp (x : RealEuclidean a) : ∑ i, (WithLp.ofLp x) i ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

theorem ofLp_mem_openNbhd (F : PolynomialBasicClosedFormat a) {t : ℝ} (ht : 0 < t)
    (hball : F.source ⊆ Metric.closedBall 0 3) {x : RealEuclidean a} (hx : x ∈ F.source) :
    WithLp.ofLp x ∈ F.openNbhd t := by
  obtain ⟨heq, hineq⟩ := hx
  refine ⟨?_, fun j => ?_, ?_⟩
  · have : eval (WithLp.ofLp x) F.equationSquares = 0 := by
      simp only [equationSquares, map_sum, map_pow]
      exact Finset.sum_eq_zero fun i _ => by
        have := heq i
        simp only [sq_eq_zero_iff]
        exact this
    rw [this]
    linarith
  · have := hineq j
    change 0 ≤ eval (WithLp.ofLp x) (F.inequalities j) at this
    linarith
  · have hn : ‖x‖ ≤ 3 := by simpa using hball ⟨heq, hineq⟩
    rw [sum_sq_ofLp]
    nlinarith [norm_nonneg x]

/-- The equations vanish and the inequalities hold on the intersection of all
closed neighborhoods. -/
theorem toLp_mem_source_of_forall (F : PolynomialBasicClosedFormat a) {x : Fin a → ℝ}
    (hx : ∀ n : ℕ, x ∈ F.closedNbhd (1 / ((n : ℝ) + 1))) : WithLp.toLp 2 x ∈ F.source := by
  have hsq : eval x F.equationSquares ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have := (hx n).1
    linarith
  have hsq0 : ∀ i, eval x (F.equations i) = 0 := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin F.numEquations)),
        0 ≤ eval x (F.equations i) ^ 2 := fun i _ => sq_nonneg _
    have hzero : ∑ i, eval x (F.equations i) ^ 2 = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      simpa [equationSquares] using hsq
    intro i
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i))
  refine ⟨hsq0, fun j => ?_⟩
  by_contra hneg
  push Not at hneg
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hneg)
  have := (hx n).2.1 j
  change 0 ≤ eval x (F.inequalities j) + 1 / ((n : ℝ) + 1) at this
  linarith

/-- A Jacobian bound on the source persists, with any loss `η`, on some barrier
neighborhood. -/
theorem exists_openNbhd_gradJacobian_le {m : ℕ} (F : PolynomialBasicClosedFormat a)
    (P : BoundedPolynomialMap a m) {B : ℝ}
    (hJ : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ P.eval x) ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ F.openNbhd t, gradJacobian P.coordinates x ≤ B + η := by
  have hcont : Continuous (fun x : Fin a → ℝ => gradJacobian P.coordinates x) := by
    have h := (ContDiff.continuous_topRealJacobian_fderiv P.contDiff_eval').comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).symm.continuous
    refine h.congr fun x => ?_
    exact P.topRealJacobian_fderiv_eval _
  let T : ℕ → Set (Fin a → ℝ) := fun n =>
    F.closedNbhd (1 / ((n : ℝ) + 1)) ∩ {x | B + η ≤ gradJacobian P.coordinates x}
  have hmono : ∀ n, T (n + 1) ⊆ T n := by
    intro n x hx
    refine ⟨⟨?_, fun j => ?_, hx.1.2.2⟩, hx.2⟩
    · have h1 := hx.1.1
      have : 1 / ((↑(n + 1) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      linarith
    · have h1 := hx.1.2.1 j
      have : 1 / ((↑(n + 1) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      linarith
  have hclosed : ∀ n, IsClosed (T n) := fun n =>
    (F.isClosed_closedNbhd _).inter (isClosed_le continuous_const hcont)
  have hcompact : IsCompact (T 0) :=
    (F.isCompact_closedNbhd _).inter_right (isClosed_le continuous_const hcont)
  by_contra hcon
  push Not at hcon
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    obtain ⟨x, hx, hxJ⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨x, F.openNbhd_subset_closedNbhd _ hx, hxJ.le⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne
    hcompact hclosed
  rw [Set.mem_iInter] at hx
  have hsrc := F.toLp_mem_source_of_forall fun n => (hx n).1
  have hJx := hJ _ hsrc
  rw [P.topRealJacobian_fderiv_eval] at hJx
  have h0 : B + η ≤ gradJacobian P.coordinates x := (hx 0).2
  have h1 : gradJacobian P.coordinates x ≤ B := hJx
  linarith

end PolynomialBasicClosedFormat

/-! ### The image-volume bound -/

/-- The explicit constant of the image-volume bound. -/
def imageVolumeConstant : ℝ := 35248

theorem one_le_imageVolumeConstant : 1 ≤ imageVolumeConstant := by
  norm_num [imageVolumeConstant]

theorem volume_sum_sq_le (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume {z : Fin m → ℝ | ∑ k, z k ^ 2 ≤ R ^ 2} =
      ENNReal.ofReal (R ^ m) * euclideanUnitBallVolume m := by
  have he := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)
  have hset : Metric.closedBall (0 : RealEuclidean m) R =
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm ⁻¹' {z : Fin m → ℝ | ∑ k, z k ^ 2 ≤ R ^ 2} := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_preimage, Set.mem_ofPred_eq]
    change ‖x‖ ≤ R ↔ ∑ k, (WithLp.ofLp x) k ^ 2 ≤ R ^ 2
    rw [PolynomialBasicClosedFormat.sum_sq_ofLp]
    constructor
    · intro h
      exact pow_le_pow_left₀ (norm_nonneg x) h 2
    · intro h
      exact (pow_le_pow_iff_left₀ (norm_nonneg x) hR (by norm_num)).mp h
  rw [← he.measure_preimage_equiv, ← hset, Measure.addHaar_closedBall _ _ hR,
    finrank_euclideanSpace_fin]
  rfl

theorem natCast_mul_sqrt_ten_le (a m : ℕ) :
    ((2 ^ a * (2 * 2202 + 2) ^ (a + m) : ℕ) : ℝ) * Real.sqrt 10 ^ m ≤
      imageVolumeConstant ^ (a + m) := by
  have h4 : Real.sqrt 10 ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ (a + m) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4' : Real.sqrt 10 ^ m ≤ 4 ^ (a + m) :=
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 m).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  push_cast
  calc (2 : ℝ) ^ a * 4406 ^ (a + m) * Real.sqrt 10 ^ m
      ≤ 2 ^ (a + m) * 4406 ^ (a + m) * 4 ^ (a + m) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h2 (by positivity)) h4' (by positivity)
          (by positivity)
    _ = imageVolumeConstant ^ (a + m) := by
      rw [← mul_pow, ← mul_pow]
      norm_num [imageVolumeConstant]

/-- The polynomial image-volume property with the explicit constant `35248`. -/
theorem polynomialImageVolumeBoundWith_imageVolumeConstant :
    PolynomialImageVolumeBoundWith imageVolumeConstant := by
  intro a m _ha _hm F P _hF hFball B hB hJ
  have hη : ∀ η : ℝ, 0 < η → volume (P.eval '' F.source) ≤
      ENNReal.ofReal (imageVolumeConstant ^ (a + m)) * euclideanUnitBallVolume m *
        ENNReal.ofReal (B + η) := by
    intro η hη
    obtain ⟨t, ht, hJt⟩ := F.exists_openNbhd_gradJacobian_le P hJ hη
    have hcore := volume_polyMap_image_le (D := 2202) P.coordinates (F.barrier t)
      (fun k => (P.degree_le k).trans (by norm_num)) (F.totalDegree_barrier_le t)
      (F.isOpen_openNbhd t) (F.isCompact_closedNbhd t) (F.openNbhd_subset_closedNbhd t)
      (fun x hx => F.barrier_pos t hx) (fun x hx hφ => F.mem_openNbhd_of_barrier_pos t hx hφ)
      (fun x hx => F.openNbhd_sum_sq_le t hx) (by linarith) hJt
    have he := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)
    have hsub : volume (P.eval '' F.source) ≤
        volume (polyMap P.coordinates '' F.openNbhd t) := by
      rw [← he.measure_preimage_equiv]
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨WithLp.ofLp x, F.ofLp_mem_openNbhd ht hFball hx, rfl⟩
    rw [volume_sum_sq_le m (Real.sqrt_nonneg 10)] at hcore
    have hnum := natCast_mul_sqrt_ten_le a m
    have hnum' : (((2 ^ a * (2 * 2202 + 2) ^ (a + m) : ℕ) : ℝ≥0∞)) *
        ENNReal.ofReal (Real.sqrt 10 ^ m) ≤ ENNReal.ofReal (imageVolumeConstant ^ (a + m)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hnum
    calc volume (P.eval '' F.source)
        ≤ ENNReal.ofReal (B + η) * ((2 ^ a * (2 * 2202 + 2) ^ (a + m) : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.sqrt 10 ^ m) * euclideanUnitBallVolume m) := hsub.trans hcore
      _ = ENNReal.ofReal (B + η) * ((((2 ^ a * (2 * 2202 + 2) ^ (a + m) : ℕ) : ℝ≥0∞)) *
            ENNReal.ofReal (Real.sqrt 10 ^ m)) * euclideanUnitBallVolume m := by ring
      _ ≤ ENNReal.ofReal (B + η) * ENNReal.ofReal (imageVolumeConstant ^ (a + m)) *
            euclideanUnitBallVolume m := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (B + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal B)) := by
    have h : Tendsto (fun n : ℕ => B + 1 / ((n : ℝ) + 1)) atTop (𝓝 B) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
    exact (ENNReal.continuous_ofReal.tendsto B).comp h
  have hK : ENNReal.ofReal (imageVolumeConstant ^ (a + m)) * euclideanUnitBallVolume m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (euclideanUnitBallVolume_ne_top m)
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr hK)) fun n =>
    hη _ (by positivity)

/-- **The polynomial image-volume bound**, proved without external hypotheses. -/
theorem polynomialImageVolumeBound : PolynomialImageVolumeBound :=
  ⟨imageVolumeConstant, one_le_imageVolumeConstant,
    polynomialImageVolumeBoundWith_imageVolumeConstant⟩

end NLQCLean
