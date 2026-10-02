/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.ImageVolume.NondegenerateZeroCount
import Mathlib.Algebra.MvPolynomial.CommRing
import NLQCLean.ImageVolume.BanachIndicatrix
import NLQCLean.ImageVolume.BlockMinorBound
import NLQCLean.ImageVolume.PolynomialDerivative

/-!
# Lagrange maps and coordinate charts

For a polynomial map `p : ℝ^a → ℝ^m` and a barrier polynomial `φ`, the Lagrange map on
`ℝ^a × ℝ^m` is

  `Φ(x, λ)_j = (φ(x) ∑ₖ λₖ ∂ⱼpₖ(x) - ∂ⱼφ(x)) / φ(x)`,

so `Φ(x, λ) = ℓ` says that `x` is a Lagrange critical point of `log φ + ⟨ℓ, ·⟩` on the
fiber of `p` through `x`. This file studies the two equidimensional maps

* `piMap (x, λ) = (Φ(x, λ), p(x))`, and
* `chartMap s (x, λ) = (Φ(x, λ), x_s)` for a coordinate subset `s` of size `m`.

Their Jacobian matrices share the first `a` rows, so the block Cauchy--Binet inequality
bounds `|det D piMap|` by the top Jacobian of `p` times `∑ₛ |det D chartMap s|`. A regular
point of a fiber of `chartMap s` is a nondegenerate zero of an explicit square polynomial
system, hence each fiber has at most `(2D + 2) ^ (a + m)` regular points.
-/

namespace NLQCLean
namespace LagrangeCharts

open MvPolynomial Set Filter Matrix
open scoped Topology

variable {a m : ℕ}

/-- Coordinates `(x, λ)` of the Lagrange space. -/
abbrev Idx (a m : ℕ) := Fin a ⊕ Fin m

/-- The first block of coordinates. -/
def xPart (w : Idx a m → ℝ) : Fin a → ℝ := fun j => w (Sum.inl j)

/-- The first block projection as a continuous linear map. -/
noncomputable def xPartL : (Idx a m → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inl j)

theorem xPartL_apply (w : Idx a m → ℝ) : xPartL w = xPart w := rfl

theorem continuous_xPart : Continuous (xPart : (Idx a m → ℝ) → Fin a → ℝ) :=
  (xPartL : (Idx a m → ℝ) →L[ℝ] (Fin a → ℝ)).continuous

theorem xPart_single_inl (c : Fin a) :
    xPart (Pi.single (Sum.inl c) (1 : ℝ) : Idx a m → ℝ) = Pi.single c 1 := by
  funext j
  simp [xPart, Pi.single_apply]

theorem xPart_single_inr (k : Fin m) :
    xPart (Pi.single (Sum.inr k) (1 : ℝ) : Idx a m → ℝ) = 0 := by
  funext j
  simp [xPart]

theorem eval_rename_inl (P : MvPolynomial (Fin a) ℝ) (w : Idx a m → ℝ) :
    eval w (rename Sum.inl P) = eval (xPart w) P := by
  rw [eval_rename]
  rfl

/-- The polynomial map in coordinates. -/
noncomputable def polyMap (p : Fin m → MvPolynomial (Fin a) ℝ) (x : Fin a → ℝ) : Fin m → ℝ :=
  fun k => eval x (p k)

theorem contDiff_polyMap {n : WithTop ℕ∞} (p : Fin m → MvPolynomial (Fin a) ℝ) :
    ContDiff ℝ n (polyMap p) :=
  contDiff_pi.mpr fun k => contDiff_eval_pi (p k)

theorem fderiv_polyMap_single (p : Fin m → MvPolynomial (Fin a) ℝ) (x : Fin a → ℝ) (j : Fin a)
    (k : Fin m) : fderiv ℝ (polyMap p) x (Pi.single j 1) k = eval x (pderiv j (p k)) := by
  have h : HasFDerivAt (polyMap p)
      (ContinuousLinearMap.pi fun k => polyGradient (p k) x) x :=
    hasFDerivAt_pi.mpr fun k => hasFDerivAt_eval_pi (p k) x
  rw [h.fderiv]
  simp [polyGradient_single]

/-- The gradient rows of `p`, as Euclidean vectors. -/
noncomputable def gradRows (p : Fin m → MvPolynomial (Fin a) ℝ) (x : Fin a → ℝ) :
    Fin m → RealEuclidean a :=
  fun k => WithLp.toLp 2 (fun c => eval x (pderiv c (p k)))

/-- The top Jacobian of `p`, as the square root of the Gram determinant of its gradients. -/
noncomputable def gradJacobian (p : Fin m → MvPolynomial (Fin a) ℝ) (x : Fin a → ℝ) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (gradRows p x)).det

/-- The numerator `φ ∑ₖ λₖ ∂ⱼpₖ - ∂ⱼφ` of the Lagrange map. -/
noncomputable def lagrangeNum (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (j : Fin a) : MvPolynomial (Idx a m) ℝ :=
  (∑ k, X (Sum.inr k) * rename Sum.inl (pderiv j (p k))) * rename Sum.inl φ -
    rename Sum.inl (pderiv j φ)

theorem eval_lagrangeNum (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (j : Fin a) (w : Idx a m → ℝ) :
    eval w (lagrangeNum p φ j) =
      (∑ k, w (Sum.inr k) * eval (xPart w) (pderiv j (p k))) * eval (xPart w) φ -
        eval (xPart w) (pderiv j φ) := by
  simp [lagrangeNum, eval_rename_inl]

theorem totalDegree_lagrangeNum_le {D : ℕ} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (hp : ∀ k, (p k).totalDegree ≤ D) (hφ : φ.totalDegree ≤ D)
    (j : Fin a) : (lagrangeNum p φ j).totalDegree ≤ 2 * D + 1 := by
  unfold lagrangeNum
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have h1 : (∑ k, X (Sum.inr k) * rename Sum.inl (pderiv j (p k)) :
        MvPolynomial (Idx a m) ℝ).totalDegree ≤ D + 1 := by
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      have hX := (totalDegree_X (R := ℝ) (Sum.inr k : Idx a m)).le
      have hr := (totalDegree_rename_le (Sum.inl : Fin a → Idx a m) (pderiv j (p k))).trans
        ((totalDegree_pderiv_le (p k) j).trans (hp k))
      omega
    have h2 := (totalDegree_rename_le (Sum.inl : Fin a → Idx a m) φ).trans hφ
    omega
  · exact (totalDegree_rename_le _ _).trans ((totalDegree_pderiv_le φ j).trans (by omega))

/-- One coordinate of the Lagrange map. -/
noncomputable def lagrangeMap (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (j : Fin a) (w : Idx a m → ℝ) : ℝ :=
  eval w (lagrangeNum p φ j) / eval (xPart w) φ

theorem contDiff_eval_xPart {n : WithTop ℕ∞} (P : MvPolynomial (Fin a) ℝ) :
    ContDiff ℝ n (fun w : Idx a m → ℝ => eval (xPart w) P) :=
  (contDiff_eval_pi P).comp (xPartL : (Idx a m → ℝ) →L[ℝ] (Fin a → ℝ)).contDiff

theorem hasFDerivAt_eval_xPart (P : MvPolynomial (Fin a) ℝ) (w : Idx a m → ℝ) :
    HasFDerivAt (fun w : Idx a m → ℝ => eval (xPart w) P)
      ((polyGradient P (xPart w)).comp xPartL) w :=
  (hasFDerivAt_eval_pi P (xPart w)).comp w xPartL.hasFDerivAt

theorem contDiffAt_lagrangeMap {n : WithTop ℕ∞} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (j : Fin a) {w : Idx a m → ℝ} (hw : eval (xPart w) φ ≠ 0) :
    ContDiffAt ℝ n (lagrangeMap p φ j) w :=
  (contDiff_eval_pi _).contDiffAt.fun_div (contDiff_eval_xPart φ).contDiffAt hw

theorem measurable_lagrangeMap (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (j : Fin a) : Measurable (lagrangeMap p φ j) :=
  (contDiff_eval_pi (n := 0) _).continuous.measurable.div
    (contDiff_eval_xPart (n := 0) φ).continuous.measurable

/-- `(x, λ) ↦ (Φ(x, λ), p(x))`. -/
noncomputable def piMap (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (w : Idx a m → ℝ) : Idx a m → ℝ :=
  Sum.elim (fun j => lagrangeMap p φ j w) (fun k => eval (xPart w) (p k))

/-- `(x, λ) ↦ (Φ(x, λ), x_s)`. -/
noncomputable def chartMap (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (s : Set.powersetCard (Fin a) m) (w : Idx a m → ℝ) : Idx a m → ℝ :=
  Sum.elim (fun j => lagrangeMap p φ j w) (fun k => w (Sum.inl (coordinateMinorAxes s k)))

theorem contDiffAt_piMap {n : WithTop ℕ∞} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) {w : Idx a m → ℝ} (hw : eval (xPart w) φ ≠ 0) :
    ContDiffAt ℝ n (piMap p φ) w := by
  refine contDiffAt_pi.mpr fun r => ?_
  rcases r with j | k
  · exact contDiffAt_lagrangeMap p φ j hw
  · exact (contDiff_eval_xPart (p k)).contDiffAt

theorem contDiffAt_chartMap {n : WithTop ℕ∞} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (s : Set.powersetCard (Fin a) m) {w : Idx a m → ℝ}
    (hw : eval (xPart w) φ ≠ 0) : ContDiffAt ℝ n (chartMap p φ s) w := by
  refine contDiffAt_pi.mpr fun r => ?_
  rcases r with j | k
  · exact contDiffAt_lagrangeMap p φ j hw
  · exact (contDiff_apply ℝ ℝ (Sum.inl (coordinateMinorAxes s k))).contDiffAt

/-- The shared upper rows of the two Jacobian matrices. -/
noncomputable def lagrangeRows (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (w : Idx a m → ℝ) : Fin a → Idx a m → ℝ :=
  fun j c => fderiv ℝ (lagrangeMap p φ j) w (Pi.single c 1)

theorem single_eq_ite' {ι : Type*} [DecidableEq ι] (c : ι) :
    (fun j' : ι => if c = j' then (1 : ℝ) else 0) = Pi.single c 1 := by
  funext j'
  simp [Pi.single_apply, eq_comm]

theorem toMatrix'_fderiv_piMap (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) {w : Idx a m → ℝ} (hw : eval (xPart w) φ ≠ 0) :
    LinearMap.toMatrix' (fderiv ℝ (piMap p φ) w : (Idx a m → ℝ) →ₗ[ℝ] (Idx a m → ℝ)) =
      blockRowMatrix (lagrangeRows p φ w) (gradRows p (xPart w)) := by
  have hdiff : ∀ r, DifferentiableAt ℝ (fun w => piMap p φ w r) w := fun r =>
    ((contDiffAt_pi.mp (contDiffAt_piMap (n := 1) p φ hw)) r).differentiableAt one_ne_zero
  have hpi := fderiv_pi (𝕜 := ℝ) (φ := fun r w => piMap p φ w r) hdiff
  ext r c
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ (fun w => fun r => piMap p φ w r) w (Pi.single c 1) r = _
  rw [hpi]
  simp only [ContinuousLinearMap.pi_apply]
  rcases r with j | k
  · rfl
  · change fderiv ℝ (fun w : Idx a m → ℝ => eval (xPart w) (p k)) w (Pi.single c 1) = _
    rw [(hasFDerivAt_eval_xPart (p k) w).fderiv]
    simp only [ContinuousLinearMap.comp_apply, xPartL_apply]
    rcases c with c | c
    · rw [xPart_single_inl, polyGradient_single]
      rfl
    · rw [xPart_single_inr, map_zero]
      rfl

theorem toMatrix'_fderiv_chartMap (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (s : Set.powersetCard (Fin a) m) {w : Idx a m → ℝ}
    (hw : eval (xPart w) φ ≠ 0) :
    LinearMap.toMatrix'
        (fderiv ℝ (chartMap p φ s) w : (Idx a m → ℝ) →ₗ[ℝ] (Idx a m → ℝ)) =
      blockRowMatrix (lagrangeRows p φ w)
        (fun k => EuclideanSpace.basisFun (Fin a) ℝ (coordinateMinorAxes s k)) := by
  have hdiff : ∀ r, DifferentiableAt ℝ (fun w => chartMap p φ s w r) w := fun r =>
    ((contDiffAt_pi.mp (contDiffAt_chartMap (n := 1) p φ s hw)) r).differentiableAt one_ne_zero
  have hpi := fderiv_pi (𝕜 := ℝ) (φ := fun r w => chartMap p φ s w r) hdiff
  ext r c
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ (fun w => fun r => chartMap p φ s w r) w (Pi.single c 1) r = _
  rw [hpi]
  simp only [ContinuousLinearMap.pi_apply]
  rcases r with j | k
  · rfl
  · change fderiv ℝ (fun w : Idx a m → ℝ => w (Sum.inl (coordinateMinorAxes s k))) w
      (Pi.single c 1) = _
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (Sum.inl (coordinateMinorAxes s k)) w).fderiv]
    simp only [ContinuousLinearMap.proj_apply, blockRowMatrix, Matrix.of_apply, Sum.elim_inr,
      lowerBlockRow]
    rcases c with c | c
    · simp [Pi.single_apply, EuclideanSpace.basisFun_apply, eq_comm]
    · simp

/-- **Determinant comparison.** -/
theorem abs_det_fderiv_piMap_le (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) {w : Idx a m → ℝ} (hw : eval (xPart w) φ ≠ 0) :
    |(fderiv ℝ (piMap p φ) w).det| ≤ gradJacobian p (xPart w) *
      ∑ s : Set.powersetCard (Fin a) m, |(fderiv ℝ (chartMap p φ s) w).det| := by
  have hpi : (fderiv ℝ (piMap p φ) w).det =
      (blockRowMatrix (lagrangeRows p φ w) (gradRows p (xPart w))).det := by
    rw [← toMatrix'_fderiv_piMap p φ hw, LinearMap.det_toMatrix']
  have hchart : ∀ s, (fderiv ℝ (chartMap p φ s) w).det =
      (blockRowMatrix (lagrangeRows p φ w)
        (fun k => EuclideanSpace.basisFun (Fin a) ℝ (coordinateMinorAxes s k))).det := by
    intro s
    rw [← toMatrix'_fderiv_chartMap p φ s hw, LinearMap.det_toMatrix']
  rw [hpi]
  simp only [hchart]
  exact abs_det_blockRowMatrix_le _ _

/-- The square polynomial system attached to a value `v` of `chartMap s`. -/
noncomputable def chartSystem (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (s : Set.powersetCard (Fin a) m) (v : Idx a m → ℝ) : Idx a m → MvPolynomial (Idx a m) ℝ :=
  Sum.elim (fun j => lagrangeNum p φ j - C (v (Sum.inl j)) * rename Sum.inl φ)
    (fun k => X (Sum.inl (coordinateMinorAxes s k)) - C (v (Sum.inr k)))

theorem totalDegree_chartSystem_le {D : ℕ} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (hp : ∀ k, (p k).totalDegree ≤ D) (hφ : φ.totalDegree ≤ D)
    (s : Set.powersetCard (Fin a) m) (v : Idx a m → ℝ) (r : Idx a m) :
    (chartSystem p φ s v r).totalDegree ≤ 2 * D + 1 := by
  rcases r with j | k
  · refine (totalDegree_sub _ _).trans (max_le (totalDegree_lagrangeNum_le p φ hp hφ j) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_rename_le _ _).trans (hφ.trans (by omega))
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_X _).le.trans (by omega)
    · rw [totalDegree_C]
      exact Nat.zero_le _

theorem eval_lagrangeNum_eq (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    (j : Fin a) {w : Idx a m → ℝ} (hw : eval (xPart w) φ ≠ 0) :
    eval w (lagrangeNum p φ j) = eval (xPart w) φ * lagrangeMap p φ j w := by
  rw [lagrangeMap, mul_div_cancel₀ _ hw]

/-- Regular points of a fiber of `chartMap s` are nondegenerate zeros of `chartSystem`. -/
theorem isNondegenerateZero_chartSystem (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (s : Set.powersetCard (Fin a) m) {w : Idx a m → ℝ}
    (hw : eval (xPart w) φ ≠ 0) (hdet : (fderiv ℝ (chartMap p φ s) w).det ≠ 0) :
    IsNondegenerateZero (chartSystem p φ s (chartMap p φ s w)) w := by
  set v := chartMap p φ s w with hv
  set G := chartSystem p φ s v
  have hzero : ∀ r, eval w (G r) = 0 := by
    intro r
    rcases r with j | k
    · simp only [G, chartSystem, Sum.elim_inl, map_sub, map_mul, eval_C, eval_rename_inl,
        eval_lagrangeNum_eq p φ j hw, hv, chartMap]
      ring
    · simp [G, chartSystem, hv, chartMap]
  refine ⟨hzero, ?_⟩
  -- Coordinate derivatives of the polynomial system.
  have hopen : IsOpen {w' : Idx a m → ℝ | eval (xPart w') φ ≠ 0} :=
    isOpen_ne_fun (contDiff_eval_xPart (n := 0) φ).continuous continuous_const
  have hinl : ∀ j, HasFDerivAt (fun w' => eval w' (G (Sum.inl j)))
      (eval (xPart w) φ • fderiv ℝ (lagrangeMap p φ j) w) w := by
    intro j
    have hφd := hasFDerivAt_eval_xPart (m := m) φ w
    have hLd : HasFDerivAt (fun w' => lagrangeMap p φ j w' - v (Sum.inl j))
        (fderiv ℝ (lagrangeMap p φ j) w) w :=
      (((contDiffAt_lagrangeMap (n := 1) p φ j hw).differentiableAt one_ne_zero).hasFDerivAt).sub_const _
    have hprod := hφd.fun_mul hLd
    have hLw : lagrangeMap p φ j w - v (Sum.inl j) = 0 := by
      simp [hv, chartMap]
    rw [hLw, zero_smul, add_zero] at hprod
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with w' hw'
    simp only [G, chartSystem, Sum.elim_inl, map_sub, map_mul, eval_C, eval_rename_inl,
      eval_lagrangeNum_eq p φ j hw']
    ring
  have hinr : ∀ k, HasFDerivAt (fun w' => eval w' (G (Sum.inr k)))
      (ContinuousLinearMap.proj (Sum.inl (coordinateMinorAxes s k)) :
        (Idx a m → ℝ) →L[ℝ] ℝ) w := by
    intro k
    refine ((hasFDerivAt_apply (𝕜 := ℝ) (Sum.inl (coordinateMinorAxes s k)) w).sub_const
      (v (Sum.inr k))).congr_of_eventuallyEq (Eventually.of_forall fun w' => ?_)
    simp [G, chartSystem]
  have hG : HasFDerivAt (polyEvalMap G)
      (ContinuousLinearMap.pi fun r => Sum.elim
        (fun j => eval (xPart w) φ • fderiv ℝ (lagrangeMap p φ j) w)
        (fun k => (ContinuousLinearMap.proj (Sum.inl (coordinateMinorAxes s k)) :
          (Idx a m → ℝ) →L[ℝ] ℝ)) r) w := by
    refine hasFDerivAt_pi.mpr fun r => ?_
    rcases r with j | k
    · exact hinl j
    · exact hinr k
  have hchart : ∀ h, (∀ j, fderiv ℝ (lagrangeMap p φ j) w h = 0) →
      (∀ k, h (Sum.inl (coordinateMinorAxes s k)) = 0) → h = 0 := by
    intro h h1 h2
    have hdiff : ∀ r, DifferentiableAt ℝ (fun w => chartMap p φ s w r) w := fun r =>
      ((contDiffAt_pi.mp (contDiffAt_chartMap (n := 1) p φ s hw)) r).differentiableAt one_ne_zero
    have hpi := fderiv_pi (𝕜 := ℝ) (φ := fun r w => chartMap p φ s w r) hdiff
    apply ContinuousLinearMap.injective_of_det_ne_zero hdet
    rw [map_zero]
    change fderiv ℝ (fun w => fun r => chartMap p φ s w r) w h = 0
    rw [hpi]
    funext r
    simp only [ContinuousLinearMap.pi_apply, Pi.zero_apply]
    rcases r with j | k
    · exact h1 j
    · change fderiv ℝ (fun w : Idx a m → ℝ => w (Sum.inl (coordinateMinorAxes s k))) w h = 0
      rw [(hasFDerivAt_apply (𝕜 := ℝ) (Sum.inl (coordinateMinorAxes s k)) w).fderiv]
      exact h2 k
  rw [hG.fderiv]
  intro h₁ h₂ hh
  rw [← sub_eq_zero]
  have hlin : ∀ h, (ContinuousLinearMap.pi fun r => Sum.elim
        (fun j => eval (xPart w) φ • fderiv ℝ (lagrangeMap p φ j) w)
        (fun k => (ContinuousLinearMap.proj (Sum.inl (coordinateMinorAxes s k)) :
          (Idx a m → ℝ) →L[ℝ] ℝ)) r) h = 0 → h = 0 := by
    intro h hz
    refine hchart h (fun j => ?_) (fun k => ?_)
    · have := congrFun hz (Sum.inl j)
      simp only [ContinuousLinearMap.pi_apply, Sum.elim_inl, _root_.smul_apply,
        smul_eq_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left hw
    · have := congrFun hz (Sum.inr k)
      simpa using this
  apply hlin
  rw [map_sub, hh, sub_self]

/-- Each fiber of `chartMap s` has at most `(2D + 2) ^ (a + m)` regular points. -/
theorem card_regular_fiber_le {D : ℕ} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (hp : ∀ k, (p k).totalDegree ≤ D) (hφ : φ.totalDegree ≤ D)
    (s : Set.powersetCard (Fin a) m) (v : Idx a m → ℝ) (T : Finset (Idx a m → ℝ))
    (hT : ∀ w ∈ T, (eval (xPart w) φ ≠ 0 ∧ (fderiv ℝ (chartMap p φ s) w).det ≠ 0) ∧
      chartMap p φ s w = v) :
    T.card ≤ (2 * D + 2) ^ (a + m) := by
  have h := card_le_of_isNondegenerateZero (chartSystem p φ s v)
    (totalDegree_chartSystem_le p φ hp hφ s v) T (fun w hw => by
      obtain ⟨⟨hw0, hdet⟩, hwv⟩ := hT w hw
      rw [← hwv]
      exact isNondegenerateZero_chartSystem p φ s hw0 hdet)
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul, add_assoc] using h

end LagrangeCharts
end NLQCLean
