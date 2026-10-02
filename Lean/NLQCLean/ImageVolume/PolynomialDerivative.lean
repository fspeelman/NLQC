/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Weight
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Derivatives of polynomial evaluation

The Fréchet derivative of `x ↦ eval x P` on `σ → ℝ` is `h ↦ ∑ j, (∂ⱼ P)(x) h j`, where
`∂ⱼ P = pderiv j P`. Partial derivatives do not increase total degree.
-/

namespace NLQCLean

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The gradient of a polynomial at a point, as a continuous linear functional. -/
noncomputable def polyGradient (P : MvPolynomial σ ℝ) (x : σ → ℝ) : (σ → ℝ) →L[ℝ] ℝ :=
  ∑ j, eval x (pderiv j P) • ContinuousLinearMap.proj j

omit [DecidableEq σ] in
theorem polyGradient_apply (P : MvPolynomial σ ℝ) (x h : σ → ℝ) :
    polyGradient P x h = ∑ j, eval x (pderiv j P) * h j := by
  simp [polyGradient]

omit [Fintype σ] in
theorem eval_pderiv_X (x : σ → ℝ) (i j : σ) :
    eval x (pderiv j (X i : MvPolynomial σ ℝ)) = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp
  · rw [pderiv_X_of_ne (Ne.symm h), ite_eq_right h, map_zero]

theorem hasFDerivAt_eval_pi (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y : σ → ℝ => eval y P) (polyGradient P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : polyGradient (C a : MvPolynomial σ ℝ) x = 0 :=
      ContinuousLinearMap.ext fun h => by simp [polyGradient_apply]
    simpa [h] using hasFDerivAt_const a x
  | add p q hp hq =>
    have h : polyGradient (p + q) x = polyGradient p x + polyGradient q x :=
      ContinuousLinearMap.ext fun h => by
        simp [polyGradient_apply, map_add, add_mul, Finset.sum_add_distrib]
    simpa only [map_add, h] using hp.fun_add hq
  | mul_X p i hp =>
    have hi : HasFDerivAt (fun y : σ → ℝ => y i) (ContinuousLinearMap.proj i) x :=
      hasFDerivAt_apply (𝕜 := ℝ) i x
    have hm := hp.fun_mul hi
    have heq : eval x p • (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ) +
        x i • polyGradient p x = polyGradient (p * X i) x := by
      refine ContinuousLinearMap.ext fun h => ?_
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, polyGradient_apply, pderiv_mul, map_add,
        map_mul, eval_X, eval_pderiv_X, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine (hm.congr_fderiv heq).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [map_mul, eval_X]

theorem fderiv_eval_pi (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    fderiv ℝ (fun y : σ → ℝ => eval y P) x = polyGradient P x :=
  (hasFDerivAt_eval_pi P x).fderiv

theorem polyGradient_single (P : MvPolynomial σ ℝ) (x : σ → ℝ) (j : σ) :
    polyGradient P x (Pi.single j 1) = eval x (pderiv j P) := by
  rw [polyGradient_apply]
  simp [Pi.single_apply]

omit [DecidableEq σ] in
theorem totalDegree_pderiv_le (P : MvPolynomial σ ℝ) (i : σ) :
    (pderiv i P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  refine (totalDegree_monomial_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  change (s - Finsupp.single i 1).degree ≤ s.degree
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun j _ => by simp

end NLQCLean
