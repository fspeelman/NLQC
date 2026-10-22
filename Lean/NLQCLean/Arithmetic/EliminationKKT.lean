module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

/-!
# Strict derivatives of integer polynomials

Strict differentiability of integer polynomials in real coordinates, with partial
derivatives `pderiv`.
-/

namespace NLQCLean.Elimination

open MvPolynomial

/-- Real evaluation of an integer polynomial. -/
noncomputable abbrev ev {σ : Type*} (x : σ → ℝ) (p : MvPolynomial σ ℤ) : ℝ :=
  eval₂ (Int.castRingHom ℝ) x p

/-- The candidate differential of `x ↦ p(a, x)`. -/
noncomputable def polyDeriv {κ J : Type*} [Fintype J] (p : MvPolynomial (κ ⊕ J) ℤ) (a : κ → ℝ)
    (x : J → ℝ) : (J → ℝ) →L[ℝ] ℝ :=
  ∑ j, ev (Sum.elim a x) (pderiv (Sum.inr j) p) • ContinuousLinearMap.proj j

theorem polyDeriv_apply {κ J : Type*} [Fintype J] (p : MvPolynomial (κ ⊕ J) ℤ) (a : κ → ℝ)
    (x δ : J → ℝ) :
    polyDeriv p a x δ = ∑ j, ev (Sum.elim a x) (pderiv (Sum.inr j) p) * δ j := by
  simp [polyDeriv]

theorem hasStrictFDerivAt_ev {κ J : Type*} [Fintype J] [DecidableEq κ] [DecidableEq J]
    (p : MvPolynomial (κ ⊕ J) ℤ) (a : κ → ℝ) (x : J → ℝ) :
    HasStrictFDerivAt (fun y : J → ℝ => ev (Sum.elim a y) p) (polyDeriv p a x) x := by
  induction p using MvPolynomial.induction_on with
  | C z =>
    have : polyDeriv (C z) a x = 0 := by ext δ; simp [polyDeriv_apply]
    rw [this]
    exact (hasStrictFDerivAt_const (z : ℝ) x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by
        show (z : ℝ) = eval₂ (Int.castRingHom ℝ) (Sum.elim a y) (C z)
        rw [eval₂_C]; simp)
  | add p q hp hq =>
    have : polyDeriv (p + q) a x = polyDeriv p a x + polyDeriv q a x := by
      ext δ; simp [polyDeriv_apply, add_mul, Finset.sum_add_distrib]
    rw [this]
    exact (hp.add hq).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [ev, eval₂_add])
  | mul_X p v hp =>
    rcases v with k | i
    · have : polyDeriv (p * X (Sum.inl k)) a x = a k • polyDeriv p a x := by
        ext δ
        simp [polyDeriv_apply, Derivation.leibniz, pderiv_X, Finset.mul_sum,
          mul_comm, mul_left_comm]
      rw [this]
      exact (hp.const_mul (a k)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [ev, eval₂_mul, mul_comm])
    · have hproj : HasStrictFDerivAt (fun y : J → ℝ => y i) (ContinuousLinearMap.proj i) x :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i).hasStrictFDerivAt
      have h := hp.mul hproj
      have hpd : ∀ j, ev (Sum.elim a x) (pderiv (Sum.inr j) (p * X (Sum.inr i))) =
          ev (Sum.elim a x) (pderiv (Sum.inr j) p) * x i +
            if j = i then ev (Sum.elim a x) p else 0 := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp [ev, Derivation.leibniz]
          ring
        · have hne : (Sum.inr i : κ ⊕ J) ≠ Sum.inr j := fun h => hji (Sum.inr_injective h).symm
          simp [ev, Derivation.leibniz, pderiv_X_of_ne hne, hji]
          ring
      have : polyDeriv (p * X (Sum.inr i)) a x =
          ev (Sum.elim a x) p • ContinuousLinearMap.proj i + x i • polyDeriv p a x := by
        ext δ
        rw [polyDeriv_apply]
        simp only [hpd, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        simp only [_root_.add_apply, _root_.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, polyDeriv_apply, Finset.mul_sum]
        rw [add_comm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [ev, eval₂_mul])

end NLQCLean.Elimination
