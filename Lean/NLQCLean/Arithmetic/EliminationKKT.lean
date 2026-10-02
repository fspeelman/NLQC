import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Lagrange multipliers for integer polynomial programs

Strict differentiability of integer polynomials in real coordinates, with partial
derivatives `pderiv`, and the Lagrange multiplier rule at a constrained maximum when the
constraint differential is surjective (linear independence of the constraint gradients).
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

/-- The directional derivative of a polynomial with an explicit quadratic restriction to a
line. -/
theorem polyDeriv_eq_of_quadratic {κ J : Type*} [Fintype J] [DecidableEq κ] [DecidableEq J]
    (p : MvPolynomial (κ ⊕ J) ℤ) (a : κ → ℝ) (x δ : J → ℝ) (A B : ℝ)
    (hline : ∀ t : ℝ, ev (Sum.elim a (x + t • δ)) p = ev (Sum.elim a x) p + t * A + t ^ 2 * B) :
    polyDeriv p a x δ = A := by
  have hℓ : HasDerivAt (fun t : ℝ => x + t • δ) δ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add x
    rw [one_smul] at this
    exact this
  have h1 : HasDerivAt (fun t : ℝ => ev (Sum.elim a (x + t • δ)) p) (polyDeriv p a x δ) 0 := by
    have hF : HasFDerivAt (fun y : J → ℝ => ev (Sum.elim a y) p) (polyDeriv p a x)
        (x + (0 : ℝ) • δ) := by
      rw [zero_smul, add_zero]; exact (hasStrictFDerivAt_ev p a x).hasFDerivAt
    exact hF.comp_hasDerivAt (0 : ℝ) hℓ
  have h2 : HasDerivAt (fun t : ℝ => ev (Sum.elim a x) p + t * A + t ^ 2 * B) A 0 := by
    set c0 := ev (Sum.elim a x) p
    have hq := (Polynomial.C c0 + Polynomial.C A * Polynomial.X +
      Polynomial.C B * Polynomial.X ^ 2).hasDerivAt (0 : ℝ)
    have hfun : (fun t : ℝ => (Polynomial.C c0 + Polynomial.C A * Polynomial.X +
        Polynomial.C B * Polynomial.X ^ 2).eval t) = fun t => c0 + t * A + t ^ 2 * B := by
      funext t; simp; ring
    rw [hfun] at hq
    convert hq using 1
    simp
  rw [show (fun t : ℝ => ev (Sum.elim a (x + t • δ)) p) =
    fun t => ev (Sum.elim a x) p + t * A + t ^ 2 * B from funext hline] at h1
  exact h1.unique h2

/-- **Lagrange multiplier rule** at a constrained maximum with surjective constraint
differential. -/
theorem exists_multipliers_of_isMax {κ J Q₀ : Type*} [Fintype J] [Fintype Q₀]
    [DecidableEq κ] [DecidableEq J] (F : MvPolynomial (κ ⊕ J) ℤ) (a : κ → ℝ)
    (h : Q₀ → MvPolynomial (κ ⊕ J) ℤ) (x₀ : J → ℝ)
    (hfeas : ∀ q, ev (Sum.elim a x₀) (h q) = 0)
    (hmax : ∀ x, (∀ q, ev (Sum.elim a x) (h q) = 0) →
      ev (Sum.elim a x) F ≤ ev (Sum.elim a x₀) F)
    (hsurj : ∀ b : Q₀ → ℝ, ∃ δ : J → ℝ, ∀ q, polyDeriv (h q) a x₀ δ = b q) :
    ∃ μ : Q₀ → ℝ, ∀ j, ev (Sum.elim a x₀) (pderiv (Sum.inr j) F) =
      ∑ q, μ q * ev (Sum.elim a x₀) (pderiv (Sum.inr j) (h q)) := by
  have hextr : IsLocalExtrOn (fun y : J → ℝ => ev (Sum.elim a y) F)
      {y | ∀ q, ev (Sum.elim a y) (h q) = ev (Sum.elim a x₀) (h q)} x₀ := by
    refine Or.inr (IsMaxOn.isLocalMaxOn fun y hy => ?_)
    exact hmax y fun q => (hy q).trans (hfeas q)
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt
    (fun q => hasStrictFDerivAt_ev (h q) a x₀) (hasStrictFDerivAt_ev F a x₀)
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    obtain ⟨δ, hδ⟩ := hsurj Λ
    have := congrArg (fun φ : (J → ℝ) →L[ℝ] ℝ => φ δ) hsum
    simp only [h0, zero_smul, add_zero, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, _root_.zero_apply,
      hδ] at this
    have hΛ : Λ = 0 := by
      have hsq : ∀ q, Λ q * Λ q = 0 := by
        intro q
        have hnn : ∀ r, 0 ≤ Λ r * Λ r := fun r => mul_self_nonneg _
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hnn r)).mp this q
          (Finset.mem_univ _)
      funext q
      exact mul_self_eq_zero.mp (hsq q)
    exact hne (by simp [hΛ, h0])
  refine ⟨fun q => -Λ q / Λ₀, fun j => ?_⟩
  have := congrArg (fun φ : (J → ℝ) →L[ℝ] ℝ => φ (Pi.single j 1)) hsum
  simp only [_root_.add_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, _root_.zero_apply,
    polyDeriv_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  have key : ∑ q, -Λ q / Λ₀ * ev (Sum.elim a x₀) (pderiv (Sum.inr j) (h q)) =
      -1 / Λ₀ * ∑ q, Λ q * ev (Sum.elim a x₀) (pderiv (Sum.inr j) (h q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [key]
  field_simp
  linarith

end NLQCLean.Elimination
