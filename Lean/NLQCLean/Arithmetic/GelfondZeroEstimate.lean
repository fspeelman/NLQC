import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Basic.Complex.Basic

/-!
# A one-point zero estimate for exponential polynomials

If `ω₀, …, ω_J` are distinct and the Taylor data at `0` of `Σ c_{jl} z^l e^{ω_j z}`,
`φ_t = Σ_{j,l} c_{jl} (t)_l ω_j^{t-l}`, vanish for all `t < (J+1)L`, then `c = 0`.

Pairing with a polynomial `Q` of degree `< (J+1)L` gives `Σ_t Q_t φ_t = Σ c_{jl} Q^{(l)}(ω_j)`;
with `Q = (X - ω_{j₀})^{l₀} ∏_{j ≠ j₀} (X - ω_j)^L` only the term `c_{j₀ l₀}` survives.
-/

namespace NLQCLean.Gelfond

open Polynomial

variable {K : Type*} [Field K]

/-- Iterated derivatives at a point through the coefficients. -/
theorem eval_iterate_derivative_eq_sum (Q : K[X]) (l : ℕ) (ω : K) {n : ℕ}
    (hQ : Q.natDegree < n) :
    (derivative^[l] Q).eval ω =
      ∑ t ∈ Finset.range n, Q.coeff t * ((t.descFactorial l : K) * ω ^ (t - l)) := by
  conv_lhs => rw [as_sum_range' Q n hQ]
  rw [iterate_derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← C_mul_X_pow_eq_monomial, iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul]
  simp [eval_smul, smul_eq_mul]
  ring

/-- Low derivatives vanish at a root of high multiplicity. -/
theorem eval_iterate_derivative_eq_zero_of_dvd [CharZero K] {p : K[X]} {a : K} {n l : ℕ}
    (hdvd : (X - C a) ^ n ∣ p) (hl : l < n) : (derivative^[l] p).eval a = 0 := by
  by_cases hp : p = 0
  · subst hp; simp
  exact isRoot_iterate_derivative_of_lt_rootMultiplicity
    (hl.trans_le ((le_rootMultiplicity_iff hp).mpr hdvd))

/-- `((X - a)^n R)^{(n)}(a) = n! R(a)`. -/
theorem eval_iterate_derivative_X_sub_pow_mul (R : K[X]) (a : K) (n : ℕ) :
    (derivative^[n] ((X - C a) ^ n * R)).eval a = (n.factorial : K) * R.eval a := by
  rw [iterate_derivative_mul, eval_finsetSum, Finset.sum_eq_single 0]
  · simp [iterate_derivative_X_sub_pow_self]
  · intro k hk hk0
    rw [iterate_derivative_X_sub_pow]
    have : 0 < n - (n - k) := by
      have := Finset.mem_range.mp hk
      omega
    simp [zero_pow this.ne']
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

/-- **Lemma Z.** -/
theorem coeff_eq_zero_of_taylor_vanish [CharZero K] {J L : ℕ} (ω : Fin (J + 1) → K)
    (hω : Function.Injective ω) (c : Fin (J + 1) → Fin L → K)
    (h : ∀ t < (J + 1) * L,
      ∑ j, ∑ l, c j l * ((t.descFactorial (l : ℕ) : K) * ω j ^ (t - l)) = 0) :
    c = 0 := by
  classical
  -- pairing identity
  have hpair : ∀ Q : K[X], Q.natDegree < (J + 1) * L →
      ∑ j, ∑ l, c j l * (derivative^[l] Q).eval (ω j) = 0 := by
    intro Q hQ
    have e1 : ∀ j l, c j l * (derivative^[l] Q).eval (ω j) =
        ∑ t ∈ Finset.range ((J + 1) * L),
          Q.coeff t * (c j l * ((t.descFactorial (l : ℕ) : K) * ω j ^ (t - l))) := by
      intro j l
      rw [eval_iterate_derivative_eq_sum Q _ _ hQ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    simp_rw [e1]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [← Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _), ← Finset.mul_sum,
      h t (Finset.mem_range.mp ht), mul_zero]
  by_contra hc
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, c j₀ ≠ 0 := by
    by_contra! H; exact hc (funext H)
  have hS : (Finset.univ.filter fun l => c j₀ l ≠ 0).Nonempty := by
    obtain ⟨l, hl⟩ : ∃ l, c j₀ l ≠ 0 := by
      by_contra! H; exact hj₀ (funext H)
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
  set l₀ := (Finset.univ.filter fun l => c j₀ l ≠ 0).max' hS with hl₀
  have hl₀mem := Finset.max'_mem _ hS
  rw [← hl₀, Finset.mem_filter] at hl₀mem
  have hmax : ∀ l, l₀ < l → c j₀ l = 0 := by
    intro l hl
    by_contra hne
    have := Finset.le_max' (Finset.univ.filter fun l => c j₀ l ≠ 0) l
      (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hne⟩)
    rw [← hl₀] at this
    exact absurd hl (not_lt.mpr this)
  obtain ⟨R, hR⟩ : ∃ R : K[X], R = ∏ j ∈ Finset.univ.erase j₀, (X - C (ω j)) ^ L := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : K[X], Q = (X - C (ω j₀)) ^ (l₀ : ℕ) * R := ⟨_, rfl⟩
  have hRdeg : R.natDegree = J * L := by
    rw [hR, natDegree_prod _ _ (fun j _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
    simp [natDegree_pow, Finset.card_erase_of_mem]
  have hQdeg : Q.natDegree < (J + 1) * L := by
    rw [hQ, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _))
      (by rw [hR]; exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (X_sub_C_ne_zero _)),
      natDegree_pow, natDegree_X_sub_C, hRdeg]
    have := l₀.isLt
    nlinarith
  have hval := hpair Q hQdeg
  rw [Finset.sum_eq_single j₀] at hval
  · rw [Finset.sum_eq_single l₀] at hval
    · rw [hQ, eval_iterate_derivative_X_sub_pow_mul] at hval
      have hRne : R.eval (ω j₀) ≠ 0 := by
        rw [hR, eval_prod]
        refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
        simp only [eval_pow, eval_sub, eval_X, eval_C]
        exact pow_ne_zero _ (sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hω h).symm)
      exact mul_ne_zero hl₀mem.2 (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        hRne) hval
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hlt | hgt
      · have hdvd0 : (X - C (ω j₀)) ^ (l₀ : ℕ) ∣ Q := hQ ▸ dvd_mul_right _ _
        rw [eval_iterate_derivative_eq_zero_of_dvd hdvd0 hlt, mul_zero]
      · rw [hmax l hgt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    refine Finset.sum_eq_zero fun l _ => ?_
    have hdvd : (X - C (ω j)) ^ L ∣ Q := by
      rw [hQ, hR]
      exact (Finset.dvd_prod_of_mem (fun j => (X - C (ω j)) ^ L)
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)).trans (dvd_mul_left _ _)
    rw [eval_iterate_derivative_eq_zero_of_dvd hdvd l.isLt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end NLQCLean.Gelfond
