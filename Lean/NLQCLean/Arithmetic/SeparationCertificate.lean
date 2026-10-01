import NLQCLean.Arithmetic.CosineTransform

/-!
# Polynomial value-separation certificates

These are ordinary implications from explicitly parameterized lower bounds
on polynomial values. They neither establish such separation bounds nor
assert an elimination or transcendence theorem.
-/

namespace NLQCLean

open Polynomial

/-- The surviving leading coefficient gives an explicit positive integral height
witness for the cleared cosine substitution. -/
theorem one_le_abs_cosineTransform_top_coeff {P : Polynomial ℤ} (hP : P ≠ 0) :
    1 ≤ |((cosineTransform P).coeff (2 * P.natDegree) : ℝ)| := by
  rw [cosineTransform_coeff_twice_natDegree]
  have hc : P.coeff P.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP
  exact_mod_cast Int.one_le_abs hc

/-- Any uniform coefficient-height bound for the nonzero transformed polynomial
is at least one; in particular it is positive. -/
theorem one_le_cosineTransform_height_bound {P : Polynomial ℤ} {H : ℝ}
    (hP : P ≠ 0) (hheight : ∀ i, |((cosineTransform P).coeff i : ℝ)| ≤ H) :
    1 ≤ H :=
  (one_le_abs_cosineTransform_top_coeff hP).trans (hheight _)

/-- A univariate separation bound and the maximal-factor quotient
give an explicit lower bound on the positive bivariate root coordinate. -/
theorem bivariate_gap_lower_bound_of_polynomial_separation
    {Q : IntBivariatePolynomial} {L : ℕ} {H c g η : ℝ}
    (hQ : Q ≠ 0) (hdegree : BivariateDegreeLE Q L)
    (hH : 1 ≤ H) (hheight : BivariateHeightLE Q H) (hc : |c| ≤ 1)
    (hg0 : 0 < g) (hg1 : g ≤ 1) (hzero : bivariateEval Q c g = 0)
    (hseparation : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ L →
      (∀ i, |(P.coeff i : ℝ)| ≤ H) → η ≤ |integerPolynomialEval P c|) :
    η / ((L + 1 : ℕ) ^ 3 * H) ≤ g := by
  obtain ⟨hp, hd, hh, hbound⟩ := bivariate_primitive_root_certificate
    hQ hdegree hH hheight hc hg0 hg1 hzero
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hden : 0 < (L + 1 : ℕ) ^ 3 * H := by positivity
  apply (div_le_iff₀ hden).mpr
  exact (hseparation _ hp hd hh).trans (hbound.trans_eq (by ring))

/-- Separation of nonconstant integer polynomials at the exponential implies
cosine separation. A nonzero constant is handled by its integral absolute value. -/
theorem integer_cosine_lower_bound_of_complex_separation
    {P : Polynomial ℤ} {L : ℕ} {H σ : ℝ} (θ : ℝ)
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ L) (hH : 0 ≤ H)
    (hheight : ∀ i, |(P.coeff i : ℝ)| ≤ H) (hσ : 0 ≤ σ)
    (hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * L →
      (∀ i, |(S.coeff i : ℝ)| ≤ (L + 1 : ℕ) * (2 : ℝ) ^ L * H) →
      σ ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖) :
    min 1 (((2 : ℝ) ^ L)⁻¹ * σ) ≤ |integerPolynomialEval P (Real.cos θ)| := by
  by_cases hd0 : P.natDegree = 0
  · exact (min_le_left _ _).trans
      (one_le_abs_integerPolynomialEval_of_constant hP hd0 (Real.cos θ))
  · have hdpos : 0 < P.natDegree := Nat.pos_of_ne_zero hd0
    have hdegreeS : (cosineTransform P).natDegree ≤ 2 * L :=
      (cosineTransform_natDegree_le P).trans (Nat.mul_le_mul_left 2 hdegree)
    have hmajor : (P.natDegree + 1 : ℕ) * (2 : ℝ) ^ P.natDegree * H ≤
        (L + 1 : ℕ) * (2 : ℝ) ^ L * H := by
      have hn : ((P.natDegree + 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hdegree 1
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hn hp (by positivity) (by positivity)) hH
    have hbound := hseparation (cosineTransform P) (cosineTransform_nonconstant hdpos) hdegreeS
      (fun i => (cosineTransform_height_le hH hheight i).trans hmajor)
    have hinv : ((2 : ℝ) ^ L)⁻¹ ≤ ((2 : ℝ) ^ P.natDegree)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree)
    rw [abs_cosine_eval_eq_inv_pow_norm_transform]
    calc
      _ ≤ ((2 : ℝ) ^ L)⁻¹ * σ := min_le_right _ _
      _ ≤ ((2 : ℝ) ^ P.natDegree)⁻¹ * σ := mul_le_mul_of_nonneg_right hinv hσ
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The full boundary-to-exponential certificate, at any explicitly chosen angle.
The degree and height arguments of the separation premise use the original
degree cap, not a separately assumed quotient or transform certificate. -/
theorem bivariate_cosine_gap_lower_bound_of_complex_separation
    {Q : IntBivariatePolynomial} {L : ℕ} {H g σ : ℝ} (θ : ℝ)
    (hQ : Q ≠ 0) (hdegree : BivariateDegreeLE Q L)
    (hH : 1 ≤ H) (hheight : BivariateHeightLE Q H)
    (hg0 : 0 < g) (hg1 : g ≤ 1) (hzero : bivariateEval Q (Real.cos θ) g = 0)
    (hσ : 0 < σ)
    (hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * L →
      (∀ i, |(S.coeff i : ℝ)| ≤ (L + 1 : ℕ) * (2 : ℝ) ^ L * H) →
      σ ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖) :
    min 1 (((2 : ℝ) ^ L)⁻¹ * σ) / ((L + 1 : ℕ) ^ 3 * H) ≤ g := by
  apply bivariate_gap_lower_bound_of_polynomial_separation
    hQ hdegree hH hheight (Real.abs_cos_le_one θ) hg0 hg1 hzero
  intro P hp hd hh
  exact integer_cosine_lower_bound_of_complex_separation θ hp hd (by linarith) hh hσ.le hseparation

theorem polynomial_separation_gap_bound_pos {L : ℕ} {H σ : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) :
    0 < min 1 (((2 : ℝ) ^ L)⁻¹ * σ) / ((L + 1 : ℕ) ^ 3 * H) := by
  positivity

/-- The exact norm identity at the named angle one, without any separation premise. -/
theorem abs_cos_one_eval_eq_inv_pow_norm_transform (P : Polynomial ℤ) :
    |integerPolynomialEval P (Real.cos 1)| =
      ((2 : ℝ) ^ P.natDegree)⁻¹ *
        ‖(cosineTransform P).eval₂ (Int.castRingHom ℂ) (Complex.exp Complex.I)‖ := by
  simpa using abs_cosine_eval_eq_inv_pow_norm_transform P 1

end NLQCLean
