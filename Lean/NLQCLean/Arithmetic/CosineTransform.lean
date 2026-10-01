import NLQCLean.Arithmetic.BivariateFactor
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Integral polynomial substitution for the cosine

The substitution is built as an integer polynomial by its finite
binomial coefficient sum. In particular no Laurent-polynomial integrality
or denominator-clearing assertion is left implicit.
-/

namespace NLQCLean

open Polynomial
open scoped BigOperators

/-- One binomial monomial in the cleared cosine substitution. -/
noncomputable def cosineTransformTerm (P : Polynomial ℤ) (j k : ℕ) : Polynomial ℤ :=
  Polynomial.monomial (P.natDegree - j + 2 * k)
    (P.coeff j * (2 : ℤ) ^ (P.natDegree - j) * (j.choose k : ℤ))

/-- The integer polynomial `2^ell z^ell P((z+z⁻¹)/2)`, expanded finitely. -/
noncomputable def cosineTransform (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    ∑ k ∈ Finset.range (j + 1), cosineTransformTerm P j k

theorem cosineTransform_natDegree_le (P : Polynomial ℤ) :
    (cosineTransform P).natDegree ≤ 2 * P.natDegree := by
  unfold cosineTransform
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hj' : j ≤ P.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hk' : k ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  unfold cosineTransformTerm
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- The top coefficient survives unchanged; all lower-degree terms stay below it. -/
theorem cosineTransform_coeff_twice_natDegree (P : Polynomial ℤ) :
    (cosineTransform P).coeff (2 * P.natDegree) = P.coeff P.natDegree := by
  rw [cosineTransform, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single P.natDegree]
    · simp [cosineTransformTerm]
    · intro k _ hkne
      simp [cosineTransformTerm, Polynomial.coeff_monomial, hkne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  · intro j hj hjne
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    have hj' : j ≤ P.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have hk' : k ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    simp [cosineTransformTerm, Polynomial.coeff_monomial,
      show P.natDegree - j + 2 * k ≠ 2 * P.natDegree by omega]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem cosineTransform_natDegree {P : Polynomial ℤ} (hP : P ≠ 0) :
    (cosineTransform P).natDegree = 2 * P.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (cosineTransform_natDegree_le P)
  rw [cosineTransform_coeff_twice_natDegree]
  simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP

theorem cosineTransform_ne_zero {P : Polynomial ℤ} (hP : P ≠ 0) : cosineTransform P ≠ 0 := by
  intro hz
  have h := cosineTransform_coeff_twice_natDegree P
  rw [hz, Polynomial.coeff_zero] at h
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) h.symm

theorem cosineTransform_nonconstant {P : Polynomial ℤ} (hP : 0 < P.natDegree) :
    0 < (cosineTransform P).natDegree := by
  rw [cosineTransform_natDegree (Polynomial.ne_zero_of_natDegree_gt hP)]
  omega

theorem abs_cosineTransformTerm_coeff_le (P : Polynomial ℤ) (j k n : ℕ) :
    |((cosineTransformTerm P j k).coeff n : ℝ)| ≤
      |(P.coeff j : ℝ)| * (2 : ℝ) ^ (P.natDegree - j) * (j.choose k : ℝ) := by
  simp only [cosineTransformTerm, Polynomial.coeff_monomial]
  split_ifs
  · push_cast
    simp [abs_mul, abs_pow]
  · simp only [Int.cast_zero, abs_zero]
    positivity

/-- The exact binomial sum controls every coefficient by the source height bound. -/
theorem cosineTransform_height_le {P : Polynomial ℤ} {H : ℝ} (_hH : 0 ≤ H)
    (hheight : ∀ i, |(P.coeff i : ℝ)| ≤ H) (n : ℕ) :
    |((cosineTransform P).coeff n : ℝ)| ≤ (P.natDegree + 1 : ℕ) * (2 : ℝ) ^ P.natDegree * H := by
  rw [cosineTransform, Polynomial.finsetSum_coeff]
  simp only [Polynomial.finsetSum_coeff, Int.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1),
        |∑ k ∈ Finset.range (j + 1), ((cosineTransformTerm P j k).coeff n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1),
        ∑ k ∈ Finset.range (j + 1), H * (2 : ℝ) ^ (P.natDegree - j) * (j.choose k : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro k _
      exact (abs_cosineTransformTerm_coeff_le P j k n).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hheight j) (by positivity)) (Nat.cast_nonneg _))
    _ = ∑ _j ∈ Finset.range (P.natDegree + 1), H * (2 : ℝ) ^ P.natDegree := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ P.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      rw [← Finset.mul_sum, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat,
        mul_assoc, ← pow_add, Nat.sub_add_cancel hj']
    _ = _ := by simp; ring

theorem eval₂_cosineTransform_eq_sum (P : Polynomial ℤ) (z : ℂ) :
    (cosineTransform P).eval₂ (Int.castRingHom ℂ) z =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (P.coeff j : ℂ) * (2 : ℂ) ^ (P.natDegree - j) * z ^ (P.natDegree - j) * (z ^ 2 + 1) ^ j := by
  simp only [cosineTransform, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_pow]
  simp only [one_pow, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [cosineTransformTerm, Polynomial.eval₂_monomial]
  change ((P.coeff j * (2 : ℤ) ^ (P.natDegree - j) * (j.choose k : ℤ) : ℤ) : ℂ) *
    z ^ (P.natDegree - j + 2 * k) = _
  push_cast
  rw [pow_add, pow_mul]
  ring

/-- Exact denominator clearing at every nonzero complex evaluation point. -/
theorem eval₂_cosineTransform (P : Polynomial ℤ) {z : ℂ} (hz : z ≠ 0) :
    (cosineTransform P).eval₂ (Int.castRingHom ℂ) z =
      (2 : ℂ) ^ P.natDegree * z ^ P.natDegree *
        P.eval₂ (Int.castRingHom ℂ) ((z + z⁻¹) / 2) := by
  rw [eval₂_cosineTransform_eq_sum, Polynomial.eval₂_eq_sum_range]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ P.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hcos : (z + z⁻¹) / 2 = (z ^ 2 + 1) / (2 * z) := by field_simp
  have htwo : (2 : ℂ) ^ P.natDegree = (2 : ℂ) ^ (P.natDegree - j) * 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  have hpow : z ^ P.natDegree = z ^ (P.natDegree - j) * z ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  rw [hcos, htwo, hpow, div_pow, mul_pow]
  change (P.coeff j : ℂ) * 2 ^ (P.natDegree - j) * z ^ (P.natDegree - j) * (z ^ 2 + 1) ^ j =
    (2 ^ (P.natDegree - j) * 2 ^ j) * (z ^ (P.natDegree - j) * z ^ j) *
      ((P.coeff j : ℂ) * ((z ^ 2 + 1) ^ j / (2 ^ j * z ^ j)))
  field_simp

theorem eval₂_int_complex_ofReal (P : Polynomial ℤ) (x : ℝ) :
    P.eval₂ (Int.castRingHom ℂ) (x : ℂ) = (integerPolynomialEval P x : ℂ) := by
  simp only [integerPolynomialEval, Polynomial.eval₂_eq_sum_range]
  push_cast
  rfl

theorem cosine_exp_angle (θ : ℝ) :
    (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) / 2 =
      (Real.cos θ : ℂ) := by
  rw [← Complex.exp_neg, show -((θ : ℂ) * Complex.I) = -(θ : ℂ) * Complex.I by ring,
    ← Complex.two_cos, ← Complex.ofReal_cos]
  ring

/-- The source normalization is exact, including the constant-polynomial case. -/
theorem abs_cosine_eval_eq_inv_pow_norm_transform (P : Polynomial ℤ) (θ : ℝ) :
    |integerPolynomialEval P (Real.cos θ)| =
      ((2 : ℝ) ^ P.natDegree)⁻¹ *
        ‖(cosineTransform P).eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  have he := eval₂_cosineTransform P (Complex.exp_ne_zero ((θ : ℂ) * Complex.I))
  rw [cosine_exp_angle, eval₂_int_complex_ofReal] at he
  have hn := congrArg norm he
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_exp_ofReal_mul_I,
    one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- A nonzero constant integer polynomial has absolute value at least one. -/
theorem one_le_abs_integerPolynomialEval_of_constant {P : Polynomial ℤ}
    (hP : P ≠ 0) (hdegree : P.natDegree = 0) (x : ℝ) : 1 ≤ |integerPolynomialEval P x| := by
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hc : P.coeff 0 ≠ 0 := by
    intro hzero
    apply hP
    rw [hC, hzero, Polynomial.C_0]
  rw [hC]
  rw [integerPolynomialEval, Polynomial.eval₂_C]
  change 1 ≤ |(P.coeff 0 : ℝ)|
  exact_mod_cast Int.one_le_abs hc

end NLQCLean
