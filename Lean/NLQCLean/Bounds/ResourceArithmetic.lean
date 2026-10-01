import NLQCLean.Bounds.CodimensionArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Arithmetic of the universal resource lower bound

These are numerical consequences of a Haar
upper bound equal to at least one; they introduce no geometric hypothesis.
-/

namespace NLQCLean

theorem log_bound_of_one_le_haar_rhs {A e : ℝ} {k : ℕ} (he : 0 < e)
    (h : 1 ≤ Real.exp A * e ^ ((k : ℝ) / 2)) :
    (k : ℝ) / 2 * Real.log (1 / e) ≤ A := by
  rw [Real.rpow_def_of_pos he, ← Real.exp_add, Real.one_le_exp_iff] at h
  rw [one_div, Real.log_inv]
  linarith

/-- Taking square roots after the codimension estimate gives the source's explicit constant. -/
theorem resource_lower_of_log_bound {d : ℕ} (hd : 2 ≤ d) {C K L : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbound : (unitaryCodimension d : ℝ) / 2 * L ≤ C * (d : ℝ) ^ 2 * K ^ 2) :
    Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt L ≤ K := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos hd0 2
  have hcod := mul_le_mul_of_nonneg_right (unitaryCodimension_lower hd) hL
  have hsq : (3 / 32 : ℝ) * (d : ℝ) ^ 2 * L ≤ C * K ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hd2).mp
    nlinarith
  have hdiv : (3 / (32 * C)) * (d : ℝ) ^ 2 * L ≤ K ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hC).mp
    calc
      C * ((3 / (32 * C)) * (d : ℝ) ^ 2 * L) = (3 / 32 : ℝ) * (d : ℝ) ^ 2 * L := by
        field_simp
      _ ≤ _ := hsq
  have hroot : (Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt L) ^ 2 =
      (3 / (32 * C)) * (d : ℝ) ^ 2 * L := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hL]
  nlinarith [show 0 ≤ Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt L by positivity]

theorem resource_lower_of_one_le_haar_rhs {d K : ℕ} (hd : 2 ≤ d) {C e : ℝ}
    (hC : 0 < C) (he : 0 < e) (he1 : e ≤ 1)
    (h : 1 ≤ Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
      e ^ ((unitaryCodimension d : ℝ) / 2)) :
    Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K :=
  resource_lower_of_log_bound hd hC (Nat.cast_nonneg K)
    (Real.log_nonneg ((one_le_div₀ he).mpr he1)) (log_bound_of_one_le_haar_rhs he h)

/-- The explicit additive constant in the qubit statement, valid for every positive c. -/
theorem qubit_lower_of_resource {c K L : ℝ} (hc : 0 < c) (hL : 0 < L) (n : ℕ)
    (h : c * (2 : ℝ) ^ n * Real.sqrt L ≤ K) :
    (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 L - max 0 (-Real.logb 2 c) ≤ Real.logb 2 K := by
  have hp : 0 < c * (2 : ℝ) ^ n * Real.sqrt L := by positivity
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp h
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul hc.ne' (by positivity),
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hL] at hl
  linarith [le_max_right (0 : ℝ) (-Real.logb 2 c)]

end NLQCLean
