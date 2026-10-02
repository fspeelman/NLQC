import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Arithmetic for the Haar bound near the Bell basis

When `d³ ≤ 2K`, the dimension `N = d⁴` satisfies `N ≤ 4K²` and
`N log K ≤ 6K²`; these absorb the polynomial prefactors of the witness tube
bound into `exp(C K²)`.
-/

namespace NLQCLean

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt hx.le]
  rw [h1]
  have := Real.log_le_sub_one_of_pos hs
  linarith

theorem pow_le_exp_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp (n * Real.log x) := by
  rw [← Real.log_pow, Real.exp_log (pow_pos hx n)]

section Cubic

variable {d K : ℝ} (hd : 2 ≤ d) (hd3 : d ^ 3 ≤ 2 * K)
include hd hd3

theorem one_le_of_cube_le : 1 ≤ K := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hd 3
  norm_num at h
  linarith

theorem sq_le_of_cube_le : d ^ 2 ≤ 2 * K := by nlinarith

theorem fourth_le_of_cube_le : d ^ 4 ≤ 4 * K ^ 2 := by
  have h6 : d ^ 6 ≤ 4 * K ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hd3 2
    nlinarith
  have : d ^ 4 ≤ d ^ 6 := by
    have h1 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ d by linarith) 4]
  linarith

theorem fourth_mul_log_le_of_cube_le : d ^ 4 * Real.log K ≤ 6 * K ^ 2 := by
  have hK1 := one_le_of_cube_le hd hd3
  have hK0 : 0 < K := by linarith
  have hlog := log_le_two_sqrt hK0
  have hlog0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hd2 := sq_le_of_cube_le hd hd3
  -- `d ≤ √(2K)`
  have hdK : d ≤ Real.sqrt (2 * K) := by
    rw [show d = Real.sqrt (d ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hd2
  have hsK : Real.sqrt (2 * K) * Real.sqrt K = Real.sqrt 2 * K := by
    rw [Real.sqrt_mul (by norm_num), mul_assoc, Real.mul_self_sqrt hK0.le]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  calc d ^ 4 * Real.log K = d * d ^ 3 * Real.log K := by ring
    _ ≤ Real.sqrt (2 * K) * (2 * K) * (2 * Real.sqrt K) := by
        have h1 : d * d ^ 3 ≤ Real.sqrt (2 * K) * (2 * K) :=
          mul_le_mul hdK hd3 (by positivity) (Real.sqrt_nonneg _)
        exact mul_le_mul h1 hlog hlog0 (by positivity)
    _ = 4 * K * (Real.sqrt (2 * K) * Real.sqrt K) := by ring
    _ = 4 * Real.sqrt 2 * K ^ 2 := by rw [hsK]; ring
    _ ≤ 6 * K ^ 2 := by nlinarith [sq_nonneg K]

end Cubic

/-- Absorption of a power `(a K²)^N`, `a ≥ 1`, into `exp(C K²)`. -/
theorem pow_sq_le_exp_of_cube_le {d K a : ℝ} (hd : 2 ≤ d) (hd3 : d ^ 3 ≤ 2 * K) (ha : 1 ≤ a) :
    (a * K ^ 2) ^ (d ^ 4 : ℝ) ≤ Real.exp ((4 * Real.log a + 12) * K ^ 2) := by
  have hK1 := one_le_of_cube_le hd hd3
  have hK0 : 0 < K := by linarith
  have hx : 0 < a * K ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (a * K ^ 2) = Real.log a + 2 * Real.log K := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlog]
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 := fourth_le_of_cube_le hd hd3
  have h2 := fourth_mul_log_le_of_cube_le hd hd3
  nlinarith

end NLQCLean
