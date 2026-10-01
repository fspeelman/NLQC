import NLQCLean.Approx.WitnessDifferentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dimension and logarithmic estimates for the Haar bound

The fixed coordinate budget is P=32d²K².
These numerical estimates do not use the polynomial image-volume input.
-/

namespace NLQCLean

/-- Dimension domination, using the real K>=d²/4 premise. -/
theorem sixth_power_le_witnessCoordinateBudget {d K : ℕ}
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) : (d : ℝ) ^ 6 ≤ witnessCoordinateBudget d K := by
  have h : (d : ℝ) ^ 2 ≤ 4 * K := by linarith
  have hs := pow_le_pow_left₀ (sq_nonneg (d : ℝ)) h 2
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (d : ℝ))
  unfold witnessCoordinateBudget
  push_cast
  nlinarith [sq_nonneg (K : ℝ)]

/-- A quadratic exponential estimate suffices for the source's sharp factor two. -/
theorem one_add_three_mul_le_two_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + 3 * x ≤ 2 * Real.exp x := by
  nlinarith [Real.quadratic_le_exp_of_nonneg hx, sq_nonneg (x - 1 / 2)]

/-- The logarithmic estimate in a form independent of the dimension parametrization. -/
theorem mul_one_add_log_le_twice_of_cube_le {P N : ℝ}
    (hP : 1 ≤ P) (hN : 0 ≤ N) (hNP : N ^ 3 ≤ P ^ 2) :
    N * (1 + Real.log P) ≤ 2 * P := by
  have hP0 : 0 < P := by linarith
  let x := Real.log P / 3
  have hx : 0 ≤ x := div_nonneg (Real.log_nonneg hP) (by norm_num)
  have hex : Real.exp (3 * x) = P := by
    dsimp only [x]
    rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), Real.exp_log hP0]
  have hepow : (Real.exp (2 * x)) ^ 3 = P ^ 2 := by
    calc
      _ = (Real.exp (3 * x)) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        norm_num
        ring
      _ = _ := by rw [hex]
  have hNE : N ≤ Real.exp (2 * x) :=
    (pow_le_pow_iff_left₀ hN (Real.exp_pos _).le (by decide : 3 ≠ 0)).mp (hepow ▸ hNP)
  have hlog : Real.log P = 3 * x := by dsimp only [x]; ring
  rw [hlog]
  calc
    _ ≤ Real.exp (2 * x) * (2 * Real.exp x) :=
      mul_le_mul hNE (one_add_three_mul_le_two_exp hx) (by linarith) (Real.exp_pos _).le
    _ = 2 * Real.exp (3 * x) := by
      rw [show 3 * x = 2 * x + x by ring, Real.exp_add]
      ring
    _ = _ := by rw [hex]

/-- The radius square bound with source constant two. -/
theorem witnessDimension_mul_one_add_log_le {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) :
    (d : ℝ) ^ 4 * (1 + Real.log (witnessCoordinateBudget d K : ℝ)) ≤
      2 * witnessCoordinateBudget d K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdim := sixth_power_le_witnessCoordinateBudget hK
  have hP : (1 : ℝ) ≤ witnessCoordinateBudget d K := (one_le_pow₀ hd1).trans hdim
  apply mul_one_add_log_le_twice_of_cube_le hP (by positivity)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (d : ℝ) ^ 6) hdim 2
  nlinarith only [hpow]

theorem witnessDimension_le_coordinateBudget {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) : (d : ℝ) ^ 4 ≤ witnessCoordinateBudget d K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  exact (pow_le_pow_right₀ hd1 (by decide : 4 ≤ 6)).trans (sixth_power_le_witnessCoordinateBudget hK)

theorem one_le_coordinateBudget_of_quarter {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) : (1 : ℝ) ≤ witnessCoordinateBudget d K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  exact (one_le_pow₀ hd1).trans (sixth_power_le_witnessCoordinateBudget hK)

/-- The source's radius bound, with no hidden dimension-dependent multiplier. -/
theorem freezing_radius_le {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) {e : ℝ} (_he : 0 ≤ e) :
    (d : ℝ) * Real.sqrt (2 * e) + Real.sqrt (2 * e) * witnessCoordinateBudget d K ≤
      2 * Real.sqrt 2 * witnessCoordinateBudget d K * Real.sqrt e := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd6 : (d : ℝ) ≤ (d : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1 ≤ 6)
  have hdP : (d : ℝ) ≤ witnessCoordinateBudget d K :=
    hd6.trans (sixth_power_le_witnessCoordinateBudget hK)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [mul_le_mul_of_nonneg_right hdP (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg e))]

theorem sqrt_pow_eq_exp_log {e : ℝ} (he : 0 < e) (k : ℕ) :
    (Real.sqrt e) ^ k = Real.exp ((k : ℝ) / 2 * Real.log e) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos he, ← Real.exp_nat_mul]
  congr 1
  ring

end NLQCLean
