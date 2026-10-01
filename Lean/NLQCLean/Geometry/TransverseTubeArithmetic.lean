import NLQCLean.Geometry.UnitaryNormalVolume
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Arithmetic of the transverse tube exponent

Cancel exactly N powers of the normal radius. All remaining
dimension-dependent fixed bases are absorbed in one universal constant.
-/

namespace NLQCLean

/-- The full 2N-dimensional Jacobian leaves N-t powers after normal-volume cancellation. -/
theorem thickenedJacobian_le_transverse {N t : ℕ} (ht : t ≤ N)
    {Λ μ r : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (hμr : μ ≤ r)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) :
    (Λ + 2 * r) ^ t * (μ + 2 * r) ^ (2 * N - t) ≤
      r ^ N * ((2 * Λ) ^ t * 9 ^ N * r ^ (N - t)) := by
  have hΛ' : Λ + 2 * r ≤ 2 * Λ := by linarith
  have hμ' : μ + 2 * r ≤ 3 * r := by linarith
  have hexp : 2 * N - t = N + (N - t) := by omega
  calc
    _ ≤ (2 * Λ) ^ t * (3 * r) ^ (2 * N - t) := by gcongr
    _ = (2 * Λ) ^ t * (3 ^ (2 * N - t) * r ^ (2 * N - t)) := by rw [mul_pow (3 : ℝ) r]
    _ ≤ (2 * Λ) ^ t * (3 ^ (2 * N) * r ^ (2 * N - t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.sub_le _ _))
        (pow_nonneg hr _)) (pow_nonneg (by linarith) _)
    _ = _ := by rw [hexp, pow_add, pow_mul]; norm_num; ring

/-- A single fixed exponential absorbs the normal determinant and image-volume constants. -/
theorem transverse_fixed_base_le_exp {C : ℝ} (hC : 1 ≤ C) (P N : ℕ) :
    16 ^ N * C ^ (P + 4 * N) * 9 ^ N ≤
      Real.exp ((144 * C ^ 4) * (P + N)) := by
  have hC0 : 0 ≤ C := by linarith
  have hbase : 0 ≤ 144 * C ^ 4 := by positivity
  calc
    _ = 144 ^ N * C ^ (P + 4 * N) := by
      rw [show (144 : ℝ) = 16 * 9 by norm_num, mul_pow]
      ring
    _ ≤ 144 ^ (P + N) * C ^ (4 * (P + N)) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 144) (by omega))
        (pow_le_pow_right₀ hC (by omega)) (by positivity) (by positivity)
    _ = (144 * C ^ 4) ^ (P + N) := by rw [mul_pow, ← pow_mul]
    _ ≤ (Real.exp (144 * C ^ 4)) ^ (P + N) := by
      gcongr
      linarith [Real.add_one_le_exp (144 * C ^ 4)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

open MeasureTheory
open scoped ENNReal

/-- Cancellation is legitimate because the Euclidean ball volume is positive and finite. -/
theorem cancel_normal_tube_volume {N : ℕ} {r A B : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) {h : ℝ≥0∞}
    (hh : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * euclideanUnitBallVolume N ^ 2 *
      ENNReal.ofReal r ^ N * h ≤
        ENNReal.ofReal A * euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal (r ^ N * B)) :
    h ≤ ENNReal.ofReal (16 ^ N * A * B) := by
  have hw0 : euclideanUnitBallVolume N ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : RealEuclidean N) zero_lt_one).ne'
  have hwt : euclideanUnitBallVolume N ≠ ∞ := measure_ball_lt_top.ne
  have hf0 : euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal r ^ N ≠ 0 := by
    have hwpos : 0 < euclideanUnitBallVolume N := pos_iff_ne_zero.mpr hw0
    positivity
  have hft : euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal r ^ N ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hc0 : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) ≠ 0 := by positivity
  have he : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * ENNReal.ofReal (16 ^ N * A * B) =
      ENNReal.ofReal A * ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 16) ^ N),
      ← ENNReal.ofReal_mul hA]
    congr 1
    calc
      _ = (((1 / 16 : ℝ) * 16) ^ N) * (A * B) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  apply (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp
  rw [he]
  apply (ENNReal.mul_le_mul_iff_left hf0 hft).mp
  calc
    _ = ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * euclideanUnitBallVolume N ^ 2 *
        ENNReal.ofReal r ^ N * h := by ring
    _ ≤ _ := hh
    _ = _ := by rw [ENNReal.ofReal_mul (pow_nonneg hr.le _), ENNReal.ofReal_pow hr.le]; ring

end NLQCLean
