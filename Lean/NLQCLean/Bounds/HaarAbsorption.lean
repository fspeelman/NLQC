import NLQCLean.Bounds.HaarArithmetic

/-!
# Both numerical regimes of the Haar estimate

One exponential prefactor handles the small tube estimate and the
probability bound when the tube radius exceeds one half.
-/

namespace NLQCLean

/-- Absorb all small-radius dimension factors with a universal multiple of CP. -/
theorem small_radius_prefactor_le {N t : ℕ} (ht : t ≤ N) {C P r e : ℝ}
    (hC : 1 ≤ C) (hP : 1 ≤ P) (hNP : (N : ℝ) ≤ P)
    (hlog : (N : ℝ) * (1 + Real.log P) ≤ 2 * P)
    (he : 0 < e) (hr : 0 ≤ r) (hrP : r ≤ 4 * P * Real.sqrt e) :
    Real.exp (3 * P) * Real.exp (C * (P + N)) * (C * P) ^ t * (C * r) ^ (N - t) ≤
      Real.exp (16 * C * P) * Real.exp (((N - t : ℕ) : ℝ) / 2 * Real.log e) := by
  have hC0 : 0 ≤ C := by linarith
  have hP0 : 0 < P := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlogC : Real.log C ≤ C := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < C)]
  have hlog4 : Real.log 4 ≤ (4 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlogs : Real.log (4 * C * P) = Real.log 4 + Real.log C + Real.log P := by
    rw [Real.log_mul (by positivity) hP0.ne', Real.log_mul (by norm_num) (by positivity)]
  have hexp : 3 * P + C * (P + N) + (N : ℝ) * Real.log (4 * C * P) ≤ 16 * C * P := by
    rw [hlogs]
    have hnc := mul_le_mul_of_nonneg_left hlogC hN0
    have hn4 := mul_le_mul_of_nonneg_left hlog4 hN0
    have hcp := mul_le_mul_of_nonneg_left hNP hC0
    have hpc : P ≤ C * P := by nlinarith
    nlinarith
  have hpow : (4 * C * P) ^ N = Real.exp ((N : ℝ) * Real.log (4 * C * P)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp (3 * P) * Real.exp (C * (P + N)) *
        (4 * C * P) ^ t * ((4 * C * P) * Real.sqrt e) ^ (N - t) := by
      have ha : C * P ≤ 4 * C * P := by nlinarith
      have hb : C * r ≤ (4 * C * P) * Real.sqrt e := by
        calc
          _ ≤ C * (4 * P * Real.sqrt e) := mul_le_mul_of_nonneg_left hrP hC0
          _ = _ := by ring
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha t) (by positivity))
        (pow_le_pow_left₀ (mul_nonneg hC0 hr) hb (N - t)) (by positivity) (by positivity)
    _ = (Real.exp (3 * P) * Real.exp (C * (P + N)) * (4 * C * P) ^ N) *
        (Real.sqrt e) ^ (N - t) := by
      have hs : (4 * C * P) ^ t * (4 * C * P) ^ (N - t) = (4 * C * P) ^ N := by
        rw [← pow_add, Nat.add_sub_of_le ht]
      rw [mul_pow (4 * C * P) (Real.sqrt e), ← hs]
      ring
    _ = Real.exp (3 * P + C * (P + N) + (N : ℝ) * Real.log (4 * C * P)) *
        Real.exp (((N - t : ℕ) : ℝ) / 2 * Real.log e) := by
      rw [hpow, sqrt_pow_eq_exp_log he, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le

/-- A radius larger than one half forces the source's dimension-dependent error lower bound. -/
theorem error_lower_of_large_radius {P r e : ℝ} (_hP : 0 < P) (he : 0 < e)
    (hr : 1 / 2 < r) (hrP : r ≤ 2 * Real.sqrt 2 * P * Real.sqrt e) :
    1 < 32 * P ^ 2 * e := by
  have hs : (2 * Real.sqrt 2 * P * Real.sqrt e) ^ 2 = 8 * P ^ 2 * e := by
    calc
      _ = 4 * (Real.sqrt 2) ^ 2 * P ^ 2 * (Real.sqrt e) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt he.le]; ring
  have hhalf : 1 / 2 < 2 * Real.sqrt 2 * P * Real.sqrt e := hr.trans_le hrP
  nlinarith

/-- The same exponential prefactor is at least one in the other radius regime. -/
theorem one_le_large_radius_rhs {N k : ℕ} (hk : k ≤ N) {C P r e : ℝ}
    (hC : 1 ≤ C) (hP : 1 ≤ P) (hNP : (N : ℝ) ≤ P)
    (hlog : (N : ℝ) * (1 + Real.log P) ≤ 2 * P)
    (he : 0 < e) (he1 : e ≤ 1) (hr : 1 / 2 < r)
    (hrP : r ≤ 2 * Real.sqrt 2 * P * Real.sqrt e) :
    1 ≤ Real.exp (16 * C * P) * Real.exp ((k : ℝ) / 2 * Real.log e) := by
  have hP0 : 0 < P := by linarith
  have hlow := (error_lower_of_large_radius hP0 he hr hrP).le
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hlow
  rw [Real.log_one, Real.log_mul (by positivity) he.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog32 : Real.log (32 : ℝ) ≤ 5 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 5) := by norm_num
      _ = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hloge : Real.log e ≤ 0 := Real.log_nonpos he.le he1
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hkn := mul_le_mul_of_nonneg_right hkR (neg_nonneg.mpr hloge)
  have hn := mul_le_mul_of_nonneg_left (show -Real.log e ≤ 5 + 2 * Real.log P by linarith)
    (Nat.cast_nonneg N)
  have hCP : P ≤ C * P := by nlinarith
  rw [← Real.exp_add, Real.one_le_exp_iff]
  nlinarith

end NLQCLean
