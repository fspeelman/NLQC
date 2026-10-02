import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# All-error arithmetic for the restricted strong Haar bound

Put `δ = √(21e/2)`, `x = K/D` and
`u = 32 δ √(1 + x)`, with `D = d²`, `N = d⁴`, `K ≥ D/2`.

* Small radius (`e ≤ 1/16`, `u ≤ 1/64`): the per-shape bound times the `K³` shapes is at most
  `exp((68 C₀ + 21) K²) e^(N/16)`, using `N ≤ 4K²`, `N x ≤ 2K²`, `N − b ≥ N/8`, `δ ≤ 1`.
* Large radius or `e > 1/16`: `exp(C K²) e^(N/16) ≥ 1` for every `C ≥ 21`.

Real powers are used for the error exponent; no `δ ≤ 1` lemma is applied outside the
small-radius regime.
-/

namespace NLQCLean

theorem strong_numeric_exp_bounds :
    (18 : ℝ) ≤ Real.exp 3 ∧ (32 : ℝ) ≤ Real.exp 4 ∧ (75497472 : ℝ) ≤ Real.exp 19 := by
  have h27 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hk : ∀ k : ℕ, k ≠ 0 → (2.7 : ℝ) ^ k < Real.exp (k : ℝ) := fun k hk => by
    rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by rw [← Real.exp_nat_mul]; simp]
    exact pow_lt_pow_left₀ h27 (by norm_num) hk
  refine ⟨?_, ?_, ?_⟩
  · have h := hk 3 (by norm_num); norm_num at h ⊢; linarith
  · have h := hk 4 (by norm_num); norm_num at h ⊢; linarith
  · have h := hk 19 (by norm_num); norm_num at h ⊢; linarith

theorem sqrt_div_sq_le_sqrt_one_add {d K : ℕ} (hd : 0 < d) :
    Real.sqrt K / d ≤ Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h : Real.sqrt K / d = Real.sqrt (K / (d : ℝ) ^ 2) := by
    rw [Real.sqrt_div (Nat.cast_nonneg K), Real.sqrt_sq hd0.le]
  rw [h]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Small-radius regime: shape count, the strong tube bound and all constants absorbed into `exp(C K²)`. -/
theorem strong_small_radius_arith {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {d K b : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 2 ≤ K) (hb : 8 * b ≤ 7 * d ^ 4) {e : ℝ} (he : 0 < e)
    (hu : 32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64) :
    (K : ℝ) ^ 3 * (Real.exp (C₀ * (64 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) *
      ((4 + 32 * Real.sqrt (21 / 2 * e)) * Real.sqrt K / d +
        2 * (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^ b *
      (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^ (d ^ 4 - b)) ≤
    Real.exp ((68 * C₀ + 21) * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16) := by
  obtain ⟨h18, h32, -⟩ := strong_numeric_exp_bounds
  have hsK := sqrt_div_sq_le_sqrt_one_add (K := K) (by omega : 0 < d)
  set δ := Real.sqrt (21 / 2 * e) with hδdef
  set x := (K : ℝ) / (d : ℝ) ^ 2 with hxdef
  set w := Real.sqrt (1 + x) with hwdef
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hd4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
  have hw1 : 1 ≤ w := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ w := Real.sqrt_le_sqrt (by linarith)
  have hw0 : 0 ≤ w := by linarith
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδs : 96 * δ ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hw1 hδ0.le]
  have hδ1 : δ ≤ 1 := by linarith
  have hbN : b ≤ d ^ 4 := by omega
  have hbase : (4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w) ≤ 32 * w := by
    rw [mul_div_assoc]
    linarith [mul_le_mul_of_nonneg_left hsK (by positivity : (0 : ℝ) ≤ 4 + 32 * δ),
      mul_le_mul_of_nonneg_right hδs hw0, mul_nonneg hδ0.le hw0]
  have hA0 : 0 ≤ (4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w) := by positivity
  have hu' : (32 * δ * w) ^ (d ^ 4 - b) = (32 * w) ^ (d ^ 4 - b) * δ ^ (d ^ 4 - b) := by
    rw [← mul_pow]; ring
  have hpow : ((4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w)) ^ b * (32 * δ * w) ^ (d ^ 4 - b) ≤
      (32 * w) ^ (d ^ 4) * δ ^ (d ^ 4 - b) := by
    rw [hu']
    calc _ ≤ (32 * w) ^ b * ((32 * w) ^ (d ^ 4 - b) * δ ^ (d ^ 4 - b)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0 hbase b) (by positivity)
      _ = (32 * w) ^ (d ^ 4) * δ ^ (d ^ 4 - b) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hbN]
  have hNR : ((d ^ 4 : ℕ) : ℝ) = (d : ℝ) ^ 4 := by push_cast; ring
  have hNK : (d : ℝ) ^ 4 ≤ 4 * (K : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) h2K 2
    calc (d : ℝ) ^ 4 = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (K : ℝ)) ^ 2 := h
      _ = 4 * (K : ℝ) ^ 2 := by ring
  have hNx : (d : ℝ) ^ 4 * x ≤ 2 * (K : ℝ) ^ 2 := by
    have : (d : ℝ) ^ 4 * x = (d : ℝ) ^ 2 * K := by rw [hxdef]; field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_right h2K (Nat.cast_nonneg K)
    linarith
  have hδpow : δ ^ (d ^ 4 - b) ≤ (21 / 2 : ℝ) ^ ((d : ℝ) ^ 4 / 16) * e ^ ((d : ℝ) ^ 4 / 16) := by
    have hexp : (d : ℝ) ^ 4 / 8 ≤ ((d ^ 4 - b : ℕ) : ℝ) := by
      rw [Nat.cast_sub hbN, hNR]
      have : (8 * b : ℝ) ≤ 7 * (d : ℝ) ^ 4 := by exact_mod_cast hb
      linarith
    calc δ ^ (d ^ 4 - b) = δ ^ (((d ^ 4 - b : ℕ)) : ℝ) := (Real.rpow_natCast δ _).symm
      _ ≤ δ ^ ((d : ℝ) ^ 4 / 8) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
      _ = (21 / 2 * e) ^ ((d : ℝ) ^ 4 / 16) := by
          rw [hδdef, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1; ring
      _ = _ := Real.mul_rpow (by norm_num) he.le
  have hbaseN : (21 / 2 : ℝ) ^ ((d : ℝ) ^ 4 / 16) ≤ Real.exp ((K : ℝ) ^ 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hl : Real.log (21 / 2) ≤ 3 :=
      (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)
    linarith [mul_le_mul_of_nonneg_right hl (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4 / 16)]
  have hw_exp : w ≤ Real.exp (x / 2) := by
    rw [hwdef, Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp x])
  have h32N : (32 * w) ^ (d ^ 4) ≤ Real.exp (17 * (K : ℝ) ^ 2) := by
    have h1 : (32 : ℝ) ^ (d ^ 4) ≤ Real.exp (16 * (K : ℝ) ^ 2) := by
      calc (32 : ℝ) ^ (d ^ 4) ≤ Real.exp 4 ^ (d ^ 4) := pow_le_pow_left₀ (by norm_num) h32 _
        _ = Real.exp (4 * (d : ℝ) ^ 4) := by rw [← Real.exp_nat_mul, hNR]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have h2 : w ^ (d ^ 4) ≤ Real.exp ((K : ℝ) ^ 2) := by
      calc w ^ (d ^ 4) ≤ Real.exp (x / 2) ^ (d ^ 4) := pow_le_pow_left₀ hw0 hw_exp _
        _ = Real.exp ((d : ℝ) ^ 4 * x / 2) := by rw [← Real.exp_nat_mul, hNR]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc (32 * w) ^ (d ^ 4) = 32 ^ (d ^ 4) * w ^ (d ^ 4) := mul_pow _ _ _
      _ ≤ Real.exp (16 * (K : ℝ) ^ 2) * Real.exp ((K : ℝ) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK3 : (K : ℝ) ^ 3 ≤ Real.exp (3 * (K : ℝ) ^ 2) := by
    have h1 : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    calc (K : ℝ) ^ 3 ≤ Real.exp K ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg K) h1 3
      _ = Real.exp (3 * K) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by
          have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := le_self_pow₀ hK1 (by norm_num)
          linarith)
  have hP : Real.exp (C₀ * (64 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) ≤ Real.exp (68 * C₀ * (K : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hNK hC₀])
  have hE := mul_le_mul hP hpow (by positivity) (by positivity)
  calc (K : ℝ) ^ 3 * (Real.exp (C₀ * (64 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) *
        ((4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w)) ^ b * (32 * δ * w) ^ (d ^ 4 - b))
      = (K : ℝ) ^ 3 * (Real.exp (C₀ * (64 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) *
        (((4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w)) ^ b * (32 * δ * w) ^ (d ^ 4 - b))) := by
        ring
    _ ≤ Real.exp (3 * (K : ℝ) ^ 2) * (Real.exp (68 * C₀ * (K : ℝ) ^ 2) *
        ((32 * w) ^ (d ^ 4) * δ ^ (d ^ 4 - b))) :=
        mul_le_mul hK3 hE (by positivity) (by positivity)
    _ ≤ Real.exp (3 * (K : ℝ) ^ 2) * (Real.exp (68 * C₀ * (K : ℝ) ^ 2) *
        (Real.exp (17 * (K : ℝ) ^ 2) * (Real.exp ((K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16)))) := by
        gcongr
        all_goals first
          | exact h32N
          | exact hδpow.trans (mul_le_mul_of_nonneg_right hbaseN (by positivity))
    _ = _ := by
        rw [show (68 * C₀ + 21) * (K : ℝ) ^ 2 =
          3 * (K : ℝ) ^ 2 + (68 * C₀ * (K : ℝ) ^ 2 + (17 * (K : ℝ) ^ 2 + (K : ℝ) ^ 2)) by ring,
          Real.exp_add, Real.exp_add, Real.exp_add]
        ring

/-- Large-radius or large-error regime: the claimed right side is at least one. -/
theorem one_le_strong_haar_rhs {C : ℝ} (hC : 21 ≤ C) {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 2 ≤ K) {e : ℝ} (he : 0 < e)
    (hcase : ¬ (e ≤ 1 / 16 ∧ 32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64)) :
    1 ≤ Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16) := by
  obtain ⟨h18, -, h19⟩ := strong_numeric_exp_bounds
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hd4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
  have hNK : (d : ℝ) ^ 4 ≤ 4 * (K : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) h2K 2
    calc (d : ℝ) ^ 4 = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (K : ℝ)) ^ 2 := h
      _ = 4 * (K : ℝ) ^ 2 := by ring
  set x := (K : ℝ) / (d : ℝ) ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hNx : (d : ℝ) ^ 4 * x ≤ 2 * (K : ℝ) ^ 2 := by
    have : (d : ℝ) ^ 4 * x = (d : ℝ) ^ 2 * K := by rw [hxdef]; field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_right h2K hK0
    linarith
  have hCK : 21 * (K : ℝ) ^ 2 ≤ C * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  have hN0 : (0 : ℝ) ≤ (d : ℝ) ^ 4 / 16 := by positivity
  have key : (d : ℝ) ^ 4 / 16 * Real.log (1 / e) ≤ C * (K : ℝ) ^ 2 := by
    by_cases he16 : e ≤ 1 / 16
    · have hlarge : 1 / 64 < 32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + x) := by
        by_contra h
        exact hcase ⟨he16, not_lt.mp h⟩
      have hprod : (1 / 2048 : ℝ) < Real.sqrt (21 / 2 * e) * Real.sqrt (1 + x) := by linarith
      have hsq : (1 / 2048 : ℝ) ^ 2 < 21 / 2 * e * (1 + x) := by
        have h := pow_lt_pow_left₀ hprod (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
        rwa [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
      have hinv : 1 / e < 75497472 * (1 + x) := by
        rw [div_lt_iff₀ he]
        linarith
      have hlog : Real.log (1 / e) ≤ 19 + x := by
        have h1 := Real.log_lt_log (by positivity) hinv
        rw [Real.log_mul (by norm_num) (by positivity)] at h1
        have h2 : Real.log 75497472 ≤ 19 := (Real.log_le_iff_le_exp (by norm_num)).mpr h19
        have h3 : Real.log (1 + x) ≤ x := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + x)
          linarith
        linarith
      calc (d : ℝ) ^ 4 / 16 * Real.log (1 / e) ≤ (d : ℝ) ^ 4 / 16 * (19 + x) :=
            mul_le_mul_of_nonneg_left hlog hN0
        _ ≤ C * (K : ℝ) ^ 2 := by linarith
    · have hinv : 1 / e < 16 := by
        rw [div_lt_iff₀ he]
        linarith
      have hlog : Real.log (1 / e) ≤ 3 := by
        have h1 := Real.log_lt_log (by positivity) hinv
        have h2 : Real.log 16 ≤ 3 := (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)
        linarith
      calc (d : ℝ) ^ 4 / 16 * Real.log (1 / e) ≤ (d : ℝ) ^ 4 / 16 * 3 :=
            mul_le_mul_of_nonneg_left hlog hN0
        _ ≤ C * (K : ℝ) ^ 2 := by linarith
  rw [Real.rpow_def_of_pos he, ← Real.exp_add, Real.one_le_exp_iff]
  rw [one_div, Real.log_inv] at key
  linarith

end NLQCLean
