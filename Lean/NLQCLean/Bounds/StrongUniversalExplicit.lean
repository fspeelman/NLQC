import NLQCLean.Geometry.StrongWitnessBarrierVolume
import NLQCLean.Bounds.StrongUniversalResources

/-!
# Explicit constants for the universal unitary bounds

The near-SWAP Haar estimate is made explicit using the following inputs:

* the barrier image-volume bound at the actual witness degrees (base `2·82 = 164` per source
  coordinate);
* the slim coordinate count `P = 38 K²`;
* the uncontrolled rank bound `16 b ≤ 13 N` (and `8 b ≤ N` for `d ≥ 8`).

The coefficients of `K²` and `N = d⁴` are kept separate:

  `μ_d(S_d ∩ Reach(d,K,ε)) ≤ exp((595/3) K² + (341/10 + γ) N) ε^(κN)`,

with `(κ, γ) = (3/32, 1/4)` for `d ≥ 2` and `(7/16, 21/20)` for `d ≥ 8`. Comparing with the
patch mass `exp(−5N)` gives `κ N ln(1/ε) ≤ (595/3) K² + (B + 5) N`. With the SWAP floor
`K ≥ d²(1 − ε)` this yields, for universal pure or common-map mixed score implementation and
for normalized diamond implementation:

* `K ≥ d² max(1 − ε, √ln(1/ε)/51, √(ln(1/ε) − 420)/46)` for every `d ≥ 2`;
* `K ≥ d² max(1 − ε, √ln(1/ε)/24, √(ln(1/ε) − 92)/22)` for every `d ≥ 8`;
* `log₂ K ≥ 2n + ½ log₂ ln(1/ε) − 6` at `d = 2ⁿ`, and `− 5` once `n ≥ 3`.

The restricted Haar bound holds in the original form with `C = 336`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-! ### Numerical facts -/

theorem pow_le_exp_nat_of_d9 (k : ℕ) : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k

/-- `x ≤ exp(k/n)` from `xⁿ ≤ 2.7182818283ᵏ`. -/
theorem le_exp_div_of_pow_le {x : ℝ} (hx : 0 ≤ x) {k n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ≤ (2.7182818283 : ℝ) ^ k) : x ≤ Real.exp ((k : ℝ) / n) := by
  have hpow : x ^ n ≤ Real.exp ((k : ℝ) / n) ^ n := by
    rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn)]
    exact h.trans (pow_le_exp_nat_of_d9 k)
  exact (pow_le_pow_iff_left₀ hx (Real.exp_pos _).le hn).mp hpow

theorem explicit_numeric_bounds :
    (164 : ℝ) ≤ Real.exp (31 / 6) ∧ (533344529940480 : ℝ) ≤ Real.exp 34 ∧
      Real.log (21 / 2) ≤ 12 / 5 ∧ (4 : ℝ) ≤ Real.exp (8 / 5) ∧ (403 : ℝ) ≤ Real.exp 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := le_exp_div_of_pow_le (x := 164) (by norm_num) (k := 31) (n := 6) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  · have h := le_exp_div_of_pow_le (x := 533344529940480) (by norm_num) (k := 34) (n := 1)
      (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := le_exp_div_of_pow_le (x := 21 / 2) (by norm_num) (k := 12) (n := 5) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  · have h := le_exp_div_of_pow_le (x := 4) (by norm_num) (k := 8) (n := 5) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  · have h := le_exp_div_of_pow_le (x := 403) (by norm_num) (k := 6) (n := 1) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h

/-! ### The uncontrolled rank -/

/-- `N − b ≥ 3N/16` for every `d ≥ 2` (equality at `d = 2`). -/
theorem sixteen_mul_strongUncontrolledRank_le {d : ℕ} (hd : 2 ≤ d) :
    16 * strongUncontrolledRank d ≤ 13 * d ^ 4 := by
  have h4 : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  unfold strongUncontrolledRank
  rw [h4]
  have hD : 4 ≤ d ^ 2 := by nlinarith
  generalize d ^ 2 = D at hD ⊢
  have ht : 64 * (D / 64) ≤ D := Nat.mul_div_le D 64
  have hsub : 4 * D - 3 + 3 = 4 * D := by omega
  rcases Nat.lt_or_ge D 64 with hlt | hge
  · rw [Nat.div_eq_of_lt hlt]
    generalize 4 * D - 3 = w at hsub ⊢
    obtain ⟨E, rfl⟩ : ∃ E, D = E + 4 := ⟨D - 4, by omega⟩
    have hw : w = 4 * E + 13 := by omega
    subst hw
    nlinarith
  · generalize D / 64 = t at ht ⊢
    generalize 4 * D - 3 = w at hsub ⊢
    have hDt : 64 * (D * t) ≤ D * D := by nlinarith
    have : 64 * D ≤ D * D := Nat.mul_le_mul_right D hge
    nlinarith

/-- `N − b ≥ 7N/8` once `d ≥ 8`. -/
theorem eight_mul_strongUncontrolledRank_le_of_eight {d : ℕ} (hd : 8 ≤ d) :
    8 * strongUncontrolledRank d ≤ d ^ 4 := by
  have h4 : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  unfold strongUncontrolledRank
  rw [h4]
  have hD : 64 ≤ d ^ 2 := by nlinarith
  generalize d ^ 2 = D at hD ⊢
  have ht : 64 * (D / 64) ≤ D := Nat.mul_div_le D 64
  have hsub : 4 * D - 3 + 3 = 4 * D := by omega
  generalize D / 64 = t at ht ⊢
  generalize 4 * D - 3 = w at hsub ⊢
  have hDt : 64 * (D * t) ≤ D * D := by nlinarith
  have : 64 * D ≤ D * D := Nat.mul_le_mul_right D hD
  nlinarith

theorem two_mul_kappa_le_of_sixteen {d : ℕ} (hd : 2 ≤ d) :
    2 * (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ ((d ^ 4 - strongUncontrolledRank d : ℕ) : ℝ) := by
  have h := sixteen_mul_strongUncontrolledRank_le hd
  have hb : strongUncontrolledRank d ≤ d ^ 4 := by omega
  rw [Nat.cast_sub hb]
  have h' : (16 * strongUncontrolledRank d : ℝ) ≤ 13 * (d : ℝ) ^ 4 := by exact_mod_cast h
  push_cast
  linarith

theorem two_mul_kappa_le_of_eight {d : ℕ} (hd : 8 ≤ d) :
    2 * (7 / 16 : ℝ) * (d : ℝ) ^ 4 ≤ ((d ^ 4 - strongUncontrolledRank d : ℕ) : ℝ) := by
  have h := eight_mul_strongUncontrolledRank_le_of_eight hd
  have hb : strongUncontrolledRank d ≤ d ^ 4 := by omega
  rw [Nat.cast_sub hb]
  have h' : (8 * strongUncontrolledRank d : ℝ) ≤ (d : ℝ) ^ 4 := by exact_mod_cast h
  push_cast
  linarith

/-! ### All-error arithmetic with separate coefficients -/

/-- `x³ ≤ exp(x²)` for real `x ≥ 0`. -/
theorem cube_le_exp_sq {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ Real.exp (x ^ 2) := by
  have h1 : x ≤ Real.exp (x ^ 2 / 3) := by
    have := Real.add_one_le_exp (x ^ 2 / 3)
    nlinarith [sq_nonneg (x - 3 / 2)]
  calc x ^ 3 ≤ Real.exp (x ^ 2 / 3) ^ 3 := pow_le_pow_left₀ hx h1 3
    _ = Real.exp (x ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- The fixed volume factors: `1024ᴺ 9ᴺ 2^(P+2N) 82^(P+4N) 10ᴺ 32ᴺ = 164^P M^N`. -/
theorem sharp_volume_factor_le (P N : ℕ) :
    (1024 : ℝ) ^ N * 9 ^ N * (((2 ^ (P + 2 * N) * 82 ^ (P + 4 * N) : ℕ) : ℝ) *
      Real.sqrt 10 ^ (2 * N)) * 32 ^ N ≤
      Real.exp (31 / 6 * (P : ℝ)) * Real.exp (34 * (N : ℝ)) := by
  obtain ⟨h164, hM, -⟩ := explicit_numeric_bounds
  have h10 : Real.sqrt 10 ^ (2 * N) = (10 : ℝ) ^ N := by
    rw [pow_mul, Real.sq_sqrt (by norm_num)]
  have hsplit : (1024 : ℝ) ^ N * 9 ^ N * (((2 ^ (P + 2 * N) * 82 ^ (P + 4 * N) : ℕ) : ℝ) *
      Real.sqrt 10 ^ (2 * N)) * 32 ^ N = (164 : ℝ) ^ P * 533344529940480 ^ N := by
    rw [h10]
    push_cast
    rw [show (164 : ℝ) = 2 * 82 by norm_num,
      show (533344529940480 : ℝ) = 2 ^ 2 * 82 ^ 4 * 10 * 1024 * 9 * 32 by norm_num,
      mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
      pow_add, pow_add]
    ring
  rw [hsplit]
  have hP : (164 : ℝ) ^ P ≤ Real.exp (31 / 6 * (P : ℝ)) := by
    calc (164 : ℝ) ^ P ≤ Real.exp (31 / 6) ^ P := pow_le_pow_left₀ (by norm_num) h164 P
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hN : (533344529940480 : ℝ) ^ N ≤ Real.exp (34 * (N : ℝ)) := by
    calc (533344529940480 : ℝ) ^ N ≤ Real.exp 34 ^ N := pow_le_pow_left₀ (by norm_num) hM N
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  exact mul_le_mul hP hN (by positivity) (by positivity)

/-- Small-radius regime: the `K³` shapes times the sharp tube bound, with separate
coefficients for `K²` and `N` and error exponent `κN`. -/
theorem sharp_small_radius_arith {d K b : ℕ} (hd : 2 ≤ d) (hK : (d : ℝ) ^ 2 / 2 ≤ K)
    (hbN : b ≤ d ^ 4) {κ γ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : 2 * κ * (d : ℝ) ^ 4 ≤ ((d ^ 4 - b : ℕ) : ℝ)) (hγ : κ * (12 / 5) ≤ γ)
    {e : ℝ} (he : 0 < e)
    (hu : 32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64) :
    (K : ℝ) ^ 3 * ((4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) *
        ((((2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
          82 ^ (slimCoordinateBudget K + 4 * d ^ 4) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * d ^ 4))) *
      (((4 + 32 * Real.sqrt (21 / 2 * e)) * Real.sqrt K / d +
        2 * (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^ b *
      (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^ (d ^ 4 - b))) ≤
    Real.exp (595 / 3 * (K : ℝ) ^ 2 + (341 / 10 + γ) * (d : ℝ) ^ 4) * e ^ (κ * (d : ℝ) ^ 4) := by
  obtain ⟨-, -, h105, h4, -⟩ := explicit_numeric_bounds
  have hsK := sqrt_div_sq_le_sqrt_one_add (K := K) (by omega : 0 < d)
  set δ := Real.sqrt (21 / 2 * e) with hδdef
  set x := (K : ℝ) / (d : ℝ) ^ 2 with hxdef
  set w := Real.sqrt (1 + x) with hwdef
  set V : ℝ := (((2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
    82 ^ (slimCoordinateBudget K + 4 * d ^ 4) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * d ^ 4) with hVdef
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hd4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
  have hw1 : 1 ≤ w := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ w := Real.sqrt_le_sqrt (by linarith)
  have hw0 : 0 ≤ w := by linarith
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδs : 96 * δ ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hw1 hδ0.le]
  have hδ1 : δ ≤ 1 := by linarith
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
  have hNx : (d : ℝ) ^ 4 * x ≤ 2 * (K : ℝ) ^ 2 := by
    have : (d : ℝ) ^ 4 * x = (d : ℝ) ^ 2 * K := by rw [hxdef]; field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_right h2K hK0
    linarith
  -- the error factor
  have hδpow : δ ^ (d ^ 4 - b) ≤ Real.exp (γ * (d : ℝ) ^ 4) * e ^ (κ * (d : ℝ) ^ 4) := by
    calc δ ^ (d ^ 4 - b) = δ ^ (((d ^ 4 - b : ℕ)) : ℝ) := (Real.rpow_natCast δ _).symm
      _ ≤ δ ^ (2 * κ * (d : ℝ) ^ 4) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hκ
      _ = (21 / 2 * e) ^ (κ * (d : ℝ) ^ 4) := by
          rw [hδdef, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1; ring
      _ = (21 / 2 : ℝ) ^ (κ * (d : ℝ) ^ 4) * e ^ (κ * (d : ℝ) ^ 4) :=
          Real.mul_rpow (by norm_num) he.le
      _ ≤ _ := by
          gcongr
          rw [Real.rpow_def_of_pos (by norm_num)]
          apply Real.exp_le_exp.mpr
          have h1 : Real.log (21 / 2) * κ ≤ γ := by nlinarith
          nlinarith [pow_nonneg hd0.le 4]
  -- the dimension factor
  have hw_exp : w ≤ Real.exp (x / 2) := by
    rw [hwdef, Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp x])
  have hwN : w ^ (d ^ 4) ≤ Real.exp ((K : ℝ) ^ 2) := by
    calc w ^ (d ^ 4) ≤ Real.exp (x / 2) ^ (d ^ 4) := pow_le_pow_left₀ hw0 hw_exp _
      _ = Real.exp ((d : ℝ) ^ 4 * x / 2) := by rw [← Real.exp_nat_mul, hNR]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hK3 : (K : ℝ) ^ 3 ≤ Real.exp ((K : ℝ) ^ 2) := cube_le_exp_sq hK0
  have hfour : (4 : ℝ) ≤ Real.exp ((d : ℝ) ^ 4 / 10) := by
    refine h4.trans (Real.exp_le_exp.mpr ?_)
    have := pow_le_pow_left₀ (by norm_num) hdR 4
    norm_num at this
    linarith
  have hvol := sharp_volume_factor_le (slimCoordinateBudget K) (d ^ 4)
  rw [← hVdef] at hvol
  have hP : ((slimCoordinateBudget K : ℕ) : ℝ) = 38 * (K : ℝ) ^ 2 := by
    simp [slimCoordinateBudget]
  rw [hP, hNR] at hvol
  have hprod := mul_le_mul hK3 (mul_le_mul hfour (mul_le_mul hvol
    (mul_le_mul hwN hδpow (by positivity) (by positivity)) (by positivity) (by positivity))
    (by positivity) (by positivity)) (by positivity) (by positivity)
  calc (K : ℝ) ^ 3 * ((4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) * V) *
        (((4 + 32 * δ) * Real.sqrt K / d + 2 * (32 * δ * w)) ^ b * (32 * δ * w) ^ (d ^ 4 - b)))
      ≤ (K : ℝ) ^ 3 * ((4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) * V) *
        ((32 * w) ^ (d ^ 4) * δ ^ (d ^ 4 - b))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity))
          (by positivity)
    _ = (K : ℝ) ^ 3 * (4 * ((1024 ^ (d ^ 4) * 9 ^ (d ^ 4) * V * 32 ^ (d ^ 4)) *
        (w ^ (d ^ 4) * δ ^ (d ^ 4 - b)))) := by rw [mul_pow]; ring
    _ ≤ _ := hprod
    _ = _ := by
        rw [show 595 / 3 * (K : ℝ) ^ 2 + (341 / 10 + γ) * (d : ℝ) ^ 4 =
          (K : ℝ) ^ 2 + ((d : ℝ) ^ 4 / 10 + ((31 / 6 * (38 * (K : ℝ) ^ 2) + 34 * (d : ℝ) ^ 4) +
            ((K : ℝ) ^ 2 + γ * (d : ℝ) ^ 4))) by ring]
        simp only [Real.exp_add]
        ring

/-- Large-radius or large-error regime: the split right side is at least one. -/
theorem one_le_sharp_haar_rhs {A B κ : ℝ} (hA : 1 ≤ A) (hB : 10 ≤ B) (hκ0 : 0 ≤ κ)
    (hκ2 : κ ≤ 1 / 2) {d K : ℕ} (hd : 2 ≤ d) (hK : (d : ℝ) ^ 2 / 2 ≤ K) {e : ℝ} (he : 0 < e)
    (hcase : ¬ (e ≤ 1 / 16 ∧
      32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64)) :
    1 ≤ Real.exp (A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4) * e ^ (κ * (d : ℝ) ^ 4) := by
  obtain ⟨-, -, h19⟩ := strong_numeric_exp_bounds
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
  set x := (K : ℝ) / (d : ℝ) ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hNx : (d : ℝ) ^ 4 * x ≤ 2 * (K : ℝ) ^ 2 := by
    have : (d : ℝ) ^ 4 * x = (d : ℝ) ^ 2 * K := by rw [hxdef]; field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_right h2K hK0
    linarith
  have hN0 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
  have hκN : 0 ≤ κ * (d : ℝ) ^ 4 := mul_nonneg hκ0 hN0
  have hAK : (K : ℝ) ^ 2 ≤ A * (K : ℝ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hA
  have hBN : 10 * (d : ℝ) ^ 4 ≤ B * (d : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hB hN0
  have hκN' : κ * (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 4 / 2 := by nlinarith
  have key : κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4 := by
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
      have hx' : κ * ((d : ℝ) ^ 4 * x) ≤ (K : ℝ) ^ 2 := by
        have := mul_le_mul hκ2 hNx (by positivity) (by norm_num)
        linarith
      calc κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ κ * (d : ℝ) ^ 4 * (19 + x) :=
            mul_le_mul_of_nonneg_left hlog hκN
        _ = 19 * (κ * (d : ℝ) ^ 4) + κ * ((d : ℝ) ^ 4 * x) := by ring
        _ ≤ A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4 := by linarith
    · have hinv : 1 / e < 16 := by
        rw [div_lt_iff₀ he]
        linarith
      have hlog : Real.log (1 / e) ≤ 3 := by
        have h1 := Real.log_lt_log (by positivity) hinv
        have h2 : Real.log 16 ≤ 3 := (Real.log_le_iff_le_exp (by norm_num)).mpr (by
          obtain ⟨h18, -, -⟩ := strong_numeric_exp_bounds
          linarith)
        linarith
      calc κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ κ * (d : ℝ) ^ 4 * 3 :=
            mul_le_mul_of_nonneg_left hlog hκN
        _ ≤ A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4 := by linarith [sq_nonneg (K : ℝ)]
  rw [Real.rpow_def_of_pos he, ← Real.exp_add, Real.one_le_exp_iff]
  rw [one_div, Real.log_inv] at key
  linarith

/-! ### The split restricted Haar bound -/

/-- Near-SWAP restricted Haar bound with separate `K²` and `N` coefficients and error
exponent `κN`, for `d ≥ max 2 d₀`. Haar is not renormalized on `S_d`. -/
def StrongRestrictedHaarSplitBound (d₀ : ℕ) (A B κ : ℝ) : Prop :=
  ∀ d K : ℕ, 2 ≤ d → d₀ ≤ d → (d : ℝ) ^ 2 / 2 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4) *
          e ^ (κ * (d : ℝ) ^ 4))) ∧
      unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ mixedReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (A * (K : ℝ) ^ 2 + B * (d : ℝ) ^ 4) *
          e ^ (κ * (d : ℝ) ^ 4)))

/-- The split bound from a lower bound on the controlled rank `N − b ≥ 2κN`. -/
theorem strongRestrictedHaarSplitBound_of_rank {d₀ : ℕ} {κ γ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ2 : κ ≤ 1 / 2) (hγ : κ * (12 / 5) ≤ γ)
    (hrank : ∀ d : ℕ, 2 ≤ d → d₀ ≤ d →
      2 * κ * (d : ℝ) ^ 4 ≤ ((d ^ 4 - strongUncontrolledRank d : ℕ) : ℝ)) :
    StrongRestrictedHaarSplitBound d₀ (595 / 3) (341 / 10 + γ) κ := by
  have hγ0 : 0 ≤ γ := by linarith
  intro d K hd hd₀ hK e he he2
  have hbN : strongUncontrolledRank d ≤ d ^ 4 := by
    have := eight_mul_strongUncontrolledRank_le hd
    omega
  have hpure : unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
      min 1 (ENNReal.ofReal (Real.exp (595 / 3 * (K : ℝ) ^ 2 + (341 / 10 + γ) * (d : ℝ) ^ 4) *
        e ^ (κ * (d : ℝ) ^ 4))) := by
    refine le_min prob_le_one ?_
    by_cases hcase : e ≤ 1 / 16 ∧
        32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64
    · obtain ⟨he16, hu⟩ := hcase
      have hd0 : 0 < d := by omega
      have hsK := sqrt_div_sq_le_sqrt_one_add (K := K) hd0
      have hw1 : 1 ≤ Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ _ := Real.sqrt_le_sqrt (by
              have : (0 : ℝ) ≤ K / (d : ℝ) ^ 2 := by positivity
              linarith)
      have hδ0 : 0 < Real.sqrt (21 / 2 * e) := Real.sqrt_pos.mpr (by positivity)
      have hu0 : 0 < 32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        positivity
      have hlam : 32 * Real.sqrt (21 / 2 * e) * Real.sqrt K / d ≤
          32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hsK (by positivity)
      have hρ : Real.sqrt (21 / 2 * e) ≤
          32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hw1 hδ0.le]
      have hcover := swapNeighborhood_inter_pureReachable_subset_slimWitnessTargets (K := K) hd
        he.le he16
      set F : ℝ := (4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) *
        ((((2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
          82 ^ (slimCoordinateBudget K + 4 * d ^ 4) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * d ^ 4))) *
        (((4 + 32 * Real.sqrt (21 / 2 * e)) * Real.sqrt K / d +
          2 * (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
            strongUncontrolledRank d *
        (32 * Real.sqrt (21 / 2 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
          (d ^ 4 - strongUncontrolledRank d)) with hF
      have hF0 : 0 ≤ F := by positivity
      have hshape : ∀ s : SlimReverseShape d K,
          unitaryHaar (Fin d × Fin d)
            (SlimReverseBlocks.witnessTargets s hd (Real.sqrt (21 / 2 * e))
              (Real.sqrt (21 / 2 * e))) ≤ ENNReal.ofReal F := fun s =>
        SlimReverseBlocks.strong_witness_haar_le_barrier s hd hδ0.le hu0 hu hlam hρ
          (SlimReverseBlocks.measurableSet_witnessTargets s hd _ _) subset_rfl
      have hcard : (Fintype.card (SlimReverseShape d K) : ℝ≥0∞) ≤
          ENNReal.ofReal ((K : ℝ) ^ 3) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast SlimReverseShape.card_le_cube d K)
      calc unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e)
          ≤ unitaryHaar (Fin d × Fin d) (⋃ s : SlimReverseShape d K,
              SlimReverseBlocks.witnessTargets s hd (Real.sqrt (21 / 2 * e))
                (Real.sqrt (21 / 2 * e))) := measure_mono hcover
        _ ≤ ∑ s : SlimReverseShape d K, unitaryHaar (Fin d × Fin d)
              (SlimReverseBlocks.witnessTargets s hd (Real.sqrt (21 / 2 * e))
                (Real.sqrt (21 / 2 * e))) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _s : SlimReverseShape d K, ENNReal.ofReal F :=
            Finset.sum_le_sum fun s _ => hshape s
        _ = (Fintype.card (SlimReverseShape d K) : ℝ≥0∞) * ENNReal.ofReal F := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal ((K : ℝ) ^ 3) * ENNReal.ofReal F := by gcongr
        _ = ENNReal.ofReal ((K : ℝ) ^ 3 * F) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal
            (sharp_small_radius_arith hd hK hbN hκ0 (hrank d hd hd₀) hγ he hu)
    · exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr
        (one_le_sharp_haar_rhs (by norm_num) (by linarith) hκ0 hκ2 hd hK he hcase))
  refine ⟨hpure, ?_⟩
  rw [mixedReachable_eq_pureReachable]
  exact hpure

/-- The split bound for every `d ≥ 2`: `exp((595/3)K² + (687/20)N) ε^(3N/32)`. -/
theorem strongRestrictedHaarSplitBound_two :
    StrongRestrictedHaarSplitBound 2 (595 / 3) (687 / 20) (3 / 32) := by
  have h := strongRestrictedHaarSplitBound_of_rank (d₀ := 2) (κ := 3 / 32) (γ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (fun d hd _ => two_mul_kappa_le_of_sixteen hd)
  rwa [show (341 / 10 + 1 / 4 : ℝ) = 687 / 20 by norm_num] at h

/-- The split bound for every `d ≥ 8`: `exp((595/3)K² + (703/20)N) ε^(7N/16)`. -/
theorem strongRestrictedHaarSplitBound_eight :
    StrongRestrictedHaarSplitBound 8 (595 / 3) (703 / 20) (7 / 16) := by
  have h := strongRestrictedHaarSplitBound_of_rank (d₀ := 8) (κ := 7 / 16) (γ := 21 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun d _ hd => two_mul_kappa_le_of_eight hd)
  rwa [show (341 / 10 + 21 / 20 : ℝ) = 703 / 20 by norm_num] at h

/-- The restricted Haar estimate of the original form with the explicit constant `336`. -/
theorem strongRestrictedHaarBound_explicit : StrongRestrictedHaarBound 336 := by
  intro d K hd hK e he he2
  obtain ⟨hp, hm⟩ := strongRestrictedHaarSplitBound_two d K hd hd hK e he he2
  have hle : Real.exp (595 / 3 * (K : ℝ) ^ 2 + 687 / 20 * (d : ℝ) ^ 4) *
      e ^ (3 / 32 * (d : ℝ) ^ 4) ≤ Real.exp (336 * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16) := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
    have hNK : (d : ℝ) ^ 4 ≤ 4 * (K : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) h2K 2
      nlinarith
    have hN0 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact Real.exp_le_exp.mpr (by linarith [sq_nonneg (K : ℝ)])
    · exact Real.rpow_le_rpow_of_exponent_ge he (by linarith) (by linarith)
  exact ⟨hp.trans (min_le_min_left _ (ENNReal.ofReal_le_ofReal hle)),
    hm.trans (min_le_min_left _ (ENNReal.ofReal_le_ofReal hle))⟩

/-- The same explicit constant for the Haar outer measure of diamond reachability. -/
theorem strongRestrictedDiamondHaarBound_explicit :
    StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} 336 := by
  intro d K hd hK e he he2
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := strongRestrictedHaarBound_explicit d K hd hK e he he2
  exact ⟨(measure_mono (Set.inter_subset_inter_right _
      (pureDiamondReachable_subset_pureReachable K e))).trans hp,
    (measure_mono (Set.inter_subset_inter_right _
      (mixedDiamondReachable_subset_mixedReachable K e))).trans hm⟩

/-! ### From the split bound to resource bounds -/

/-- Patch mass against the split bound: `κ N ln(1/ε) ≤ A K² + (B + 5) N`. -/
theorem PureUniversalScore.log_le_of_split {d₀ : ℕ} {A B κ : ℝ}
    (h : StrongRestrictedHaarSplitBound d₀ A B κ) {d K : ℕ} (hd : 2 ≤ d) (hd₀ : d₀ ≤ d)
    {e : ℝ} (he : 0 < e) (he2 : e ≤ 1 / 2) (hu : PureUniversalScore d K e) :
    κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ A * (K : ℝ) ^ 2 + (B + 5) * (d : ℝ) ^ 4 := by
  have hK := hu.half_dimension_le (by omega : 0 < d) he2
  have hm := (h d K hd hd₀ hK e he he2).1
  rw [hu.reachable_eq_univ, Set.inter_univ] at hm
  have hle := ((strongSwapPatchMassBound_five d hd).trans hm).trans (min_le_right _ _)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), Real.rpow_def_of_pos he, ← Real.exp_add,
    Real.exp_le_exp] at hle
  rw [one_div, Real.log_inv]
  linarith

/-- The precision term with the SWAP floor `K ≥ d²(1 − ε)`: if `c² ≤ 1/24` and
`c² (A + (101/100)(B + 5)) ≤ κ`, then `c d² √ln(1/ε) ≤ K`. -/
theorem resource_of_log_floor {A B κ c : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c)
    (hB : 0 ≤ B + 5) (hc24 : c ^ 2 ≤ 1 / 24) (hcoef : c ^ 2 * (A + 101 / 100 * (B + 5)) ≤ κ)
    {d K : ℕ} {e : ℝ} (he : 0 < e) (he2 : e ≤ 1 / 2) (hfloor : (d : ℝ) ^ 2 * (1 - e) ≤ K)
    (hlog : κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ A * (K : ℝ) ^ 2 + (B + 5) * (d : ℝ) ^ 4) :
    c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
  obtain ⟨-, -, -, -, h403⟩ := explicit_numeric_bounds
  have hL0 : 0 ≤ Real.log (1 / e) :=
    Real.log_nonneg ((one_le_div₀ he).mpr (by linarith))
  set L := Real.log (1 / e) with hLdef
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hX0 : 0 ≤ c * (d : ℝ) ^ 2 * Real.sqrt L := by positivity
  have hX2 : (c * (d : ℝ) ^ 2 * Real.sqrt L) ^ 2 = c ^ 2 * (d : ℝ) ^ 4 * L := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hL0]; ring
  have hN0 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
  apply (pow_le_pow_iff_left₀ hX0 hK0 (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [hX2]
  have hfl2 : ((d : ℝ) ^ 2 * (1 - e)) ^ 2 ≤ (K : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) hfloor 2
  by_cases hcase : c ^ 2 * L ≤ (1 - e) ^ 2
  · calc c ^ 2 * (d : ℝ) ^ 4 * L = (c ^ 2 * L) * (d : ℝ) ^ 4 := by ring
      _ ≤ (1 - e) ^ 2 * (d : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hcase hN0
      _ = ((d : ℝ) ^ 2 * (1 - e)) ^ 2 := by ring
      _ ≤ _ := hfl2
  · -- then `ln(1/ε) > 6`, so `ε < 1/403` and `N ≤ (101/100) K²`
    have h14 : (1 / 4 : ℝ) ≤ (1 - e) ^ 2 := by nlinarith
    have hL6 : 6 < L := by
      by_contra hle
      have : c ^ 2 * L ≤ 1 / 24 * 6 :=
        mul_le_mul hc24 (not_lt.mp hle) hL0 (by norm_num)
      exact hcase (by linarith)
    have he403 : e < 1 / 403 := by
      have h1 : Real.exp 6 < 1 / e := by
        rw [hLdef] at hL6
        exact (Real.lt_log_iff_exp_lt (by positivity)).mp hL6
      have h2 : (403 : ℝ) < 1 / e := lt_of_le_of_lt h403 h1
      rw [lt_div_iff₀ he] at h2
      rw [lt_div_iff₀ (by norm_num)]
      linarith
    have hNK : (d : ℝ) ^ 4 ≤ 101 / 100 * (K : ℝ) ^ 2 := by
      have h99 : (100 / 101 : ℝ) ≤ (1 - e) ^ 2 := by nlinarith
      have : (d : ℝ) ^ 4 * (100 / 101) ≤ (K : ℝ) ^ 2 := by
        calc (d : ℝ) ^ 4 * (100 / 101) ≤ (d : ℝ) ^ 4 * (1 - e) ^ 2 :=
              mul_le_mul_of_nonneg_left h99 hN0
          _ = ((d : ℝ) ^ 2 * (1 - e)) ^ 2 := by ring
          _ ≤ _ := hfl2
      linarith
    have hκX : κ * (c ^ 2 * (d : ℝ) ^ 4 * L) ≤ κ * (K : ℝ) ^ 2 := by
      calc κ * (c ^ 2 * (d : ℝ) ^ 4 * L) = c ^ 2 * (κ * (d : ℝ) ^ 4 * L) := by ring
        _ ≤ c ^ 2 * (A * (K : ℝ) ^ 2 + (B + 5) * (d : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hlog (sq_nonneg c)
        _ ≤ c ^ 2 * (A * (K : ℝ) ^ 2 + (B + 5) * (101 / 100 * (K : ℝ) ^ 2)) := by gcongr
        _ = (c ^ 2 * (A + 101 / 100 * (B + 5))) * (K : ℝ) ^ 2 := by ring
        _ ≤ κ * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    exact le_of_mul_le_mul_left hκX hκ

/-- The asymptotic precision term: if `c² A ≤ κ` and `B + 5 ≤ κ t`, then
`c d² √(ln(1/ε) − t) ≤ K`. -/
theorem resource_of_log_shift {A B κ c t : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c)
    (hcoef : c ^ 2 * A ≤ κ) (ht : B + 5 ≤ κ * t) {d K : ℕ} {e : ℝ}
    (hlog : κ * (d : ℝ) ^ 4 * Real.log (1 / e) ≤ A * (K : ℝ) ^ 2 + (B + 5) * (d : ℝ) ^ 4) :
    c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e) - t) ≤ K := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set L := Real.log (1 / e)
  by_cases hLt : L - t ≤ 0
  · rw [Real.sqrt_eq_zero'.mpr hLt, mul_zero]
    exact hK0
  · have hLt' : 0 ≤ L - t := (not_le.mp hLt).le
    have hX0 : 0 ≤ c * (d : ℝ) ^ 2 * Real.sqrt (L - t) := by positivity
    apply (pow_le_pow_iff_left₀ hX0 hK0 (by norm_num : (2 : ℕ) ≠ 0)).mp
    have hX2 : (c * (d : ℝ) ^ 2 * Real.sqrt (L - t)) ^ 2 = c ^ 2 * ((d : ℝ) ^ 4 * (L - t)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hLt']; ring
    rw [hX2]
    have hN0 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
    have h1 : κ * ((d : ℝ) ^ 4 * (L - t)) ≤ A * (K : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right ht hN0
      nlinarith
    have hκX : κ * (c ^ 2 * ((d : ℝ) ^ 4 * (L - t))) ≤ κ * (K : ℝ) ^ 2 := by
      calc κ * (c ^ 2 * ((d : ℝ) ^ 4 * (L - t))) = c ^ 2 * (κ * ((d : ℝ) ^ 4 * (L - t))) := by
            ring
        _ ≤ c ^ 2 * (A * (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ = (c ^ 2 * A) * (K : ℝ) ^ 2 := by ring
        _ ≤ κ * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    exact le_of_mul_le_mul_left hκX hκ

/-! ### Explicit universal bounds -/

private theorem max3_le {a b c K : ℝ} (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) :
    max a (max b c) ≤ K :=
  max_le ha (max_le hb hc)

/-- **Explicit universal unitary bound, every `d ≥ 2`.** A universal pure score
implementation at error `0 < ε ≤ 1/2` has charged footprint
`K ≥ d² max(1 − ε, √ln(1/ε)/51, √(ln(1/ε) − 420)/46)`. -/
theorem PureUniversalScore.explicit_resource_bound {d K : ℕ} (hd : 2 ≤ d) {e : ℝ} (he : 0 < e)
    (he2 : e ≤ 1 / 2) (hu : PureUniversalScore d K e) :
    (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
      (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K := by
  have hfloor := hu.swap_floor (by omega : 0 < d)
  have hlog := hu.log_le_of_split strongRestrictedHaarSplitBound_two hd hd he he2
  rw [mul_max_of_nonneg _ _ (by positivity), mul_max_of_nonneg _ _ (by positivity)]
  refine max3_le hfloor ?_ ?_
  · have h := resource_of_log_floor (c := 1 / 51) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) he he2 hfloor hlog
    linarith
  · have h := resource_of_log_shift (c := 1 / 46) (t := 420) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog
    linarith

/-- **Explicit universal unitary bound, every `d ≥ 8`.**
`K ≥ d² max(1 − ε, √ln(1/ε)/24, √(ln(1/ε) − 92)/22)`. -/
theorem PureUniversalScore.explicit_resource_bound_of_eight {d K : ℕ} (hd : 8 ≤ d) {e : ℝ}
    (he : 0 < e) (he2 : e ≤ 1 / 2) (hu : PureUniversalScore d K e) :
    (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
      (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K := by
  have hfloor := hu.swap_floor (by omega : 0 < d)
  have hlog := hu.log_le_of_split strongRestrictedHaarSplitBound_eight (by omega) hd he he2
  rw [mul_max_of_nonneg _ _ (by positivity), mul_max_of_nonneg _ _ (by positivity)]
  refine max3_le hfloor ?_ ?_
  · have h := resource_of_log_floor (c := 1 / 24) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) he he2 hfloor hlog
    linarith
  · have h := resource_of_log_shift (c := 1 / 22) (t := 92) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog
    linarith

/-- The explicit universal bounds for pure and common-map finite-mixed score universality. -/
theorem strongUniversal_explicit (d K : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 < e) (he2 : e ≤ 1 / 2) :
    (PureUniversalScore d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
        (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) ∧
    (MixedUniversalScore d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
        (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) :=
  ⟨fun hu => hu.explicit_resource_bound hd he he2,
    fun hm => ((mixedUniversalScore_iff_pure d K e).mp hm).explicit_resource_bound hd he he2⟩

/-- The `d ≥ 8` explicit universal bounds, pure and common-map finite mixed. -/
theorem strongUniversal_explicit_of_eight (d K : ℕ) (hd : 8 ≤ d) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PureUniversalScore d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
        (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) ∧
    (MixedUniversalScore d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
        (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) :=
  ⟨fun hu => hu.explicit_resource_bound_of_eight hd he he2,
    fun hm => ((mixedUniversalScore_iff_pure d K e).mp hm).explicit_resource_bound_of_eight
      hd he he2⟩

/-- The explicit universal bounds for pure and common-map finite-mixed normalized diamond
universality. -/
theorem strongUniversalDiamond_explicit (d K : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
        (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) ∧
    (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
        (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := strongUniversal_explicit d K hd e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

/-- The `d ≥ 8` explicit bounds for normalized diamond universality. -/
theorem strongUniversalDiamond_explicit_of_eight (d K : ℕ) (hd : 8 ≤ d) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
        (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) ∧
    (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
        (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := strongUniversal_explicit_of_eight d K hd e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

/-- `K ≥ d² √ln(1/ε) / 51` in the named form. -/
theorem strongUniversalResourceBound_explicit : StrongUniversalResourceBound (1 / 51) := by
  intro d K hd e he he2
  have key (h : PureUniversalScore d K e) :
      1 / 51 * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have hb := h.explicit_resource_bound hd he he2
    have hm : Real.sqrt (Real.log (1 / e)) / 51 ≤ max (1 - e) (max
        (Real.sqrt (Real.log (1 / e)) / 51) (Real.sqrt (Real.log (1 / e) - 420) / 46)) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)
    linarith
  exact ⟨key, fun hm => key ((mixedUniversalScore_iff_pure d K e).mp hm)⟩

/-- The named diamond form with `c = 1/51`. -/
theorem strongUniversalDiamondResourceBound_explicit :
    StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (1 / 51) := by
  intro d K hd e he he2
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := strongUniversalResourceBound_explicit d K hd e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

theorem logb_two_inv_two_pow (k : ℕ) : max 0 (-Real.logb 2 (1 / 2 ^ k)) = k := by
  rw [one_div, Real.logb_inv, neg_neg, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one]
  exact max_eq_right (Nat.cast_nonneg k)

/-- `log₂ K ≥ 2n + ½ log₂ ln(1/ε) − 6` at `d = 2ⁿ`. -/
theorem strongUniversalQubitBound_explicit : StrongUniversalQubitBound 6 := by
  intro n K hn _ e he he2
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  obtain ⟨hp, hm⟩ := strongUniversalResourceBound_explicit (2 ^ n) K hd e he he2
  have hconv (h : 1 / 51 * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) :
      2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - 6 ≤ Real.logb 2 K := by
    have h' : 1 / 2 ^ 6 * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K :=
      le_trans (by gcongr; norm_num) h
    have hq := strong_qubit_of_resource (c := 1 / 2 ^ 6) (by norm_num) he he2 n h'
    rwa [logb_two_inv_two_pow 6] at hq
  exact ⟨fun hu => hconv (hp hu), fun hu => hconv (hm hu)⟩

/-- The qubit form with offset `6` for normalized diamond universality. -/
theorem strongUniversalDiamondQubitBound_explicit :
    StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} 6 := by
  intro n K hn hK e he he2
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨hp, hm⟩ := strongUniversalQubitBound_explicit n K hn hK e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

/-- `log₂ K ≥ 2n + ½ log₂ ln(1/ε) − 5` at `d = 2ⁿ` once `n ≥ 3`, pure and common-map mixed
score and normalized diamond universality. -/
theorem strongUniversalQubitBound_explicit_of_three (n K : ℕ) (hn : 3 ≤ n) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PureUniversalScore (2 ^ n) K e ∨ MixedUniversalScore (2 ^ n) K e ∨
      PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e ∨
      MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e) →
      2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - 5 ≤ Real.logb 2 K := by
  intro h
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  have hd : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hpure : PureUniversalScore (2 ^ n) K e := by
    rcases h with h | h | h | h
    · exact h
    · exact (mixedUniversalScore_iff_pure _ K e).mp h
    · exact h.score
    · exact (mixedUniversalScore_iff_pure _ K e).mp h.score
  have hb := hpure.explicit_resource_bound_of_eight hd he he2
  have hm : Real.sqrt (Real.log (1 / e)) / 24 ≤ max (1 - e) (max
      (Real.sqrt (Real.log (1 / e)) / 24) (Real.sqrt (Real.log (1 / e) - 92) / 22)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h' : 1 / 2 ^ 5 * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)) ^ 2)
    have hs := Real.sqrt_nonneg (Real.log (1 / e))
    nlinarith
  have hq := strong_qubit_of_resource (c := 1 / 2 ^ 5) (by norm_num) he he2 n h'
  rwa [logb_two_inv_two_pow 5] at hq

end NLQCLean
