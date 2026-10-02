import NLQCLean.Arithmetic.GelfondDoubling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerics of Gelfond's method

Parameters `h = B³`, `J = B⁴`, `L = 4B⁸`, `T₀ = B⁸` for `B ≥ 128`. Every quantity of the doubling
conditions is bounded by an explicit power of `2` whose exponent is a polynomial in `B`
(and the derivative order), and the two conditions are checked along the whole chain.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

/-! ### Powers of two -/

theorem natCast_pow_le_two_pow (B k : ℕ) : ((B : ℝ)) ^ k ≤ 2 ^ (k * B) := by
  have : (B : ℝ) ≤ 2 ^ B := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc (B : ℝ) ^ k ≤ (2 ^ B) ^ k := pow_le_pow_left₀ (by positivity) this k
    _ = 2 ^ (k * B) := by rw [← pow_mul, mul_comm]

theorem le_two_pow_mul {x y : ℝ} {a b : ℕ} (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ 2 ^ a)
    (hy : y ≤ 2 ^ b) : x * y ≤ 2 ^ (a + b) := by
  rw [pow_add]; exact mul_le_mul hx hy hy0 (by positivity)

theorem pow_le_two_pow {x : ℝ} {a : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ 2 ^ a) (k : ℕ) :
    x ^ k ≤ 2 ^ (a * k) := by
  rw [pow_mul]; exact pow_le_pow_left₀ hx0 hx k

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b :=
  pow_le_pow_right₀ (by norm_num) h

theorem Bfact {B : ℕ} (hB : 128 ≤ B) (k : ℕ) : 128 * B ^ k ≤ B ^ (k + 1) := by
  rw [pow_succ]; nlinarith [Nat.zero_le (B ^ k)]

theorem exp_natCast_le_two_pow (n : ℕ) : Real.exp n ≤ 2 ^ (2 * n) := by
  have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
  calc Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 4 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le he n
    _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num

/-! ### The parameters -/

theorem paramH_le (B : ℕ) : ((B : ℝ) ^ 3) ≤ 2 ^ (3 * B) := natCast_pow_le_two_pow B 3

section Params

variable {B : ℕ} (hB : 128 ≤ B)
include hB

theorem paramU_le : (((B ^ 4 + 1) * (4 * B ^ 8) : ℕ) : ℝ) ≤ 2 ^ (12 * B + 3) := by
  have h1 : (B ^ 4 + 1) * (4 * B ^ 8) ≤ 8 * B ^ 12 := by
    have : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith [Nat.zero_le (B ^ 8), show B ^ 12 = B ^ 4 * B ^ 8 by ring]
  calc (((B ^ 4 + 1) * (4 * B ^ 8) : ℕ) : ℝ) ≤ ((8 * B ^ 12 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 2 ^ 3 * (B : ℝ) ^ 12 := by push_cast; norm_num
    _ ≤ 2 ^ 3 * 2 ^ (12 * B) := by gcongr; exact natCast_pow_le_two_pow B 12
    _ = 2 ^ (12 * B + 3) := by rw [← pow_add]; ring_nf

theorem paramJL_le : ((B : ℝ) ^ 4 + (4 * B ^ 8 : ℕ)) ≤ 2 ^ (8 * B + 3) := by
  have h1 : B ^ 4 + 4 * B ^ 8 ≤ 8 * B ^ 8 := by
    have : B ^ 4 ≤ B ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  calc ((B : ℝ) ^ 4 + (4 * B ^ 8 : ℕ)) = ((B ^ 4 + 4 * B ^ 8 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((8 * B ^ 8 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 2 ^ 3 * (B : ℝ) ^ 8 := by push_cast; norm_num
    _ ≤ 2 ^ 3 * 2 ^ (8 * B) := by gcongr; exact natCast_pow_le_two_pow B 8
    _ = 2 ^ (8 * B + 3) := by rw [← pow_add]; ring_nf

theorem paramJL_le' : (((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ)) ≤ 2 ^ (8 * B + 3) := by
  have := paramJL_le hB
  push_cast at this ⊢
  exact this

theorem one_le_paramJL : (1 : ℝ) ≤ ((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ) := by
  have : (1 : ℝ) ≤ ((B ^ 4 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h0 : (0 : ℝ) ≤ ((4 * B ^ 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- The Siegel coefficient bound. -/
theorem siegelBound_le {G : GaussianInt[X]} (hg : G.natDegree ≤ B) :
    siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8) ≤ 2 ^ (22 * B ^ 9) := by
  have hU := paramU_le hB
  have hh : ((B ^ 3 : ℕ) : ℝ) ^ (4 * B ^ 8) ≤ 2 ^ (3 * B * (4 * B ^ 8)) := by
    refine pow_le_two_pow (by positivity) ?_ _
    push_cast; exact paramH_le B
  have hJL : (((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ)) ^ (B ^ 8) ≤ 2 ^ ((8 * B + 3) * B ^ 8) :=
    pow_le_two_pow (by positivity) (paramJL_le' hB) _
  have ha : ((2 : ℝ) ^ B) ^ (B ^ 4 * B ^ 3) = 2 ^ (B * B ^ 7) := by
    rw [← pow_mul]; ring_nf
  have hag : (1 + ((2 : ℝ) ^ B) ^ G.natDegree) ^ (B ^ 4 * B ^ 3) ≤ 2 ^ ((B * B + 1) * B ^ 7) := by
    have h1 : 1 + ((2 : ℝ) ^ B) ^ G.natDegree ≤ 2 ^ (B * B + 1) := by
      rw [← pow_mul, pow_succ]
      have : (2 : ℝ) ^ (B * G.natDegree) ≤ 2 ^ (B * B) := two_pow_mono (Nat.mul_le_mul_left _ hg)
      have h1 : (1 : ℝ) ≤ 2 ^ (B * B) := one_le_pow₀ (by norm_num)
      linarith
    refine (pow_le_two_pow (by positivity) h1 _).trans (le_of_eq ?_)
    ring_nf
  unfold siegelBound
  calc ((((B ^ 4 + 1) * (4 * B ^ 8) : ℕ)) : ℝ) * (((B ^ 3 : ℕ) : ℝ) ^ (4 * B ^ 8) *
        (((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ)) ^ (B ^ 8) * (2 ^ B) ^ (B ^ 4 * B ^ 3) *
        (1 + (2 ^ B) ^ G.natDegree) ^ (B ^ 4 * B ^ 3))
      ≤ 2 ^ (12 * B + 3) * (2 ^ (3 * B * (4 * B ^ 8)) * 2 ^ ((8 * B + 3) * B ^ 8) *
          2 ^ (B * B ^ 7) * 2 ^ ((B * B + 1) * B ^ 7)) := by
        rw [ha]
        gcongr
    _ = 2 ^ (12 * B + 3 + 3 * B * (4 * B ^ 8) + (8 * B + 3) * B ^ 8 + B * B ^ 7 +
          (B * B + 1) * B ^ 7) := by
        simp only [pow_add]; ring
    _ ≤ 2 ^ (22 * B ^ 9) := by
        apply two_pow_mono
        have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
        have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
        have f1 : B ≤ B ^ 7 := Nat.le_self_pow (by norm_num) B
        ring_nf
        omega

theorem paramUreal_le : (((B ^ 4 : ℕ) : ℝ) + 1) * ((4 * B ^ 8 : ℕ) : ℝ) ≤ 2 ^ (12 * B + 3) := by
  have := paramU_le hB
  push_cast at this ⊢
  exact this

theorem heightQ_le {Cc : ℝ} (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (22 * B ^ 9)) (t : ℕ) :
    heightQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤
      2 ^ (12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) + (8 * B + 3) * t) := by
  unfold heightQ
  have hh : ((B ^ 3 : ℕ) : ℝ) ^ (4 * B ^ 8) ≤ 2 ^ (3 * B * (4 * B ^ 8)) := by
    refine pow_le_two_pow (by positivity) ?_ _
    push_cast; exact paramH_le B
  have hJL : (((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ)) ^ t ≤ 2 ^ ((8 * B + 3) * t) :=
    pow_le_two_pow (by positivity) (paramJL_le' hB) _
  calc (((B ^ 4 : ℕ) : ℝ) + 1) * ((4 * B ^ 8 : ℕ) : ℝ) * (Cc * (((B ^ 3 : ℕ) : ℝ) ^ (4 * B ^ 8) *
        (((B ^ 4 : ℕ) : ℝ) + ((4 * B ^ 8 : ℕ) : ℝ)) ^ t))
      ≤ 2 ^ (12 * B + 3) * (2 ^ (22 * B ^ 9) * (2 ^ (3 * B * (4 * B ^ 8)) *
          2 ^ ((8 * B + 3) * t))) := by
        gcongr
        exact paramUreal_le hB
    _ = _ := by simp only [pow_add]; ring

omit hB in
theorem mahlerMeasure_le {G : GaussianInt[X]} (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) :
    (G.map toComplex).mahlerMeasure ≤ 2 ^ (2 * B) := by
  refine (mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
  have hdeg : (G.map toComplex).natDegree ≤ B := by
    rw [natDegree_map_eq_of_injective toComplex_injective]; exact hg
  have hsup : (G.map toComplex).supNorm ≤ 2 ^ B :=
    supNorm_le_of_coeff_le fun k => by rw [coeff_map]; exact hcoeff k
  have hsq : √(((G.map toComplex).natDegree : ℝ) + 1) ≤ 2 ^ B := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : ((G.map toComplex).natDegree : ℝ) + 1 ≤ 2 ^ B := by
      have : (G.map toComplex).natDegree + 1 ≤ 2 ^ B := (Nat.succ_le_succ hdeg).trans
        (Nat.lt_two_pow_self)
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    nlinarith
  calc √(((G.map toComplex).natDegree : ℝ) + 1) * (G.map toComplex).supNorm
      ≤ 2 ^ B * 2 ^ B := mul_le_mul hsq hsup (supNorm_nonneg _) (by positivity)
    _ = 2 ^ (2 * B) := by rw [← pow_add]; ring_nf

omit hB in
theorem heightQ_nonneg' {J L h : ℕ} {Cc : ℝ} (hCc0 : 0 ≤ Cc) (t : ℕ) :
    0 ≤ heightQ J L h Cc t := by
  unfold heightQ
  exact mul_nonneg (by positivity) (mul_nonneg hCc0 (by positivity))

theorem deltaInv_le {G : GaussianInt[X]} (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : Cc ≤ 2 ^ (22 * B ^ 9)) (t : ℕ) :
    deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤
      2 ^ (B * (35 * B ^ 9 + (8 * B + 3) * t) + 2 * B * B ^ 7) := by
  unfold deltaInv
  set e := 35 * B ^ 9 + (8 * B + 3) * t
  have hq : (((B ^ 4 * B ^ 3 : ℕ) : ℝ) + 1) ≤ 2 ^ (7 * B + 1) := by
    have h1 : B ^ 4 * B ^ 3 + 1 ≤ 2 ^ (7 * B + 1) := by
      have : B ^ 4 * B ^ 3 ≤ 2 ^ (7 * B) := by
        rw [← pow_add]
        calc B ^ (4 + 3) ≤ (2 ^ B) ^ (4 + 3) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ (7 * B) := by rw [← pow_mul]; ring_nf
      have h2 := Nat.one_le_two_pow (n := 7 * B)
      calc B ^ 4 * B ^ 3 + 1 ≤ 2 * 2 ^ (7 * B) := by omega
        _ = 2 ^ (7 * B + 1) := by ring
    exact_mod_cast h1
  have hbase : (((B ^ 4 * B ^ 3 : ℕ) : ℝ) + 1) * heightQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ e := by
    refine (le_two_pow_mul (by positivity) (heightQ_nonneg' hCc0 t) hq
      (heightQ_le hB hCc0 hCc t)).trans (two_pow_mono ?_)
    have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
    have f1 : B ≤ B ^ 8 := Nat.le_self_pow (by norm_num) B
    simp only [e]
    ring_nf
    omega
  have hpow : ((((B ^ 4 * B ^ 3 : ℕ) : ℝ) + 1) * heightQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t) ^
      (G.natDegree - 1) ≤ 2 ^ (B * e) := by
    calc _ ≤ (2 ^ e : ℝ) ^ (G.natDegree - 1) :=
          pow_le_pow_left₀ (mul_nonneg (by positivity) (heightQ_nonneg' hCc0 t)) hbase _
      _ ≤ (2 ^ e : ℝ) ^ B := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
      _ = 2 ^ (B * e) := by rw [← pow_mul, mul_comm]
  have hM : (G.map toComplex).mahlerMeasure ^ (B ^ 4 * B ^ 3) ≤ 2 ^ (2 * B * B ^ 7) := by
    refine (pow_le_two_pow (mahlerMeasure_nonneg _) (mahlerMeasure_le hg hcoeff) _).trans
      (le_of_eq (by congr 1; ring))
  calc _ ≤ 2 ^ (B * e) * 2 ^ (2 * B * B ^ 7) :=
        mul_le_mul hpow hM (pow_nonneg (mahlerMeasure_nonneg _) _) (by positivity)
    _ = _ := by rw [← pow_add]

theorem growthF_le {Cc : ℝ} (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (22 * B ^ 9)) :
    growthF (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc ≤ 2 ^ (35 * B ^ 9) := by
  unfold growthF
  have h8 : (8 * ((B ^ 3 : ℕ) : ℝ)) ^ (4 * B ^ 8) ≤ 2 ^ ((3 * B + 3) * (4 * B ^ 8)) := by
    refine pow_le_two_pow (by positivity) ?_ _
    push_cast
    rw [pow_add]
    have := paramH_le B
    nlinarith
  have hexp : Real.exp (((B ^ 4 : ℕ) : ℝ) * (8 * ((B ^ 3 : ℕ) : ℝ))) ≤ 2 ^ (2 * (8 * B ^ 7)) := by
    have : ((B ^ 4 : ℕ) : ℝ) * (8 * ((B ^ 3 : ℕ) : ℝ)) = ((8 * B ^ 7 : ℕ) : ℝ) := by
      push_cast; ring
    rw [this]; exact exp_natCast_le_two_pow _
  calc (((B ^ 4 : ℕ) : ℝ) + 1) * ((4 * B ^ 8 : ℕ) : ℝ) * Cc * (8 * ((B ^ 3 : ℕ) : ℝ)) ^ (4 * B ^ 8) *
        Real.exp (((B ^ 4 : ℕ) : ℝ) * (8 * ((B ^ 3 : ℕ) : ℝ)))
      ≤ 2 ^ (12 * B + 3) * 2 ^ (22 * B ^ 9) * 2 ^ ((3 * B + 3) * (4 * B ^ 8)) *
          2 ^ (2 * (8 * B ^ 7)) := by
        gcongr
        exact paramUreal_le hB
    _ = 2 ^ (12 * B + 3 + 22 * B ^ 9 + (3 * B + 3) * (4 * B ^ 8) + 2 * (8 * B ^ 7)) := by
        simp only [pow_add]
    _ ≤ 2 ^ (35 * B ^ 9) := by
        apply two_pow_mono
        have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
        have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
        have f1 : B ≤ B ^ 7 := Nat.le_self_pow (by norm_num) B
        ring_nf
        omega

theorem paramU_nat_le : (B ^ 4 + 1) * (4 * B ^ 8) ≤ 8 * B ^ 12 := by
  have : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith [Nat.zero_le (B ^ 8), show B ^ 12 = B ^ 4 * B ^ 8 by ring]

theorem factorial_le_of_lt_twoU {t : ℕ} (ht : t ≤ 2 * ((B ^ 4 + 1) * (4 * B ^ 8))) :
    (t.factorial : ℝ) ≤ 2 ^ ((12 * B + 4) * t) := by
  have h1 : t ≤ 2 ^ (12 * B + 4) := by
    have hU := paramU_nat_le hB
    have hB12 : B ^ 12 ≤ 2 ^ (12 * B) := by
      calc B ^ 12 ≤ (2 ^ B) ^ 12 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ (12 * B) := by rw [← pow_mul]; ring_nf
    calc t ≤ 16 * B ^ 12 := by omega
      _ ≤ 16 * 2 ^ (12 * B) := by omega
      _ = 2 ^ (12 * B + 4) := by ring
  calc (t.factorial : ℝ) ≤ ((t ^ t : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow t
    _ ≤ ((2 ^ (12 * B + 4)) ^ t : ℕ) := by exact_mod_cast Nat.pow_le_pow_left h1 t
    _ = 2 ^ ((12 * B + 4) * t) := by push_cast; rw [← pow_mul]

omit hB in
theorem two_pow_le_seven_pow (n : ℕ) : (2 : ℝ) ^ (2 * n) ≤ 7 ^ n := by
  rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- **Condition H1** along the chain. -/
theorem condition_H1 {G : GaussianInt[X]} (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) :
    ∀ T, B ^ 8 ≤ T → T < (B ^ 4 + 1) * (4 * B ^ 8) → ∀ t < 2 * T,
      t.factorial * growthF (B ^ 4) (4 * B ^ 8) (B ^ 3)
          (siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)) / 7 ^ (B ^ 3 * T) *
        deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3)
          (siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)) t ≤ 1 / 4 := by
  intro T hT hTU t ht
  set Cc := siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)
  have hCc := siegelBound_le hB hg
  have hCc0 : 0 ≤ Cc := by
    simp only [Cc, siegelBound]
    have : (0 : ℝ) ≤ 1 + (2 ^ B) ^ G.natDegree := by positivity
    positivity
  have hfac := factorial_le_of_lt_twoU hB (t := t) (by omega)
  have hgr := growthF_le hB hCc0 hCc
  have hdi := deltaInv_le hB hg hcoeff hCc0 hCc t
  have hgr0 : 0 ≤ growthF (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc := by
    unfold growthF; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCc0) (by positivity))
      (Real.exp_pos _).le
  have hdi0 : 0 ≤ deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t := by
    unfold deltaInv
    exact mul_nonneg (pow_nonneg (mul_nonneg (by positivity) (heightQ_nonneg' hCc0 t)) _)
      (pow_nonneg (mahlerMeasure_nonneg _) _)
  set E := (12 * B + 4) * t + 35 * B ^ 9 + (B * (35 * B ^ 9 + (8 * B + 3) * t) + 2 * B * B ^ 7)
  have hnum : (t.factorial : ℝ) * growthF (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc *
      deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ E := by
    calc (t.factorial : ℝ) * growthF (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc *
          deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t
        ≤ 2 ^ ((12 * B + 4) * t) * 2 ^ (35 * B ^ 9) *
            2 ^ (B * (35 * B ^ 9 + (8 * B + 3) * t) + 2 * B * B ^ 7) := by gcongr
      _ = 2 ^ E := by simp only [E, pow_add]
  have hexp : E + 2 ≤ 2 * (B ^ 3 * T) := by
    have k1 : (12 * B + 4) * t + B * ((8 * B + 3) * t) ≤ (8 * B ^ 2 + 15 * B + 4) * (2 * T) := by
      have : (12 * B + 4) * t + B * ((8 * B + 3) * t) = (8 * B ^ 2 + 15 * B + 4) * t := by ring
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    have k2 : (8 * B ^ 2 + 15 * B + 4) * 2 ≤ B ^ 3 := by nlinarith
    have k2' : (8 * B ^ 2 + 15 * B + 4) * (2 * T) ≤ B ^ 3 * T := by
      calc (8 * B ^ 2 + 15 * B + 4) * (2 * T) = ((8 * B ^ 2 + 15 * B + 4) * 2) * T := by ring
        _ ≤ B ^ 3 * T := Nat.mul_le_mul_right _ k2
    have k3 : 35 * B ^ 9 + B * (35 * B ^ 9) + 2 * B * B ^ 7 + 2 ≤ B ^ 3 * T := by
      have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
      have f9 : 128 * B ^ 9 ≤ B ^ 10 := Bfact hB 9
      have f10 : 128 * B ^ 10 ≤ B ^ 11 := Bfact hB 10
      have hBT : B ^ 11 ≤ B ^ 3 * T := by
        calc B ^ 11 = B ^ 3 * B ^ 8 := by ring
          _ ≤ B ^ 3 * T := Nat.mul_le_mul_left _ hT
      have h8 : 1 ≤ B ^ 8 := Nat.one_le_pow _ _ (by omega)
      have e1 : B * (35 * B ^ 9) = 35 * B ^ 10 := by ring
      have e2 : 2 * B * B ^ 7 = 2 * B ^ 8 := by ring
      rw [e1, e2]
      omega
    have : E + 2 = ((12 * B + 4) * t + B * ((8 * B + 3) * t)) +
        (35 * B ^ 9 + B * (35 * B ^ 9) + 2 * B * B ^ 7 + 2) := by simp only [E]; ring
    rw [this]
    omega
  have h7 : (2 : ℝ) ^ (E + 2) ≤ 7 ^ (B ^ 3 * T) :=
    (two_pow_mono hexp).trans (two_pow_le_seven_pow _)
  have h7pos : (0 : ℝ) < 7 ^ (B ^ 3 * T) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h7pos]
  calc (t.factorial : ℝ) * growthF (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc *
        deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ E := hnum
    _ = 1 / 4 * 2 ^ (E + 2) := by rw [pow_add]; ring
    _ ≤ 1 / 4 * 7 ^ (B ^ 3 * T) := by gcongr

omit hB in
theorem paramQ_le : (((B ^ 4 * B ^ 3 : ℕ) : ℝ) + 1) ≤ 2 ^ (7 * B + 1) := by
  have h1 : B ^ 4 * B ^ 3 + 1 ≤ 2 ^ (7 * B + 1) := by
    have : B ^ 4 * B ^ 3 ≤ 2 ^ (7 * B) := by
      rw [← pow_add]
      calc B ^ (4 + 3) ≤ (2 ^ B) ^ (4 + 3) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ (7 * B) := by rw [← pow_mul]; ring_nf
    have h2 := Nat.one_le_two_pow (n := 7 * B)
    calc B ^ 4 * B ^ 3 + 1 ≤ 2 * 2 ^ (7 * B) := by omega
      _ = 2 ^ (7 * B + 1) := by ring
  exact_mod_cast h1

omit hB in
theorem paramN_le {T : ℕ} (hT : T ≤ 8 * B ^ 12) : B ^ 3 * T ≤ 2 ^ (15 * B + 3) := by
  have hB15 : B ^ 15 ≤ 2 ^ (15 * B) := by
    calc B ^ 15 ≤ (2 ^ B) ^ 15 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
      _ = 2 ^ (15 * B) := by rw [← pow_mul]; ring_nf
  calc B ^ 3 * T ≤ B ^ 3 * (8 * B ^ 12) := Nat.mul_le_mul_left _ hT
    _ = 8 * B ^ 15 := by ring
    _ ≤ 8 * 2 ^ (15 * B) := by omega
    _ = 2 ^ (15 * B + 3) := by ring

theorem interpConst_le {T : ℕ} (hT : T ≤ 8 * B ^ 12) :
    (interpConst (B ^ 3) T : ℝ) ≤ 2 ^ ((15 * B + 3) * (B ^ 3 * T + 1) +
      (B ^ 3 * T) * ((15 * B + 3) * T + 3 * B * (B ^ 3 * T))) := by
  have hn := paramN_le hT
  unfold interpConst
  set n := B ^ 3 * T
  have hh : B ^ 3 ≤ 2 ^ (3 * B) := by
    calc B ^ 3 ≤ (2 ^ B) ^ 3 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
      _ = 2 ^ (3 * B) := by rw [← pow_mul]; ring_nf
  have h1 : n ^ (n + 1) * (n ^ T * (B ^ 3) ^ n) ^ n ≤
      (2 ^ (15 * B + 3)) ^ (n + 1) * ((2 ^ (15 * B + 3)) ^ T * (2 ^ (3 * B)) ^ n) ^ n := by
    gcongr
  have h2 : (2 ^ (15 * B + 3)) ^ (n + 1) * ((2 ^ (15 * B + 3)) ^ T * (2 ^ (3 * B)) ^ n) ^ n =
      2 ^ ((15 * B + 3) * (n + 1) + n * ((15 * B + 3) * T + 3 * B * n)) := by
    simp only [← pow_mul, ← pow_add]
    ring_nf
  have := h1.trans_eq h2
  exact_mod_cast this

theorem quotB_le {Cc : ℝ} (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (22 * B ^ 9)) (T : ℕ) :
    quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T ≤ 2 ^ (B ^ 4 * B ^ 3 + (7 * B + 1 +
      (12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) + (8 * B + 3) * T))) := by
  unfold quotB
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left (le_two_pow_mul (by positivity) (heightQ_nonneg' hCc0 T)
    paramQ_le (heightQ_le hB hCc0 hCc T)) (by positivity)

theorem lipQ_le {Cc : ℝ} (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (22 * B ^ 9)) (t : ℕ) :
    lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ (7 * B + 1 + (7 * B +
      ((12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) + (8 * B + 3) * t) + B ^ 4 * B ^ 3))) := by
  unfold lipQ
  have hq : (((B ^ 4 * B ^ 3 : ℕ) : ℝ)) ≤ 2 ^ (7 * B) := by
    have : B ^ 4 * B ^ 3 ≤ 2 ^ (7 * B) := by
      rw [← pow_add]
      calc B ^ (4 + 3) ≤ (2 ^ B) ^ (4 + 3) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ (7 * B) := by rw [← pow_mul]; ring_nf
    exact_mod_cast this
  refine le_two_pow_mul (by positivity) (by
      exact mul_nonneg (by positivity) (mul_nonneg (heightQ_nonneg' hCc0 t) (by positivity)))
    paramQ_le ?_
  refine le_two_pow_mul (by positivity)
    (mul_nonneg (heightQ_nonneg' hCc0 t) (by positivity)) hq ?_
  exact le_two_pow_mul (heightQ_nonneg' hCc0 t) (by positivity) (heightQ_le hB hCc0 hCc t) le_rfl

theorem eightH_pow_le (m : ℕ) : (8 * ((B ^ 3 : ℕ) : ℝ)) ^ m ≤ 2 ^ ((3 * B + 3) * m) := by
  refine pow_le_two_pow (by positivity) ?_ _
  push_cast
  rw [pow_add]
  have := paramH_le B
  nlinarith

/-- The total exponent of condition H2. -/
theorem exponent_H2 {T t : ℕ} (hT : T ≤ 8 * B ^ 12) (ht : t ≤ 16 * B ^ 12) :
    B * (35 * B ^ 9 + (8 * B + 3) * t) + 2 * B * B ^ 7 +
      ((15 * B + 3) + ((15 * B + 3) * (B ^ 3 * T + 1) +
        (B ^ 3 * T) * ((15 * B + 3) * T + 3 * B * (B ^ 3 * T))) +
        (27 * B + 7) * t + (6 * B + 3) * (B ^ 3 * T)) +
      (B ^ 4 * B ^ 3 + (7 * B + 1 + (12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) +
        (8 * B + 3) * T))) +
      (7 * B + 1 + (7 * B + ((12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) + (8 * B + 3) * t) +
        B ^ 4 * B ^ 3))) + 3 ≤ 200 * B ^ 31 := by
  set n := B ^ 3 * T with hn
  have hn' : n ≤ 8 * B ^ 15 := by
    calc n ≤ B ^ 3 * (8 * B ^ 12) := Nat.mul_le_mul_left _ hT
      _ = 8 * B ^ 15 := by ring
  have c1 : 15 * B + 3 ≤ 16 * B := by omega
  have c2 : 8 * B + 3 ≤ 9 * B := by omega
  have c3 : 27 * B + 7 ≤ 28 * B := by omega
  have c4 : 6 * B + 3 ≤ 7 * B := by omega
  have pa : B * ((8 * B + 3) * t) ≤ 144 * B ^ 14 := by
    calc B * ((8 * B + 3) * t) ≤ B * ((9 * B) * (16 * B ^ 12)) := by gcongr
      _ = 144 * B ^ 14 := by ring
  have pb : (27 * B + 7) * t ≤ 448 * B ^ 13 := by
    calc (27 * B + 7) * t ≤ (28 * B) * (16 * B ^ 12) := by gcongr
      _ = 448 * B ^ 13 := by ring
  have pc : (6 * B + 3) * n ≤ 56 * B ^ 16 := by
    calc (6 * B + 3) * n ≤ (7 * B) * (8 * B ^ 15) := by gcongr
      _ = 56 * B ^ 16 := by ring
  have pd : (15 * B + 3) * (n + 1) ≤ 128 * B ^ 16 + 16 * B := by
    calc (15 * B + 3) * (n + 1) ≤ (16 * B) * (8 * B ^ 15 + 1) := by gcongr
      _ = 128 * B ^ 16 + 16 * B := by ring
  have pe : n * ((15 * B + 3) * T) ≤ 1024 * B ^ 28 := by
    calc n * ((15 * B + 3) * T) ≤ (8 * B ^ 15) * ((16 * B) * (8 * B ^ 12)) := by gcongr
      _ = 1024 * B ^ 28 := by ring
  have pf : n * (3 * B * n) ≤ 192 * B ^ 31 := by
    calc n * (3 * B * n) ≤ (8 * B ^ 15) * (3 * B * (8 * B ^ 15)) := by gcongr
      _ = 192 * B ^ 31 := by ring
  have pg : (8 * B + 3) * T ≤ 72 * B ^ 13 := by
    calc (8 * B + 3) * T ≤ (9 * B) * (8 * B ^ 12) := by gcongr
      _ = 72 * B ^ 13 := by ring
  have ph : (8 * B + 3) * t ≤ 144 * B ^ 13 := by
    calc (8 * B + 3) * t ≤ (9 * B) * (16 * B ^ 12) := by gcongr
      _ = 144 * B ^ 13 := by ring
  have e1 : B * (35 * B ^ 9 + (8 * B + 3) * t) = 35 * B ^ 10 + B * ((8 * B + 3) * t) := by ring
  have e2 : 2 * B * B ^ 7 = 2 * B ^ 8 := by ring
  have e3 : B ^ 4 * B ^ 3 = B ^ 7 := by ring
  have e4 : 3 * B * (4 * B ^ 8) = 12 * B ^ 9 := by ring
  have e5 : n * ((15 * B + 3) * T + 3 * B * n) = n * ((15 * B + 3) * T) + n * (3 * B * n) := by ring
  rw [e1, e2, e3, e4, e5]
  have f1 : 128 * B ≤ B ^ 2 := by nlinarith
  have f2 : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
  have f3 : 128 * B ^ 3 ≤ B ^ 4 := Bfact hB 3
  have f4 : 128 * B ^ 4 ≤ B ^ 5 := Bfact hB 4
  have f5 : 128 * B ^ 5 ≤ B ^ 6 := Bfact hB 5
  have f6 : 128 * B ^ 6 ≤ B ^ 7 := Bfact hB 6
  have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
  have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
  have f9 : 128 * B ^ 9 ≤ B ^ 10 := Bfact hB 9
  have f10 : 128 * B ^ 10 ≤ B ^ 11 := Bfact hB 10
  have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
  have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
  have f13 : 128 * B ^ 13 ≤ B ^ 14 := Bfact hB 13
  have f14 : 128 * B ^ 14 ≤ B ^ 15 := Bfact hB 14
  have f15 : 128 * B ^ 15 ≤ B ^ 16 := Bfact hB 15
  have f16 : 128 * B ^ 16 ≤ B ^ 17 := Bfact hB 16
  have f17 : 128 * B ^ 17 ≤ B ^ 18 := Bfact hB 17
  have f18 : 128 * B ^ 18 ≤ B ^ 19 := Bfact hB 18
  have f19 : 128 * B ^ 19 ≤ B ^ 20 := Bfact hB 19
  have f20 : 128 * B ^ 20 ≤ B ^ 21 := Bfact hB 20
  have f21 : 128 * B ^ 21 ≤ B ^ 22 := Bfact hB 21
  have f22 : 128 * B ^ 22 ≤ B ^ 23 := Bfact hB 22
  have f23 : 128 * B ^ 23 ≤ B ^ 24 := Bfact hB 23
  have f24 : 128 * B ^ 24 ≤ B ^ 25 := Bfact hB 24
  have f25 : 128 * B ^ 25 ≤ B ^ 26 := Bfact hB 25
  have f26 : 128 * B ^ 26 ≤ B ^ 27 := Bfact hB 26
  have f27 : 128 * B ^ 27 ≤ B ^ 28 := Bfact hB 27
  have f28 : 128 * B ^ 28 ≤ B ^ 29 := Bfact hB 28
  have f29 : 128 * B ^ 29 ≤ B ^ 30 := Bfact hB 29
  have f30 : 128 * B ^ 30 ≤ B ^ 31 := Bfact hB 30
  omega

/-- The small parameter `ρ = 2^{-(200 B^{31} + 1)}`. -/
noncomputable def rhoB (B : ℕ) : ℝ := (1 / 2) ^ (200 * B ^ 31 + 1)

/-- **Condition H2** along the chain. -/
theorem condition_H2 {G : GaussianInt[X]} (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) :
    ∀ T, B ^ 8 ≤ T → T < (B ^ 4 + 1) * (4 * B ^ 8) → ∀ t < 2 * T,
      deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3)
          (siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)) t *
      (rhoB B * (quotB (B ^ 4) (4 * B ^ 8) (B ^ 3)
          (siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)) T + 1) *
        (t.factorial * ((((B ^ 3 * T : ℕ) : ℝ)) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ (B ^ 3 * T)) / 7 ^ (B ^ 3 * T) +
          (((B ^ 3 * T : ℕ) : ℝ)) * interpConst (B ^ 3) T *
            ((((B ^ 3 * T : ℕ) : ℝ)) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ (B ^ 3 * T))) + rhoB B +
        rhoB B * lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3)
          (siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)) t) ≤ 1 / 2 := by
  intro T hT hTU t ht
  set Cc := siegelBound G (2 ^ B) (B ^ 4) (4 * B ^ 8) (B ^ 3) (B ^ 8)
  have hCc := siegelBound_le hB hg
  have hCc0 : 0 ≤ Cc := by
    simp only [Cc, siegelBound]
    have : (0 : ℝ) ≤ 1 + (2 ^ B) ^ G.natDegree := by positivity
    positivity
  have hU := paramU_nat_le hB
  have hTle : T ≤ 8 * B ^ 12 := by omega
  have htle : t ≤ 16 * B ^ 12 := by omega
  set n := B ^ 3 * T with hn
  set d := B * (35 * B ^ 9 + (8 * B + 3) * t) + 2 * B * B ^ 7
  set eK := (15 * B + 3) * (n + 1) + n * ((15 * B + 3) * T + 3 * B * n)
  set a := (15 * B + 3) + eK + (27 * B + 7) * t + (6 * B + 3) * n
  set b := B ^ 4 * B ^ 3 + (7 * B + 1 + (12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) +
    (8 * B + 3) * T))
  set c := 7 * B + 1 + (7 * B + ((12 * B + 3 + 22 * B ^ 9 + 3 * B * (4 * B ^ 8) +
    (8 * B + 3) * t) + B ^ 4 * B ^ 3))
  have hD : deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ d := deltaInv_le hB hg hcoeff hCc0 hCc t
  have hQ : quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T ≤ 2 ^ b := quotB_le hB hCc0 hCc T
  have hLp : lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ c := lipQ_le hB hCc0 hCc t
  have hK : (interpConst (B ^ 3) T : ℝ) ≤ 2 ^ eK := interpConst_le hB hTle
  have hnr : ((n : ℕ) : ℝ) ≤ 2 ^ (15 * B + 3) := by exact_mod_cast paramN_le hTle
  have h8 := eightH_pow_le hB n
  have hnt : ((n : ℕ) : ℝ) ^ t ≤ 2 ^ ((15 * B + 3) * t) := pow_le_two_pow (by positivity) hnr t
  have hhn : ((B ^ 3 : ℕ) : ℝ) ^ n ≤ 2 ^ (3 * B * n) :=
    pow_le_two_pow (by positivity) (by push_cast; exact paramH_le B) n
  have hfac := factorial_le_of_lt_twoU hB (t := t) (by omega)
  have hK0 : (0 : ℝ) ≤ interpConst (B ^ 3) T := by positivity
  have hD0 : 0 ≤ deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t := by
    unfold deltaInv
    exact mul_nonneg (pow_nonneg (mul_nonneg (by positivity) (heightQ_nonneg' hCc0 t)) _)
      (pow_nonneg (mahlerMeasure_nonneg _) _)
  have hQ0 : 0 ≤ quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T := by
    unfold quotB; exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (heightQ_nonneg' hCc0 T))
  have hLp0 : 0 ≤ lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t := by
    unfold lipQ; exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg (heightQ_nonneg' hCc0 t) (by positivity)))
  -- the two interpolation terms
  have hX1 : (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
      (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n ≤ 2 ^ a := by
    have h7 : (1 : ℝ) ≤ 7 ^ n := one_le_pow₀ (by norm_num)
    calc (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n
        ≤ (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) := div_le_self (by positivity) h7
      _ ≤ 2 ^ ((12 * B + 4) * t) * (2 ^ (15 * B + 3) * 2 ^ eK * 2 ^ ((3 * B + 3) * n)) := by
          gcongr
      _ = 2 ^ ((12 * B + 4) * t + (15 * B + 3) + eK + (3 * B + 3) * n) := by
          simp only [pow_add]; ring
      _ ≤ 2 ^ a := two_pow_mono (by
          simp only [a]
          have : (12 * B + 4) * t ≤ (27 * B + 7) * t := Nat.mul_le_mul_right _ (by omega)
          have : (3 * B + 3) * n ≤ (6 * B + 3) * n := Nat.mul_le_mul_right _ (by omega)
          omega)
  have hX2 : ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
      (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n) ≤ 2 ^ a := by
    calc ((n : ℕ) : ℝ) * interpConst (B ^ 3) T * (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n)
        ≤ 2 ^ (15 * B + 3) * 2 ^ eK * (2 ^ ((15 * B + 3) * t) * 2 ^ (3 * B * n)) := by gcongr
      _ = 2 ^ ((15 * B + 3) + eK + (15 * B + 3) * t + 3 * B * n) := by
          simp only [pow_add]; ring
      _ ≤ 2 ^ a := two_pow_mono (by
          simp only [a]
          have : (15 * B + 3) * t ≤ (27 * B + 7) * t := Nat.mul_le_mul_right _ (by omega)
          have : 3 * B * n ≤ (6 * B + 3) * n := Nat.mul_le_mul_right _ (by omega)
          omega)
  have hpow1 : ∀ m : ℕ, (2 : ℝ) ^ m + 1 ≤ 2 ^ (m + 1) := fun m => by
    rw [pow_succ]; linarith [one_le_pow₀ (n := m) (by norm_num : (1 : ℝ) ≤ 2)]
  have hY : deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t *
      ((quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T + 1) *
        ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n)) + 1 +
        lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t) ≤ 2 ^ (200 * B ^ 31) := by
    have hQ1 : quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T + 1 ≤ 2 ^ (b + 1) := by
      have := hpow1 b; linarith
    have hsum : (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n) ≤ 2 ^ (a + 1) := by
      have h2a : (2 : ℝ) ^ (a + 1) = 2 * 2 ^ a := by ring
      linarith
    have hL1 : 1 + lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ (c + 1) := by
      have := hpow1 c; linarith
    have hinner : (quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T + 1) *
        ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n)) + 1 +
        lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t ≤ 2 ^ (a + b + c + 3) := by
      have h1 : (quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T + 1) *
          ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
            (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
            (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n)) ≤ 2 ^ (b + 1) * 2 ^ (a + 1) :=
        mul_le_mul hQ1 hsum (by positivity) (by positivity)
      have h2 : (2 : ℝ) ^ (b + 1) * 2 ^ (a + 1) ≤ 2 ^ (a + b + c + 2) := by
        rw [← pow_add]; exact two_pow_mono (by omega)
      have h3 : (2 : ℝ) ^ (c + 1) ≤ 2 ^ (a + b + c + 2) := two_pow_mono (by omega)
      have h4 : (2 : ℝ) ^ (a + b + c + 3) = 2 * 2 ^ (a + b + c + 2) := by
        rw [show a + b + c + 3 = (a + b + c + 2) + 1 by ring, pow_succ]; ring
      linarith
    calc _ ≤ 2 ^ d * 2 ^ (a + b + c + 3) := mul_le_mul hD hinner (by positivity) (by positivity)
      _ = 2 ^ (d + (a + b + c + 3)) := by rw [← pow_add]
      _ ≤ 2 ^ (200 * B ^ 31) := two_pow_mono (by
          have := exponent_H2 hB hTle htle
          rw [← hn] at this
          simp only [d, a, b, c, eK]
          omega)
  have hρ : rhoB B * 2 ^ (200 * B ^ 31) = 1 / 2 := by
    have h1 : ((1 : ℝ) / 2) ^ (200 * B ^ 31) * 2 ^ (200 * B ^ 31) = 1 := by
      rw [← mul_pow]; norm_num
    rw [rhoB, pow_succ]
    linear_combination (1 / 2 : ℝ) * h1
  have hρ0 : 0 ≤ rhoB B := by unfold rhoB; positivity
  calc _ = rhoB B * (deltaInv G (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t *
        ((quotB (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc T + 1) *
          ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
            (8 * ((B ^ 3 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 3) T *
            (((n : ℕ) : ℝ) ^ t * ((B ^ 3 : ℕ) : ℝ) ^ n)) + 1 +
          lipQ (B ^ 4) (4 * B ^ 8) (B ^ 3) Cc t)) := by ring
    _ ≤ rhoB B * 2 ^ (200 * B ^ 31) := mul_le_mul_of_nonneg_left hY hρ0
    _ = 1 / 2 := hρ

end Params

/-- **Measure for an irreducible Gaussian-integer polynomial.** -/
theorem norm_eval_exp_I_ge_of_irreducible {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {B : ℕ} (hB : 128 ≤ B) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) :
    (1 / 2 : ℝ) ^ (B * (200 * B ^ 31 + 1)) ≤
      ‖(G.map toComplex).eval (Complex.exp Complex.I)‖ := by
  have hρ0 : 0 < rhoB B := by unfold rhoB; positivity
  have hρ1 : rhoB B ≤ 1 := by unfold rhoB; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hcount : 2 * (B ^ 8 * B ^ 3 * G.natDegree * 2) ≤ (B ^ 4 + 1) * (4 * B ^ 8) := by
    have : B ^ 8 * B ^ 3 * G.natDegree ≤ B ^ 8 * B ^ 3 * B := Nat.mul_le_mul_left _ hg
    have e : (B ^ 4 + 1) * (4 * B ^ 8) = 4 * (B ^ 8 * B ^ 3 * B) + 4 * B ^ 8 := by ring
    omega
  have hmain := lower_bound_of_conditions hG hdeg (a := 2 ^ B) (one_le_pow₀ (by norm_num)) hcoeff
    (J := B ^ 4) (L := 4 * B ^ 8) (h := B ^ 3) (T₀ := B ^ 8)
    (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega))
    (by have := Nat.one_le_pow 8 B (by omega); omega) hcount
    hρ0 hρ1 (condition_H1 hB hg hcoeff) (condition_H2 hB hg hcoeff)
  calc (1 / 2 : ℝ) ^ (B * (200 * B ^ 31 + 1)) = rhoB B ^ B := by
        unfold rhoB; rw [← pow_mul, mul_comm]
    _ ≤ rhoB B ^ G.natDegree := pow_le_pow_of_le_one hρ0.le hρ1 hg
    _ ≤ _ := hmain

end NLQCLean.Gelfond
