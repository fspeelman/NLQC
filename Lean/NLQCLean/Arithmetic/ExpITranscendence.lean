import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Bertrand

/-!
# A hypothesis-free transcendence measure for `e^i`

For every nonzero integer polynomial `P` of degree at most `N ≥ 1` with coefficients bounded
by `H`, `‖P(e^i)‖²` is at least an explicit positive number depending only on `N` and `H`.

Hermite's method: `‖P(e^i)‖² = Σ_{j,k} a_j a_k e^{(j-k)i}` uses only the exponents `ti`,
`|t| ≤ N`, which are roots of `f = ∏_{m=1}^N (X² + m²) ∈ ℤ[X]`. For a prime `p` put
`h = X^{p-1} f^p` and `S = Σ_k h^{(k)}`. Then `S(ti) = p!·g(ti)` for `t ≠ 0` and
`S(0) = (p-1)!·n` with `n ≡ f(0)^p (mod p)`; the Gaussian-integer part has integer real part.
Taking real parts of `Σ a_j a_k (e^{s} S(0) - S(s)) = Σ a_j a_k P(h, s)` gives an integer
`T ≡ (Σ a_j²) f(0)^p (mod p)`, hence `|T| ≥ 1` for `p` above `N` and `Σ a_j²`, while the
analytic part is at most `C c^p / (p-1)!`. The measure is of the shape
`exp(-N^{O(N)} · poly(H))`, weaker than polynomial type.
-/

namespace NLQCLean.ExpITranscendence

open Polynomial Complex
open scoped Nat

/-- Hermite's base polynomial `∏_{m=1}^N (X² + m²)`. -/
noncomputable def hermiteBase (N : ℕ) : ℤ[X] :=
  ∏ m ∈ Finset.range N, (X ^ 2 + C (((m : ℤ) + 1) ^ 2))

theorem hermiteBase_eval_zero (N : ℕ) :
    (hermiteBase N).eval 0 = ∏ m ∈ Finset.range N, (((m : ℤ) + 1) ^ 2) := by
  simp [hermiteBase, eval_prod]

/-- `t·i` is a root of the base polynomial for `1 ≤ |t| ≤ N`. -/
theorem aeval_hermiteBase_eq_zero {N : ℕ} {t : ℤ} (ht0 : t ≠ 0) (htN : t.natAbs ≤ N) :
    aeval ((t : ℂ) * I) (hermiteBase N) = 0 := by
  rw [hermiteBase, map_prod]
  apply Finset.prod_eq_zero (i := t.natAbs - 1)
  · simp only [Finset.mem_range]; omega
  · have hm : (((t.natAbs - 1 : ℕ) : ℤ) + 1) ^ 2 = t ^ 2 := by
      have h1 : ((t.natAbs - 1 : ℕ) : ℤ) + 1 = (t.natAbs : ℤ) := by omega
      rw [h1, Int.natCast_natAbs, sq_abs]
    rw [hm, map_add, map_pow, aeval_X, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_pow]
    rw [mul_pow, I_sq]
    ring

/-- Gaussian-integer evaluation: `P(t i)` is the image of a Gaussian integer. -/
theorem aeval_intMulI_eq_toComplex (g : ℤ[X]) (t : ℤ) :
    aeval ((t : ℂ) * I) g = ((aeval (⟨0, t⟩ : GaussianInt) g : GaussianInt) : ℂ) := by
  have h : ((t : ℂ) * I) = ((⟨0, t⟩ : GaussianInt) : ℂ) := by
    rw [GaussianInt.toComplex_def']; push_cast; ring
  rw [h]
  exact aeval_algHom_apply (GaussianInt.toComplex.toIntAlgHom) _ g

/-- Hermite's auxiliary polynomial `X^{p-1} f^p`. -/
noncomputable def hermiteAux (N p : ℕ) : ℤ[X] := X ^ (p - 1) * hermiteBase N ^ p

theorem hermiteAux_dvd {N p : ℕ} {t : ℤ} (ht0 : t ≠ 0) (htN : t.natAbs ≤ N) :
    ((X : ℂ[X]) - C ((t : ℂ) * I)) ^ p ∣ (hermiteAux N p).map (algebraMap ℤ ℂ) := by
  have hev : ((hermiteBase N).map (algebraMap ℤ ℂ)).eval ((t : ℂ) * I) = 0 := by
    rw [eval_map_algebraMap]
    exact aeval_hermiteBase_eq_zero ht0 htN
  have hroot : (X : ℂ[X]) - C ((t : ℂ) * I) ∣ (hermiteBase N).map (algebraMap ℤ ℂ) :=
    dvd_iff_isRoot.mpr hev
  have hmap : (hermiteAux N p).map (algebraMap ℤ ℂ) =
      (X : ℂ[X]) ^ (p - 1) * ((hermiteBase N).map (algebraMap ℤ ℂ)) ^ p := by
    simp only [hermiteAux, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rw [hmap]
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hroot p) _

/-! ### Nonnegative coefficients and the value at zero -/

/-- All coefficients are nonnegative. -/
def CoeffNonneg (f : ℤ[X]) : Prop := ∀ i, 0 ≤ f.coeff i

theorem CoeffNonneg.mul {f g : ℤ[X]} (hf : CoeffNonneg f) (hg : CoeffNonneg g) :
    CoeffNonneg (f * g) := fun i => by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

theorem CoeffNonneg.one : CoeffNonneg (1 : ℤ[X]) := fun i => by
  rw [coeff_one]; split_ifs <;> norm_num

theorem CoeffNonneg.pow {f : ℤ[X]} (hf : CoeffNonneg f) (n : ℕ) : CoeffNonneg (f ^ n) := by
  induction n with
  | zero => simpa using CoeffNonneg.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem coeffNonneg_hermiteBase (N : ℕ) : CoeffNonneg (hermiteBase N) := by
  unfold hermiteBase
  induction N with
  | zero => simpa using CoeffNonneg.one
  | succ n ih =>
    rw [Finset.prod_range_succ]
    refine ih.mul fun i => ?_
    rw [coeff_add, coeff_X_pow, coeff_C]
    have : (0 : ℤ) ≤ ((n : ℤ) + 1) ^ 2 := sq_nonneg _
    split_ifs <;> omega

theorem coeffNonneg_hermiteAux (N p : ℕ) : CoeffNonneg (hermiteAux N p) := by
  refine CoeffNonneg.mul (fun i => ?_) ((coeffNonneg_hermiteBase N).pow p)
  rw [coeff_X_pow]; split_ifs <;> norm_num

theorem natDegree_hermiteBase_le (N : ℕ) : (hermiteBase N).natDegree ≤ 2 * N := by
  unfold hermiteBase
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ m ∈ Finset.range N, (X ^ 2 + C (((m : ℤ) + 1) ^ 2) : ℤ[X]).natDegree
      ≤ ∑ _m ∈ Finset.range N, 2 := Finset.sum_le_sum fun m _ =>
        (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le 2) (by simp))
    _ = 2 * N := by simp [mul_comm]

theorem natDegree_hermiteAux_le (N p : ℕ) :
    (hermiteAux N p).natDegree ≤ (p - 1) + p * (2 * N) := by
  unfold hermiteAux
  refine (natDegree_mul_le).trans (add_le_add (natDegree_X_pow_le _) ?_)
  exact (natDegree_pow_le).trans (Nat.mul_le_mul_left _ (natDegree_hermiteBase_le N))

/-- `S(0) = Σ_j j! h_j`. -/
theorem eval_zero_sumIDeriv (h : ℤ[X]) :
    (sumIDeriv h).eval 0 = ∑ j ∈ Finset.range (h.natDegree + 1), (j ! : ℤ) * h.coeff j := by
  rw [sumIDeriv_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- For nonnegative coefficients, `0 ≤ S(0) ≤ D! · h(1)`. -/
theorem eval_zero_sumIDeriv_le {h : ℤ[X]} (hh : CoeffNonneg h) :
    0 ≤ (sumIDeriv h).eval 0 ∧ (sumIDeriv h).eval 0 ≤ (h.natDegree ! : ℤ) * h.eval 1 := by
  rw [eval_zero_sumIDeriv, eval_eq_sum_range]
  simp only [one_pow, mul_one]
  refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hh j), ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (hh j)
  exact_mod_cast Nat.factorial_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem eval_one_hermiteBase_le (N : ℕ) : (hermiteBase N).eval 1 ≤ (1 + (N : ℤ) ^ 2) ^ N := by
  have key : ∀ n ≤ N, (∏ m ∈ Finset.range n, (X ^ 2 + C (((m : ℤ) + 1) ^ 2) : ℤ[X])).eval 1 ≤
      (1 + (N : ℤ) ^ 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [Finset.prod_range_succ, eval_mul, pow_succ]
      have h0 : 0 ≤ (∏ m ∈ Finset.range n, (X ^ 2 + C (((m : ℤ) + 1) ^ 2) : ℤ[X])).eval 1 := by
        rw [eval_prod]
        exact Finset.prod_nonneg fun m _ => by
          simp only [eval_add, eval_pow, eval_X, eval_C]; positivity
      have h1 : (X ^ 2 + C (((n : ℤ) + 1) ^ 2) : ℤ[X]).eval 1 ≤ 1 + (N : ℤ) ^ 2 := by
        simp only [eval_add, eval_pow, eval_X, eval_C, one_pow]
        have : (n : ℤ) + 1 ≤ N := by omega
        nlinarith
      exact mul_le_mul (ih (by omega)) h1 (by simp only [eval_add, eval_pow, eval_X, eval_C]; positivity)
        (by positivity)
  exact key N le_rfl

/-! ### The squared modulus as an exponential sum -/

theorem normSq_aeval_exp_I_eq {P : ℤ[X]} {N : ℕ} (hdeg : P.natDegree ≤ N) :
    (normSq (aeval (exp I) P) : ℂ) = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ((P.coeff j * P.coeff k : ℤ) : ℂ) * exp ((((j : ℤ) - k : ℤ) : ℂ) * I) := by
  rw [← mul_conj, aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg), map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [zsmul_eq_mul, map_mul, map_intCast, map_pow, ← exp_conj, conj_I]
  rw [← exp_nat_mul, ← exp_nat_mul, mul_mul_mul_comm, ← exp_add]
  push_cast
  ring_nf

/-! ### Analytic estimates -/

/-- The Hermite remainder `e^s S(0) − S(s)`, `S = Σ_k f^{(k)}` (as in Mathlib's
Lindemann–Weierstrass analytic part, whose declarations are not exported). -/
noncomputable def hermiteP (f : ℂ[X]) (s : ℂ) : ℂ :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

theorem hasDerivAt_cexp_mul_sumIDeriv (f : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * f.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * f.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv f).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add f]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

theorem hermiteP_eq_integral (f : ℂ[X]) (s : ℂ) :
    hermiteP f s = exp s * (s * ∫ x in (0 : ℝ)..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_cexp_mul_sumIDeriv f s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp only [one_smul, zero_smul, neg_zero, exp_zero, one_mul, hermiteP]
  have he : cexp s * cexp (-s) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  linear_combination (eval s (sumIDeriv f)) * he

theorem hermiteP_map (f : ℤ[X]) (s : ℂ) :
    hermiteP (f.map (algebraMap ℤ ℂ)) s =
      exp s * (((sumIDeriv f).eval 0 : ℤ) : ℂ) - aeval s (sumIDeriv f) := by
  rw [hermiteP, sumIDeriv_map, eval_map_algebraMap, eval_map_algebraMap]
  congr 2
  rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero]
  rfl

/-- The Hermite remainder with an explicit bound on `f` along the segment `[0, s]`. -/
theorem norm_hermiteP_le_of_bound (f : ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖f.eval (x • s)‖ ≤ c) :
    ‖hermiteP f s‖ ≤ Real.exp s.re * (Real.exp ‖s‖ * c * ‖s‖) := by
  rw [hermiteP_eq_integral f s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · exact hc x hx

/-- The explicit constant `c = N (2N²)^N`. -/
def measureC (N : ℕ) : ℕ := N * (2 * N ^ 2) ^ N

theorem norm_aeval_hermiteBase_le {N : ℕ} {z : ℂ} (hz : ‖z‖ ≤ N) :
    ‖aeval z (hermiteBase N)‖ ≤ ((2 * N ^ 2 : ℕ) : ℝ) ^ N := by
  rw [hermiteBase, map_prod, norm_prod]
  calc ∏ m ∈ Finset.range N, ‖aeval z (X ^ 2 + C (((m : ℤ) + 1) ^ 2) : ℤ[X])‖
      ≤ ∏ _m ∈ Finset.range N, ((2 * N ^ 2 : ℕ) : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro m hm
        have hm' : (m : ℝ) + 1 ≤ N := by
          have := Finset.mem_range.mp hm
          exact_mod_cast (show m + 1 ≤ N by omega)
        rw [map_add, map_pow, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast]
        refine (norm_add_le _ _).trans ?_
        rw [norm_pow, norm_intCast, abs_of_nonneg (by positivity)]
        push_cast
        nlinarith [norm_nonneg z, sq_nonneg ((m : ℝ) + 1)]
    _ = _ := by simp

theorem norm_eval_hermiteAux_le {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : ‖z‖ ≤ N) (q : ℕ) :
    ‖((hermiteAux N q).map (algebraMap ℤ ℂ)).eval z‖ ≤ (measureC N : ℝ) ^ q := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [hermiteAux, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, map_X, eval_mul,
    eval_pow, eval_pow, eval_X, eval_map_algebraMap, norm_mul, norm_pow, norm_pow]
  have h1 : ‖z‖ ^ (q - 1) ≤ (N : ℝ) ^ q :=
    (pow_le_pow_left₀ (norm_nonneg _) hz _).trans (pow_le_pow_right₀ hNr (Nat.sub_le _ _))
  have h2 : ‖aeval z (hermiteBase N)‖ ^ q ≤ (((2 * N ^ 2 : ℕ) : ℝ) ^ N) ^ q :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_aeval_hermiteBase_le hz) _
  calc ‖z‖ ^ (q - 1) * ‖aeval z (hermiteBase N)‖ ^ q
      ≤ (N : ℝ) ^ q * (((2 * N ^ 2 : ℕ) : ℝ) ^ N) ^ q :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (measureC N : ℝ) ^ q := by rw [measureC, ← mul_pow]; push_cast; ring

/-- The Hermite remainder at `t i`, `|t| ≤ N`: at most `e^N c^p N`. -/
theorem norm_P_hermiteAux_le {N : ℕ} (hN : 1 ≤ N) (p : ℕ) {t : ℤ} (ht : t.natAbs ≤ N) :
    ‖hermiteP ((hermiteAux N p).map (algebraMap ℤ ℂ)) ((t : ℂ) * I)‖ ≤
      Real.exp N * ((measureC N : ℝ) ^ p * N) := by
  have hs : ‖((t : ℂ) * I)‖ ≤ N := by
    rw [norm_mul, norm_I, mul_one, norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast ht
  have hre : ((t : ℂ) * I).re = 0 := by simp
  refine (norm_hermiteP_le_of_bound _ _ ((measureC N : ℝ) ^ p) fun x hx => ?_).trans ?_
  · apply norm_eval_hermiteAux_le hN
    rw [norm_smul, Real.norm_of_nonneg hx.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans hs
  · rw [hre, Real.exp_zero, one_mul]
    have hexp : Real.exp ‖((t : ℂ) * I)‖ ≤ Real.exp N := Real.exp_le_exp.mpr hs
    have hc : (0 : ℝ) ≤ (measureC N : ℝ) ^ p := by positivity
    calc Real.exp ‖((t : ℂ) * I)‖ * (measureC N : ℝ) ^ p * ‖((t : ℂ) * I)‖
        ≤ Real.exp N * (measureC N : ℝ) ^ p * N :=
          mul_le_mul (mul_le_mul_of_nonneg_right hexp hc) hs (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `A c^{k+1} ≤ k!` once `k ≥ 6c` and `k ≥ A c`. -/
theorem factorial_bound {A c k : ℕ} (hc : 1 ≤ c) (hk1 : 6 * c ≤ k) (hk2 : A * c ≤ k) :
    (A : ℝ) * (c : ℝ) ^ (k + 1) ≤ k ! := by
  have hkpos : (0 : ℝ) < k := by
    have : 1 ≤ k := le_trans (by omega) hk1
    exact_mod_cast this
  -- `k^k / k! ≤ e^k ≤ 3^k`
  have he := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have h3 : Real.exp k ≤ 3 ^ k := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) k
  have hfac : (k : ℝ) ^ k ≤ 3 ^ k * k ! := by
    have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hf] at he
    nlinarith
  -- `(6c)^k ≤ k^k`, so `2^k c^k ≤ k!`
  have h6 : ((6 * c : ℕ) : ℝ) ^ k ≤ (k : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hk1) k
  have h2 : (2 : ℝ) ^ k * (c : ℝ) ^ k ≤ k ! := by
    have : (3 : ℝ) ^ k * ((2 : ℝ) ^ k * (c : ℝ) ^ k) ≤ 3 ^ k * k ! := by
      calc (3 : ℝ) ^ k * ((2 : ℝ) ^ k * (c : ℝ) ^ k) = ((6 * c : ℕ) : ℝ) ^ k := by
            push_cast; rw [mul_pow, ← mul_assoc, ← mul_pow]; norm_num
        _ ≤ _ := h6.trans hfac
    exact le_of_mul_le_mul_left this (by positivity)
  have h2k : ((A * c : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    have : A * c < 2 ^ k := lt_of_le_of_lt hk2 (Nat.lt_two_pow_self)
    exact_mod_cast this.le
  calc (A : ℝ) * (c : ℝ) ^ (k + 1) = ((A * c : ℕ) : ℝ) * (c : ℝ) ^ k := by
        push_cast; ring
    _ ≤ (2 : ℝ) ^ k * (c : ℝ) ^ k := mul_le_mul_of_nonneg_right h2k (by positivity)
    _ ≤ _ := h2

/-- A prime above `N` does not divide `f(0) = ∏ (m+1)²`. -/
theorem prime_not_dvd_hermiteBase_eval_zero {N p : ℕ} (hp : p.Prime) (hpN : N < p) :
    ¬ (p : ℤ) ∣ (hermiteBase N).eval 0 := by
  rw [hermiteBase_eval_zero]
  intro hdvd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨m, hm, hmd⟩ := (Prime.dvd_finsetProd_iff hpz _).mp hdvd
  have hmd' : (p : ℤ) ∣ (m : ℤ) + 1 := hpz.dvd_of_dvd_pow hmd
  have hle : (p : ℤ) ≤ (m : ℤ) + 1 := Int.le_of_dvd (by positivity) hmd'
  have := Finset.mem_range.mp hm
  omega

/-! ### The measure -/

/-- `2 (N+1)² H² 3^N N`, dominating the analytic remainder. -/
def measureA (N H : ℕ) : ℕ := 2 * (N + 1) ^ 2 * H ^ 2 * 3 ^ N * N

/-- The prime is chosen in `(B, 2B]`. -/
def measureB (N H : ℕ) : ℕ :=
  6 * measureC N + measureA N H * measureC N + N + (N + 1) * H ^ 2 + 1

/-- The explicit denominator `2 · ((2N+1)·2B)! · (1+N²)^{N·2B}`. -/
def measureDenominator (N H : ℕ) : ℕ :=
  2 * (((2 * N + 1) * (2 * measureB N H)) ! * (1 + N ^ 2) ^ (N * (2 * measureB N H)))

theorem aeval_zero_int (f : ℤ[X]) : aeval (0 : ℂ) f = ((f.eval 0 : ℤ) : ℂ) := by
  rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Transcendence measure for `e^i`, hypothesis-free.** For a nonzero integer polynomial of
degree at most `N ≥ 1` with coefficients bounded by `H`,
`|P(e^i)|² ≥ 1 / measureDenominator N H`. -/
theorem one_div_le_normSq_aeval_exp_I {P : ℤ[X]} (hP : P ≠ 0) {N H : ℕ} (hN : 1 ≤ N)
    (hdeg : P.natDegree ≤ N) (hH : ∀ i, |P.coeff i| ≤ H) :
    1 / (measureDenominator N H : ℝ) ≤ normSq (aeval (exp I) P) := by
  classical
  set B := measureB N H with hB
  have hB0 : B ≠ 0 := by simp [hB, measureB]
  obtain ⟨p, hp, hBp, hp2B⟩ := Nat.exists_prime_lt_and_le_two_mul B hB0
  have hp0 : 0 < p := hp.pos
  have hNB : N < B := by simp only [hB, measureB]; omega
  have hNp : N < p := hNB.trans hBp
  set c := measureC N with hc
  have hc1 : 1 ≤ c := by
    simp only [hc, measureC]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  set h := hermiteAux N p with hh
  set S := sumIDeriv h with hS
  obtain ⟨gp, -, hgp⟩ := aeval_sumIDeriv ℂ h p
  obtain ⟨g', -, hg'⟩ := eval_sumIDeriv_of_pos h hp0
  set f0 := (hermiteBase N).eval 0 with hf0
  set n : ℤ := f0 ^ p + p * g'.eval 0 with hn
  have hfac : (p ! : ℤ) = p * (p - 1)! := by
    exact_mod_cast (Nat.mul_factorial_pred hp0.ne').symm
  have hS0 : S.eval 0 = ((p - 1)! : ℤ) * n := by
    have hdec : h = (X - C 0) ^ (p - 1) * hermiteBase N ^ p := by
      simp [hh, hermiteAux]
    rw [hg' 0 hdec, nsmul_eq_mul, nsmul_eq_mul, eval_pow, hn, hfac]
    ring
  -- the terms
  set s : ℕ → ℕ → ℂ := fun j k => ((((j : ℤ) - k : ℤ) : ℂ)) * I with hsdef
  set w : GaussianInt := ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    ((P.coeff j * P.coeff k : ℤ) : GaussianInt) *
      (if j = k then 0 else aeval (⟨0, (j : ℤ) - k⟩ : GaussianInt) gp) with hw
  set b0 : ℤ := ∑ j ∈ Finset.range (N + 1), P.coeff j * P.coeff j with hb0
  have hterm : ∀ j ∈ Finset.range (N + 1), ∀ k ∈ Finset.range (N + 1),
      aeval (s j k) S = (if j = k then ((S.eval 0 : ℤ) : ℂ) else 0) +
        (p ! : ℂ) * (((if j = k then 0 else
          aeval (⟨0, (j : ℤ) - k⟩ : GaussianInt) gp) : GaussianInt) : ℂ) := by
    intro j hj k hk
    by_cases hjk : j = k
    · subst hjk
      simp only [hsdef, sub_self, Int.cast_zero, zero_mul, ite_true, map_zero, mul_zero,
        add_zero]
      exact aeval_zero_int S
    · have ht0 : ((j : ℤ) - k) ≠ 0 := by omega
      have htN : ((j : ℤ) - k).natAbs ≤ N := by
        have := Finset.mem_range.mp hj; have := Finset.mem_range.mp hk; omega
      rw [ite_eq_right hjk, ite_eq_right hjk, zero_add, hsdef]
      simp only
      rw [hgp _ (hermiteAux_dvd ht0 htN), nsmul_eq_mul, aeval_intMulI_eq_toComplex]
  -- the main identity
  have hid : (normSq (aeval (exp I) P) : ℂ) * ((S.eval 0 : ℤ) : ℂ) -
      ((b0 : ℤ) : ℂ) * ((S.eval 0 : ℤ) : ℂ) - (p ! : ℂ) * (w : ℂ) =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ((P.coeff j * P.coeff k : ℤ) : ℂ) * hermiteP (h.map (algebraMap ℤ ℂ)) (s j k) := by
    simp_rw [hermiteP_map, mul_sub, Finset.sum_sub_distrib]
    rw [normSq_aeval_exp_I_eq hdeg, Finset.sum_mul]
    have h2 : ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ((P.coeff j * P.coeff k : ℤ) : ℂ) * aeval (s j k) S =
        ((b0 : ℤ) : ℂ) * ((S.eval 0 : ℤ) : ℂ) + (p ! : ℂ) * (w : ℂ) := by
      rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by
        rw [hterm j hj k hk]]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_range]
      rw [hw, hb0]
      simp only [map_sum, map_mul, map_intCast, Finset.mul_sum, Int.cast_sum, Int.cast_mul,
        Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [ite_eq_left (Finset.mem_range.mp hj)]
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    rw [sub_sub, ← h2]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hsdef]
    ring
  -- real parts
  set R : ℂ := ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ((P.coeff j * P.coeff k : ℤ) : ℂ) * hermiteP (h.map (algebraMap ℤ ℂ)) (s j k) with hR
  set ν : ℝ := normSq (aeval (exp I) P) with hν
  have hν0 : 0 ≤ ν := normSq_nonneg _
  have hre : ν * ((S.eval 0 : ℤ) : ℝ) - (b0 : ℝ) * ((S.eval 0 : ℤ) : ℝ) -
      (p ! : ℝ) * (w.re : ℝ) = R.re := by
    have := congrArg Complex.re hid
    rw [← this]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im,
      ← GaussianInt.intCast_re, mul_zero, sub_zero, zero_mul]
  -- the analytic bound
  have hE : ∀ j ∈ Finset.range (N + 1), ∀ k ∈ Finset.range (N + 1),
      ‖hermiteP (h.map (algebraMap ℤ ℂ)) (s j k)‖ ≤ Real.exp N * ((c : ℝ) ^ p * N) := by
    intro j hj k hk
    have := Finset.mem_range.mp hj; have := Finset.mem_range.mp hk
    exact norm_P_hermiteAux_le hN p (by omega)
  have hcoef : ∀ j k, ‖((P.coeff j * P.coeff k : ℤ) : ℂ)‖ ≤ (H : ℝ) ^ 2 := by
    intro j k
    rw [norm_intCast, Int.cast_mul, abs_mul, sq]
    have h1 : |(P.coeff j : ℝ)| ≤ H := by exact_mod_cast hH j
    have h2 : |(P.coeff k : ℝ)| ≤ H := by exact_mod_cast hH k
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hRle : ‖R‖ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 * ((H : ℝ) ^ 2 * (Real.exp N * ((c : ℝ) ^ p * N))) := by
    calc ‖R‖ ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          ‖((P.coeff j * P.coeff k : ℤ) : ℂ) * hermiteP (h.map (algebraMap ℤ ℂ)) (s j k)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ _j ∈ Finset.range (N + 1), ∑ _k ∈ Finset.range (N + 1),
          (H : ℝ) ^ 2 * (Real.exp N * ((c : ℝ) ^ p * N)) := by
          refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul]
          exact mul_le_mul (hcoef j k) (hE j hj k hk) (norm_nonneg _) (by positivity)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hk : p - 1 + 1 = p := Nat.sub_add_cancel hp0
  have hfb := factorial_bound (A := measureA N H) (c := c) (k := p - 1) hc1
    (by simp only [hB, measureB, hc] at hBp ⊢; omega)
    (by simp only [hB, measureB, hc] at hBp ⊢; omega)
  rw [hk] at hfb
  have he3 : Real.exp N ≤ 3 ^ N := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) N
  have hRhalf : 2 * ‖R‖ ≤ ((p - 1)! : ℝ) := by
    refine le_trans ?_ hfb
    rw [measureA]
    push_cast
    have hcp : (0 : ℝ) ≤ (c : ℝ) ^ p * N := by positivity
    calc 2 * ‖R‖ ≤ 2 * (((N : ℝ) + 1) ^ 2 * ((H : ℝ) ^ 2 * (Real.exp N * ((c : ℝ) ^ p * N)))) := by
          have := hRle; push_cast at this; linarith
      _ ≤ 2 * (((N : ℝ) + 1) ^ 2 * ((H : ℝ) ^ 2 * (3 ^ N * ((c : ℝ) ^ p * N)))) := by
          gcongr
      _ = _ := by ring
  -- the integer `T`
  set T : ℤ := b0 * n + p * w.re with hT
  have hfacpos : (0 : ℝ) < ((p - 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpfac : (p ! : ℝ) = p * ((p - 1)! : ℝ) := by exact_mod_cast hfac
  have hS0r : ((S.eval 0 : ℤ) : ℝ) = ((p - 1)! : ℝ) * (n : ℝ) := by rw [hS0]; push_cast; ring
  have hdiff : |ν * n - T| ≤ 1 / 2 := by
    have hkey : ((p - 1)! : ℝ) * (ν * n - T) = R.re := by
      rw [← hre, hS0r, hpfac, hT]; push_cast; ring
    have habs : ((p - 1)! : ℝ) * |ν * n - T| ≤ ((p - 1)! : ℝ) * (1 / 2) := by
      rw [← abs_of_pos hfacpos, ← abs_mul, hkey, abs_of_pos hfacpos]
      linarith [Complex.abs_re_le_norm R]
    exact le_of_mul_le_mul_left habs hfacpos
  -- `p ∤ T`
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hb0pos : 1 ≤ b0 := by
    have hlc : P.coeff P.natDegree ≠ 0 := by
      rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hP
    have hmem : P.natDegree ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun j => P.coeff j * P.coeff j)
      (fun j _ => mul_self_nonneg _) hmem
    have hpos : 0 < P.coeff P.natDegree * P.coeff P.natDegree := mul_self_pos.mpr hlc
    rw [hb0]; omega
  have hb0lt : b0 < p := by
    have hle : b0 ≤ ((N + 1) * H ^ 2 : ℕ) := by
      rw [hb0]
      calc ∑ j ∈ Finset.range (N + 1), P.coeff j * P.coeff j
          ≤ ∑ _j ∈ Finset.range (N + 1), ((H : ℤ) ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have := hH j
            rw [← sq]; exact sq_le_sq' (by linarith [abs_le.mp this]) (abs_le.mp this).2
        _ = _ := by simp
    have : (N + 1) * H ^ 2 < B := by simp only [hB, measureB]; omega
    have : ((N + 1) * H ^ 2 : ℕ) < (p : ℤ) := by exact_mod_cast this.trans hBp
    omega
  have hTne : T ≠ 0 := by
    intro hT0
    have hdvd : (p : ℤ) ∣ b0 * n := by
      have : b0 * n = T - p * w.re := by rw [hT]; ring
      rw [this, hT0, zero_sub]
      exact (dvd_mul_right _ _).neg_right
    rcases hpz.dvd_or_dvd hdvd with h1 | h1
    · have := Int.le_of_dvd (by omega) h1
      omega
    · have h2 : (p : ℤ) ∣ f0 ^ p := by
        have : f0 ^ p = n - p * g'.eval 0 := by rw [hn]; ring
        rw [this]
        exact dvd_sub h1 (dvd_mul_right _ _)
      exact prime_not_dvd_hermiteBase_eval_zero hp hNp (hpz.dvd_of_dvd_pow h2)
  have hT1 : (1 : ℝ) ≤ |(T : ℝ)| := by
    have : 1 ≤ |T| := Int.one_le_abs hTne
    exact_mod_cast this
  -- sizes
  obtain ⟨hS0nn, hS0le⟩ := eval_zero_sumIDeriv_le (coeffNonneg_hermiteAux N p)
  have hn0 : 0 ≤ n := by
    have h0 : (0 : ℤ) ≤ ((p - 1)! : ℤ) * n := hS0 ▸ hS0nn
    have hf : (0 : ℤ) < ((p - 1)! : ℤ) := by positivity
    exact nonneg_of_mul_nonneg_right h0 hf
  have hn0r : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  have hνn : (1 / 2 : ℝ) ≤ ν * n := by
    have h1 := abs_le.mp hdiff
    rcases le_or_gt 0 T with hT0 | hT0
    · have : (1 : ℝ) ≤ T := by rw [abs_of_nonneg (by exact_mod_cast hT0)] at hT1; exact hT1
      linarith
    · have : (T : ℝ) ≤ -1 := by
        rw [abs_of_neg (by exact_mod_cast hT0)] at hT1; linarith
      nlinarith [mul_nonneg hν0 hn0r]
  have hnpos : (0 : ℝ) < n := by
    rcases hn0r.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hνn; linarith
  -- `n ≤ D! h(1)`
  have hnle : (n : ℝ) ≤ ((h.natDegree ! : ℕ) : ℝ) * ((h.eval 1 : ℤ) : ℝ) := by
    have h1 : (n : ℤ) ≤ ((p - 1)! : ℤ) * n :=
      le_mul_of_one_le_left hn0 (by exact_mod_cast Nat.factorial_pos _)
    have h2 := (h1.trans_eq hS0.symm).trans hS0le
    exact_mod_cast h2
  have hdegh : h.natDegree ≤ (2 * N + 1) * (2 * B) := by
    have := natDegree_hermiteAux_le N p
    have hp2 : p ≤ 2 * B := hp2B
    calc h.natDegree ≤ (p - 1) + p * (2 * N) := this
      _ ≤ (2 * N + 1) * p := by
          have : p - 1 ≤ p := Nat.sub_le _ _
          nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hp2
  have hev : h.eval 1 = (hermiteBase N).eval 1 ^ p := by
    simp [hh, hermiteAux, eval_mul, eval_pow]
  have hb0' : 0 ≤ (hermiteBase N).eval 1 := by
    rw [hermiteBase, eval_prod]
    exact Finset.prod_nonneg fun m _ => by simp only [eval_add, eval_pow, eval_X, eval_C]; positivity
  have hh1 : ((h.eval 1 : ℤ) : ℝ) ≤ ((1 + N ^ 2) ^ (N * (2 * B)) : ℕ) := by
    have hb1 := eval_one_hermiteBase_le N
    have : h.eval 1 ≤ ((1 + (N : ℤ) ^ 2) ^ N) ^ p := by
      rw [hev]; exact pow_le_pow_left₀ hb0' hb1 p
    have hpow : ((1 + (N : ℤ) ^ 2) ^ N) ^ p ≤ (1 + (N : ℤ) ^ 2) ^ (N * (2 * B)) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by nlinarith) (Nat.mul_le_mul_left _ hp2B)
    have := this.trans hpow
    exact_mod_cast this
  have hdenom : 2 * (n : ℝ) ≤ (measureDenominator N H : ℝ) := by
    rw [measureDenominator, ← hB]
    push_cast
    have hf : ((h.natDegree ! : ℕ) : ℝ) ≤ (((2 * N + 1) * (2 * B)) ! : ℕ) := by
      exact_mod_cast Nat.factorial_le hdegh
    have hh1' : ((h.eval 1 : ℤ) : ℝ) ≤ (1 + (N : ℝ) ^ 2) ^ (N * (2 * B)) := by
      have := hh1; push_cast at this; exact this
    have : (n : ℝ) ≤ (((2 * N + 1) * (2 * B)) ! : ℕ) * (1 + (N : ℝ) ^ 2) ^ (N * (2 * B)) := by
      refine hnle.trans (mul_le_mul hf hh1' ?_ (by positivity))
      have hpos1 : (0 : ℤ) ≤ h.eval 1 := by rw [hev]; exact pow_nonneg hb0' p
      exact_mod_cast hpos1
    linarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  calc 1 / (measureDenominator N H : ℝ) ≤ 1 / (2 * n) := one_div_le_one_div_of_le h2n hdenom
    _ ≤ ν := by
        rw [div_le_iff₀ h2n]
        linarith

/-! ### A compact form of the measure -/

/-- The single base `Z = 6 (N+1)² (H+1)²`. -/
def measureZ (N H : ℕ) : ℕ := 6 * (N + 1) ^ 2 * (H + 1) ^ 2

theorem measureDenominator_le {N : ℕ} (H : ℕ) (hN : 1 ≤ N) :
    measureDenominator N H ≤ measureZ N H ^ (measureZ N H ^ (2 * N + 9)) := by
  set Z := measureZ N H with hZ
  have hH1 : 1 ≤ (H + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN1 : (N + 1) ^ 2 ≤ Z := by
    rw [hZ, measureZ]; nlinarith
  have hZ1 : 1 ≤ Z := le_trans (Nat.one_le_pow _ _ (by omega)) hN1
  have hZN : 2 * N + 9 ≤ Z := by
    have : 2 * N + 9 ≤ 6 * (N + 1) ^ 2 := by nlinarith
    calc 2 * N + 9 ≤ 6 * (N + 1) ^ 2 := this
      _ ≤ Z := by rw [hZ, measureZ]; nlinarith
  have hZ4 : 4 * N + 2 ≤ Z := by
    have : 4 * N + 2 ≤ 6 * (N + 1) ^ 2 := by nlinarith
    calc 4 * N + 2 ≤ 6 * (N + 1) ^ 2 := this
      _ ≤ Z := by rw [hZ, measureZ]; nlinarith
  have hpow : ∀ {a b : ℕ}, a ≤ b → Z ^ a ≤ Z ^ b := fun h => Nat.pow_le_pow_right hZ1 h
  have h2N2 : 2 * N ^ 2 ≤ Z := by rw [hZ, measureZ]; nlinarith
  have hNZ : N ≤ Z := by omega
  have hc : measureC N ≤ Z ^ (N + 1) := by
    rw [measureC]
    calc N * (2 * N ^ 2) ^ N ≤ Z * Z ^ N := Nat.mul_le_mul hNZ (Nat.pow_le_pow_left h2N2 N)
      _ = Z ^ (N + 1) := by ring
  have hA : measureA N H ≤ Z ^ (N + 2) := by
    rw [measureA]
    have h1 : 2 * (N + 1) ^ 2 * H ^ 2 ≤ Z := by
      rw [hZ, measureZ]
      have : H ^ 2 ≤ (H + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    have h3 : 3 ^ N ≤ Z ^ N := Nat.pow_le_pow_left (by omega) N
    calc 2 * (N + 1) ^ 2 * H ^ 2 * 3 ^ N * N ≤ Z * Z ^ N * Z :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h3) hNZ
      _ = Z ^ (N + 2) := by ring
  have hB : measureB N H ≤ Z ^ (2 * N + 5) := by
    rw [measureB]
    have h1 : 6 * measureC N ≤ Z ^ (2 * N + 3) :=
      calc 6 * measureC N ≤ Z * Z ^ (N + 1) := Nat.mul_le_mul (by omega) hc
        _ = Z ^ (N + 2) := by ring
        _ ≤ Z ^ (2 * N + 3) := hpow (by omega)
    have h2 : measureA N H * measureC N ≤ Z ^ (2 * N + 3) :=
      (Nat.mul_le_mul hA hc).trans (by rw [← pow_add]; exact hpow (by omega))
    have h3 : N + (N + 1) * H ^ 2 + 1 ≤ Z ^ (2 * N + 3) := by
      have : N + (N + 1) * H ^ 2 + 1 ≤ Z := by
        rw [hZ, measureZ]
        have : H ^ 2 ≤ (H + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith
      exact this.trans (by simpa using hpow (show 1 ≤ 2 * N + 3 by omega))
    have h4 : 3 * Z ^ (2 * N + 3) ≤ Z ^ (2 * N + 5) := by
      calc 3 * Z ^ (2 * N + 3) ≤ Z ^ 2 * Z ^ (2 * N + 3) := Nat.mul_le_mul_right _
            (le_trans (by norm_num : 3 ≤ 6 ^ 2) (Nat.pow_le_pow_left (by omega : 6 ≤ Z) 2))
        _ = Z ^ (2 * N + 5) := by ring
    omega
  set E := Z ^ (2 * N + 7) with hE
  have hD : (2 * N + 1) * (2 * measureB N H) ≤ E := by
    calc (2 * N + 1) * (2 * measureB N H) = (2 * (2 * N + 1)) * measureB N H := by ring
      _ ≤ Z * Z ^ (2 * N + 5) := Nat.mul_le_mul (by omega) hB
      _ = Z ^ (2 * N + 6) := by ring
      _ ≤ E := hpow (by omega)
  have hfac : ((2 * N + 1) * (2 * measureB N H)) ! ≤ Z ^ ((2 * N + 7) * E) :=
    (Nat.factorial_le hD).trans ((Nat.factorial_le_pow E).trans (by rw [hE, ← pow_mul]))
  have hpw : (1 + N ^ 2) ^ (N * (2 * measureB N H)) ≤ Z ^ E := by
    refine (Nat.pow_le_pow_left (by rw [hZ, measureZ]; nlinarith) _).trans (hpow ?_)
    exact le_trans (by nlinarith) hD
  calc measureDenominator N H
      ≤ Z * (Z ^ ((2 * N + 7) * E) * Z ^ E) := by
        rw [measureDenominator]
        exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul hfac hpw)
    _ = Z ^ (1 + (2 * N + 8) * E) := by ring
    _ ≤ Z ^ (Z ^ (2 * N + 9)) := by
        apply hpow
        have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
        calc 1 + (2 * N + 8) * E ≤ (2 * N + 9) * E := by nlinarith
          _ ≤ Z * E := Nat.mul_le_mul_right _ hZN
          _ = Z ^ (2 * N + 8) := by rw [hE, ← pow_succ']
          _ ≤ Z ^ (2 * N + 9) := hpow (by omega)

/-- **Transcendence measure for `e^i`, compact form.** For a nonzero integer polynomial of
degree at most `N ≥ 1` with coefficients bounded by `H` and `Z = 6(N+1)²(H+1)²`,
`|P(e^i)|² ≥ Z^{-Z^{2N+9}}`. -/
theorem normSq_aeval_exp_I_ge {P : ℤ[X]} (hP : P ≠ 0) {N H : ℕ} (hN : 1 ≤ N)
    (hdeg : P.natDegree ≤ N) (hH : ∀ i, |P.coeff i| ≤ H) :
    1 / ((measureZ N H : ℝ) ^ (measureZ N H ^ (2 * N + 9))) ≤ normSq (aeval (exp I) P) := by
  refine le_trans ?_ (one_div_le_normSq_aeval_exp_I hP hN hdeg hH)
  have hden : (0 : ℝ) < measureDenominator N H := by
    rw [measureDenominator]; positivity
  apply one_div_le_one_div_of_le hden
  exact_mod_cast measureDenominator_le H hN

end NLQCLean.ExpITranscendence
