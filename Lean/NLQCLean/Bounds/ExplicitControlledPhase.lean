import NLQCLean.Bounds.ExplicitGateEpigraph
import NLQCLean.Arithmetic.SeparationCertificate
import NLQCLean.Arithmetic.BivariateFactor
import NLQCLean.Arithmetic.PhaseTranscendence
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Effective bound for an explicit controlled phase (`thm:explicit`)

Appendix C of the robust companion, for two qubits. For every nonzero real
algebraic angle `θ`, in particular the named gate `C₁ = diag(1,1,1,e^i)`, there
is `C_E > 0` with

`g_K(θ) ≥ exp(-exp(C_E K²))` for every footprint `K ≥ 1`,

so every pure or common-map mixed protocol of footprint at most `K` has Choi
infidelity (score deficit) at least `exp(-exp(C_E K²))`; with free
standard-Borel classical messages and quantum footprint `Kq ≥ 1` the bound is
`exp(-exp(256 C_E Kq¹⁰))`. Consequently `log₂ K ≥ ½ log₂ ln ln(1/ε) - O(1)`
and `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - O(1)`.

The proof uses exactly two external inputs, `BasuPollackRoyExistentialElimination`
(E-QE) and the polynomial-type transcendence measure
`PolynomialTypeTranscendenceMeasureExpAngle` (weak E-TM), which Cijsouw's
theorem implies (`CijsouwTranscendenceMeasureExp.polynomialType`) and which is proved in
`Arithmetic/GelfondAngleMeasure` (`Bounds/ExplicitControlledPhaseAngle` gives the E-QE-only
forms); positivity of
`g_K(θ)` is the proved exact exclusion. The sources state that the constants are
effectively computable; here only their existence is proved.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial ExplicitGate ClassicalCommunication

/-- A nonzero real algebraic angle has nonzero sine: otherwise `e^{iθ} = ±1`
would be algebraic, contradicting Hermite–Lindemann. -/
theorem sin_ne_zero_of_isAlgebraic {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    Real.sin θ ≠ 0 := by
  intro hsin
  have hcos : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
    have h := Real.cos_sq_add_sin_sq θ
    rw [hsin] at h
    have : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  have halg : IsAlgebraic ℚ (Real.cos θ) := by
    rcases hcos with h | h <;> rw [h]
    · exact isAlgebraic_one
    · exact isAlgebraic_one.neg
  exact transcendental_exp_angle hθ0 hθ (isAlgebraic_exp_angle_of_cos halg)

/-- The exponent `iθ` is a nonzero algebraic number. -/
theorem isAlgebraic_angle_mul_I {θ : ℝ} (hθ : IsAlgebraic ℚ θ) :
    IsAlgebraic ℚ ((θ : ℂ) * Complex.I) := by
  have hθc : IsAlgebraic ℚ (θ : ℂ) := by
    simpa only [Complex.coe_algebraMap] using hθ.algebraMap (A := ℂ)
  exact hθc.mul (Complex.isIntegral_I ℚ).isAlgebraic

theorem abs_intCast_le_of_natAbs_lt {z : ℤ} {n : ℕ} (h : z.natAbs < 2 ^ n) :
    |(z : ℝ)| ≤ (2 : ℝ) ^ n := by
  have h' : ((z.natAbs : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h.le
  rw [show |(z : ℝ)| = ((z.natAbs : ℤ) : ℝ) by rw [Int.natCast_natAbs, Int.cast_abs]]
  exact_mod_cast h'

section Arithmetic

theorem two_pow_le_exp (n : ℝ) (hn : 0 ≤ n) : (2 : ℝ) ^ n ≤ Real.exp n := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have := Real.log_two_lt_d9
  nlinarith

theorem two_pow_nat_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have := two_pow_le_exp (n : ℝ) (Nat.cast_nonneg n)
  rwa [Real.rpow_natCast] at this

theorem natCast_succ_le_exp (M : ℕ) : ((M + 1 : ℕ) : ℝ) ≤ Real.exp M := by
  have := Real.add_one_le_exp (M : ℝ)
  push_cast
  linarith

/-- The final quotient bound, from a lower bound on the separation level. -/
theorem explicit_gap_arith {M p : ℕ} (hM : 1 ≤ M) (hp : 1 ≤ p) {A τ σ H : ℝ} (hA : 0 ≤ A)
    (hτ : 0 ≤ τ) (hσ : Real.exp (-(A * (M : ℝ) ^ p)) ≤ σ) (hH : 0 < H)
    (hHle : H ≤ Real.exp (τ * M)) :
    Real.exp (-((A + 4 + τ) * (M : ℝ) ^ p)) ≤
      min 1 (((2 : ℝ) ^ M)⁻¹ * σ) / ((M + 1 : ℕ) ^ 3 * H) := by
  have hMp : (M : ℝ) ≤ (M : ℝ) ^ p := by
    exact_mod_cast Nat.le_self_pow (by omega) M
  have h2M : (2 : ℝ) ^ M ≤ Real.exp M := two_pow_nat_le_exp M
  have hnum : Real.exp (-((M : ℝ) + A * (M : ℝ) ^ p)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * σ) := by
    apply le_min
    · rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (by positivity)
    · calc Real.exp (-((M : ℝ) + A * (M : ℝ) ^ p))
          = (Real.exp M)⁻¹ * Real.exp (-(A * (M : ℝ) ^ p)) := by
            rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
        _ ≤ ((2 : ℝ) ^ M)⁻¹ * σ := by
            apply mul_le_mul _ hσ (Real.exp_pos _).le (by positivity)
            exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr h2M
  have hden : ((M + 1 : ℕ) : ℝ) ^ 3 * H ≤ Real.exp (3 * M + τ * M) := by
    rw [Real.exp_add]
    apply mul_le_mul _ hHle hH.le (Real.exp_pos _).le
    rw [show (3 : ℝ) * M = M * 3 by ring, Real.exp_mul (M : ℝ) 3]
    exact pow_le_pow_left₀ (by positivity) (natCast_succ_le_exp M) 3 |>.trans_eq
      (by rw [← Real.rpow_natCast]; norm_num)
  have hdenpos : 0 < ((M + 1 : ℕ) : ℝ) ^ 3 * H := by positivity
  rw [le_div_iff₀ hdenpos]
  calc Real.exp (-((A + 4 + τ) * (M : ℝ) ^ p)) * (((M + 1 : ℕ) : ℝ) ^ 3 * H)
      ≤ Real.exp (-((A + 4 + τ) * (M : ℝ) ^ p)) * Real.exp (3 * M + τ * M) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = Real.exp (-((A + 4 + τ) * (M : ℝ) ^ p) + (3 * M + τ * M)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-((M : ℝ) + A * (M : ℝ) ^ p)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hMp hτ]
    _ ≤ _ := hnum

/-- The logarithm of the separation height `(M+1) 2^M 2^{τM}`. -/
theorem log_explicit_height_le (M τ : ℕ) :
    Real.log (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) ≤ (2 + τ) * M := by
  have hpos : (0 : ℝ) < (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) := by positivity
  rw [Real.log_le_iff_le_exp hpos]
  have h1 := natCast_succ_le_exp M
  have h2 : (2 : ℝ) ^ M ≤ Real.exp M := two_pow_nat_le_exp M
  have h3 : (2 : ℝ) ^ (τ * M) ≤ Real.exp ((τ : ℝ) * M) := by
    have := two_pow_nat_le_exp (τ * M)
    push_cast at this
    exact this
  have : (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) ≤
      Real.exp M * Real.exp M * Real.exp ((τ : ℝ) * M) := by
    push_cast
    have := mul_le_mul (mul_le_mul (by exact_mod_cast h1) h2 (by positivity) (Real.exp_pos _).le)
      h3 (by positivity) (by positivity)
    simpa using this
  refine this.trans (le_of_eq ?_)
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- The separation level at degree `2M` and height `(M+1) 2^M 2^{τM}` for a
transcendence measure `exp(-C (N + log H)^c)` of polynomial type. -/
theorem explicit_separation_level {M τ c : ℕ} {C : ℝ} (hC : 0 < C) :
    Real.exp (-(C * (4 + τ : ℝ) ^ c * (M : ℝ) ^ c)) ≤
      Real.exp (-(C * (((2 * M : ℕ) : ℝ) +
        Real.log (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ)) ^ c)) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hlog := log_explicit_height_le M τ
  have hlog0 : 0 ≤ Real.log (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hcast : (((2 * M : ℕ) : ℝ)) = 2 * (M : ℝ) := by push_cast; ring
  have hle : ((2 * M : ℕ) : ℝ) + Real.log (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) ≤
      (4 + τ : ℝ) * M := by
    rw [hcast]; linarith
  have h0 : 0 ≤ ((2 * M : ℕ) : ℝ) + Real.log (((M + 1) * 2 ^ M * 2 ^ (τ * M) : ℕ) : ℝ) := by
    positivity
  rw [mul_assoc C, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle c) hC.le

theorem twelve_pow_le_exp (n : ℕ) : (12 : ℝ) ^ n ≤ Real.exp (3 * n) := by
  have h12 : (12 : ℝ) ≤ Real.exp 3 := by
    have := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 3
    norm_num at this ⊢
    linarith
  calc (12 : ℝ) ^ n ≤ Real.exp 3 ^ n := pow_le_pow_left₀ (by norm_num) h12 n
    _ = Real.exp (3 * n) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Absorption of all format parameters into `exp(C_E K²)`. -/
theorem explicit_exponent_le {C : ℝ} (hC : 0 < C) (a p : ℕ) {K n : ℕ} (hK : 1 ≤ K)
    (hn : n ≤ 1 + 82 * K ^ 2) :
    (C + 1) * (4 + ((56 + 14 * K : ℕ) : ℝ)) ^ p * ((12 ^ (a * (n + 1)) : ℕ) : ℝ) ^ p ≤
      Real.exp ((Real.log (C + 1) + 6 * p + 252 * a * p) * (K : ℝ) ^ 2) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hlogC : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  have h1 : C + 1 ≤ Real.exp (Real.log (C + 1) * (K : ℝ) ^ 2) := by
    calc C + 1 = Real.exp (Real.log (C + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right hlogC hK2)
  have h2 : 4 + ((56 + 14 * K : ℕ) : ℝ) ≤ Real.exp (6 * (K : ℝ) ^ 2) := by
    have hK1 := Real.add_one_le_exp ((K : ℝ) ^ 2)
    have h5 : (74 : ℝ) ≤ Real.exp 5 := by
      have := Real.exp_one_gt_d9
      have h5' : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h5']
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 5
      norm_num at this ⊢
      linarith
    have : 4 + ((56 + 14 * K : ℕ) : ℝ) ≤ 74 * (K : ℝ) ^ 2 := by push_cast; nlinarith
    calc 4 + ((56 + 14 * K : ℕ) : ℝ) ≤ 74 * (K : ℝ) ^ 2 := this
      _ ≤ Real.exp 5 * Real.exp ((K : ℝ) ^ 2) := by
          apply mul_le_mul h5 _ (by positivity) (Real.exp_pos _).le
          linarith
      _ = Real.exp (5 + (K : ℝ) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have h2p : (4 + ((56 + 14 * K : ℕ) : ℝ)) ^ p ≤ Real.exp (6 * p * (K : ℝ) ^ 2) := by
    calc (4 + ((56 + 14 * K : ℕ) : ℝ)) ^ p ≤ Real.exp (6 * (K : ℝ) ^ 2) ^ p :=
          pow_le_pow_left₀ (by positivity) h2 p
      _ = Real.exp (6 * p * (K : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have h3 : ((12 ^ (a * (n + 1)) : ℕ) : ℝ) ^ p ≤ Real.exp (252 * a * p * (K : ℝ) ^ 2) := by
    push_cast
    rw [← pow_mul]
    refine (twelve_pow_le_exp _).trans (Real.exp_le_exp.mpr ?_)
    have hn' : ((n : ℝ)) ≤ 1 + 82 * (K : ℝ) ^ 2 := by exact_mod_cast hn
    push_cast
    have hap : (0 : ℝ) ≤ a * p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn' hap, mul_le_mul_of_nonneg_left hK2 hap]
  calc (C + 1) * (4 + ((56 + 14 * K : ℕ) : ℝ)) ^ p * ((12 ^ (a * (n + 1)) : ℕ) : ℝ) ^ p
      ≤ Real.exp (Real.log (C + 1) * (K : ℝ) ^ 2) * Real.exp (6 * p * (K : ℝ) ^ 2) *
          Real.exp (252 * a * p * (K : ℝ) ^ 2) :=
        mul_le_mul (mul_le_mul h1 h2p (by positivity) (Real.exp_pos _).le) h3
          (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- Cijsouw's measure is of polynomial type, with exponent `3`. -/
theorem CijsouwTranscendenceMeasureExp.polynomialType (hTM : CijsouwTranscendenceMeasureExp) :
    PolynomialTypeTranscendenceMeasureExpAngle := by
  intro θ hθ0 hθ
  have hα : ((θ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hθ0) Complex.I_ne_zero
  obtain ⟨C, hC, htm⟩ := hTM _ hα (isAlgebraic_angle_mul_I hθ)
  refine ⟨C, 3, hC, fun N H P hP hPN hcoeff => le_of_lt (lt_of_le_of_lt ?_
    (htm N H P hP hPN hcoeff))⟩
  have hH : 1 ≤ H := by
    by_contra h
    have hP0 : P = 0 := by
      ext i
      have := hcoeff i
      simp only [show H = 0 by omega, Nat.cast_zero, abs_nonpos_iff] at this
      simpa using this
    simp [hP0] at hP
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + Real.log H) ^ 2 := pow_le_pow_left₀ hN (by linarith) 2
  calc C * (N : ℝ) ^ 2 * ((N : ℝ) + Real.log H)
      ≤ C * ((N : ℝ) + Real.log H) ^ 2 * ((N : ℝ) + Real.log H) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq hC.le
    _ = C * ((N : ℝ) + Real.log H) ^ 3 := by ring

end Arithmetic

/-- **Theorem E (`thm:explicit`), least-deficit form.** Under E-QE and weak E-TM,
for every nonzero real algebraic angle `θ` there is `C_E > 0` with
`exp(-exp(C_E K²)) ≤ g_K(θ)` for every footprint `K ≥ 1`. -/
theorem exists_explicit_controlledPhaseLeastDeficit_lower_bound
    (hQE : BasuPollackRoyExistentialElimination)
    (hTM : PolynomialTypeTranscendenceMeasureExpAngle)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K θ := by
  obtain ⟨a, hqe⟩ := hQE
  obtain ⟨Cc, c, hCc, htm⟩ := hTM θ hθ0 hθ
  have hsin := sin_ne_zero_of_isAlgebraic hθ0 hθ
  refine ⟨Real.log (Cc + 1) + 6 * (c + 1 : ℕ) + 252 * a * (c + 1 : ℕ),
    by have := Real.log_nonneg (show (1 : ℝ) ≤ Cc + 1 by linarith); positivity,
    fun K hK => ?_⟩
  obtain ⟨t, hbox, hcount, -, -, -, -, hupper, hattain⟩ :=
    exists_controlledPhaseLeastDeficit_polynomial_certificate hK θ
  set g := controlledPhaseLeastDeficit K θ with hgdef
  have hg0 : 0 < g := controlledPhaseLeastDeficit_pos hK hθ0 hθ
  have hg1 : g ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK θ).2
  set σ : ℤ := if 0 < Real.sin θ then 1 else -1 with hσdef
  have hσ : σ.natAbs = 1 := by by_cases h : 0 < Real.sin θ <;> simp [σ, h]
  obtain ⟨Ψ, hΨbd, hΨ⟩ := hqe (BoundIndex t) 4 12 (56 + 14 * K) (by norm_num) (by omega)
    (epigraphPolynomials t σ) (epigraphPolynomials_totalDegree_le t σ)
    (epigraphPolynomials_bitsize t hK hbox hσ) epigraphFormula
  obtain ⟨hin, hout⟩ := epigraph_boundary hsin hupper hattain
  have hp : Ψ.Holds ![g, Real.cos θ] := (hΨ _).mpr hin
  have hnear : ∀ δ > 0, ∃ q, dist q ![g, Real.cos θ] < δ ∧ ¬ Ψ.Holds q := by
    intro δ hδ
    have hm : 0 < min (δ / 2) (g / 2) := lt_min (by linarith) (by linarith)
    refine ⟨![g - min (δ / 2) (g / 2), Real.cos θ], ?_, fun h => hout _ ?_ ((hΨ _).mp h)⟩
    · rw [dist_pi_lt_iff hδ]
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.dist_eq]
        rw [show g - min (δ / 2) (g / 2) - g = -min (δ / 2) (g / 2) by ring, abs_neg,
          abs_of_pos hm]
        exact (min_le_left _ _).trans_lt (by linarith)
      · simpa using hδ
    · linarith
  obtain ⟨L, hL, A, hA, hQ0, hQzero⟩ := Ψ.exists_atom_zero_of_boundary hp hnear
  obtain ⟨hdeg, hbits⟩ := hΨbd L hL A hA
  set M := 12 ^ (a * (Fintype.card (BoundIndex t) + 1)) with hMdef
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by norm_num)
  set τ' := (56 + 14 * K) * M with hτ'def
  set Hn : ℕ := (M + 1) * 2 ^ M * 2 ^ τ' with hHndef
  set sep : ℝ := Real.exp (-(Cc * (((2 * M : ℕ) : ℝ) + Real.log (Hn : ℝ)) ^ c)) with hsepdef
  have hzero : bivariateEval (bivariateOfMv A.polynomial) (Real.cos θ) g = 0 := by
    rw [bivariateEval_bivariateOfMv]
    have hfun : (Fin.cons g (fun _ : Fin 1 => Real.cos θ) : Fin 2 → ℝ) = ![g, Real.cos θ] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]
    exact hQzero
  have hheight : BivariateHeightLE (bivariateOfMv A.polynomial) ((2 : ℝ) ^ τ') :=
    bivariateOfMv_heightLE fun m => abs_intCast_le_of_natAbs_lt (hbits m)
  have hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      sep ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
    intro S hS hSdeg hScoeff
    refine htm (2 * M) Hn S hS hSdeg fun i => ?_
    have h := hScoeff i
    have hcast : ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ' = ((Hn : ℤ) : ℝ) := by
      simp [Hn]
    rw [hcast, ← Int.cast_abs] at h
    exact_mod_cast h
  have hcert := bivariate_cosine_gap_lower_bound_of_complex_separation θ
    (bivariateOfMv_ne_zero hQ0) (bivariateOfMv_degreeLE hdeg) (one_le_pow₀ (by norm_num))
    hheight hg0 hg1 hzero (Real.exp_pos _) hseparation
  set τ : ℝ := ((56 + 14 * K : ℕ) : ℝ) with hτdef
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMc : (M : ℝ) ^ c ≤ (M : ℝ) ^ (c + 1) := pow_le_pow_right₀ hMr (Nat.le_succ c)
  have hsepbd : Real.exp (-(Cc * (4 + τ) ^ c * (M : ℝ) ^ (c + 1))) ≤ sep := by
    refine le_trans ?_ (explicit_separation_level (M := M) (τ := 56 + 14 * K) (c := c) hCc)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMc (by positivity)) hCc.le
  have hH : (2 : ℝ) ^ τ' ≤ Real.exp (τ * M) := by
    have := two_pow_nat_le_exp τ'
    rw [hτ'def] at this ⊢
    rw [hτdef]
    push_cast at this ⊢
    exact this
  have harith := explicit_gap_arith hM (Nat.le_add_left 1 c) (by positivity) hτ0 hsepbd
    (by positivity) hH
  have hcard : Fintype.card (BoundIndex t) ≤ 1 + 82 * K ^ 2 := by
    rw [Fintype.card_sum, Fintype.card_unit, card_physicalCoordinateIndex]
    omega
  have hexp := explicit_exponent_le hCc a (c + 1) hK hcard
  have h4τ : (1 : ℝ) ≤ 4 + τ := by linarith
  have hA : Cc * (4 + τ) ^ c + 4 + τ ≤ (Cc + 1) * (4 + τ) ^ (c + 1) := by
    have hpow : (4 + τ) ^ c ≤ (4 + τ) ^ (c + 1) := pow_le_pow_right₀ h4τ (Nat.le_succ c)
    have hone : 4 + τ ≤ (4 + τ) ^ (c + 1) := by
      simpa using pow_le_pow_right₀ h4τ (Nat.le_add_left 1 c)
    nlinarith [mul_le_mul_of_nonneg_left hpow hCc.le]
  calc Real.exp (-Real.exp ((Real.log (Cc + 1) + 6 * (c + 1 : ℕ) + 252 * a * (c + 1 : ℕ)) *
        (K : ℝ) ^ 2))
      ≤ Real.exp (-((Cc * (4 + τ) ^ c + 4 + τ) * (M : ℝ) ^ (c + 1))) := by
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        refine le_trans ?_ hexp
        have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ (c + 1) := by positivity
        have : (M : ℝ) ^ (c + 1) =
            ((12 ^ (a * (Fintype.card (BoundIndex t) + 1)) : ℕ) : ℝ) ^ (c + 1) := by
          rw [hMdef]
        calc (Cc * (4 + τ) ^ c + 4 + τ) * (M : ℝ) ^ (c + 1)
            ≤ (Cc + 1) * (4 + τ) ^ (c + 1) * (M : ℝ) ^ (c + 1) :=
              mul_le_mul_of_nonneg_right hA hM3
          _ = _ := by rw [this, hτdef]
    _ ≤ _ := harith
    _ ≤ g := hcert

/-- Theorem E for the named gate `C₁ = diag(1,1,1,e^i)`. -/
theorem exists_explicit_controlledPhase_one_lower_bound
    (hQE : BasuPollackRoyExistentialElimination)
    (hTM : PolynomialTypeTranscendenceMeasureExpAngle) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K 1 :=
  exists_explicit_controlledPhaseLeastDeficit_lower_bound hQE hTM one_ne_zero isAlgebraic_one

/-- **Theorem E, protocol form.** Every pure protocol of footprint at most `K ≥ 1`
implementing the controlled phase with Choi infidelity (score deficit) at most `ε`,
and every common-map mixed protocol, has `ε ≥ exp(-exp(C_E K²))`; with free
standard-Borel classical messages and quantum footprint `Kq ≥ 1`,
`ε ≥ exp(-exp(256 C_E Kq¹⁰))`. -/
theorem exists_explicit_controlledPhase_protocol_bound
    (hQE : BasuPollackRoyExistentialElimination)
    (hTM : PolynomialTypeTranscendenceMeasureExpAngle)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ CE : ℝ, 0 < CE ∧
      (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
        Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε))) := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhaseLeastDeficit_lower_bound hQE hTM hθ0 hθ
  refine ⟨CE, hCE, fun P K ε hK hP hs => (hbound K hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) =
      Real.exp (-Real.exp (CE * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2)) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := θ) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (hbound _ h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (hbound _ h64).trans (hmixed n m hK hs)⟩

/-- **Theorem E, iterated-logarithm form.** For `0 < ε < 1/e`, a charged
footprint `K ≥ 1` reaching least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln(1/ε) - b`. -/
theorem exists_explicit_controlledPhase_iterated_log_bound
    (hQE : BasuPollackRoyExistentialElimination)
    (hTM : PolynomialTypeTranscendenceMeasureExpAngle)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (K : ℕ) (ε : ℝ), 1 ≤ K → 0 < ε → ε < Real.exp (-1) →
      controlledPhaseLeastDeficit K θ ≤ ε →
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 K := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhaseLeastDeficit_lower_bound hQE hTM hθ0 hθ
  refine ⟨max 0 ((1 / 2 : ℝ) * Real.logb 2 CE), le_max_left _ _, ?_⟩
  intro K ε hK hε hεe hle
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := (hbound K hK).trans hle
  have hL1 : 1 < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-1)) := Real.log_lt_log hε hεe
      _ = -1 := Real.log_exp _
  have hlog : Real.log (1 / ε) ≤ Real.exp (CE * (K : ℝ) ^ 2) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hloglog : Real.log (Real.log (1 / ε)) ≤ CE * (K : ℝ) ^ 2 := by
    have := Real.log_le_log (by linarith) hlog
    rwa [Real.log_exp] at this
  have hll0 : 0 < Real.log (Real.log (1 / ε)) := Real.log_pos hL1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hll0 hloglog
  rw [Real.logb_mul hCE.ne' (by positivity), Real.logb_pow] at hb
  have : (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) -
      (1 / 2 : ℝ) * Real.logb 2 CE ≤ Real.logb 2 K := by
    push_cast at hb
    linarith
  linarith [le_max_right 0 ((1 / 2 : ℝ) * Real.logb 2 CE)]

/-- Two logarithms of a doubly exponential lower bound `ε ≥ exp(-exp(C xᵖ))`. -/
theorem logb_iterated_log_le_of_double_exp {C x ε : ℝ} {p : ℕ} (hC : 0 < C) (hx : 0 < x)
    (hp : 0 < p) (hε : 0 < ε) (hεe : ε < Real.exp (-1))
    (h : Real.exp (-Real.exp (C * x ^ p)) ≤ ε) :
    (1 / p : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - (1 / p : ℝ) * Real.logb 2 C ≤
      Real.logb 2 x := by
  have hL1 : 1 < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-1)) := Real.log_lt_log hε hεe
      _ = -1 := Real.log_exp _
  have hlog : Real.log (1 / ε) ≤ Real.exp (C * x ^ p) := by
    have := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hloglog : Real.log (Real.log (1 / ε)) ≤ C * x ^ p := by
    have := Real.log_le_log (by linarith) hlog
    rwa [Real.log_exp] at this
  have hll0 : 0 < Real.log (Real.log (1 / ε)) := Real.log_pos hL1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hll0 hloglog
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_pow] at hb
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have : Real.logb 2 (Real.log (Real.log (1 / ε))) - Real.logb 2 C ≤ p * Real.logb 2 x := by
    linarith
  calc (1 / p : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - (1 / p : ℝ) * Real.logb 2 C
      = (1 / p : ℝ) * (Real.logb 2 (Real.log (Real.log (1 / ε))) - Real.logb 2 C) := by ring
    _ ≤ (1 / p : ℝ) * (p * Real.logb 2 x) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.logb 2 x := by field_simp

/-- **Theorem E, quantum-footprint iterated-logarithm form.** With free
standard-Borel classical messages, for `0 < ε < 1/e`, every pure or common-map
mixed protocol of quantum footprint `Kq ≥ 1` and score deficit at most `ε`
satisfies `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - b`. In LOSCC `Kq` is the
Schmidt number of the resource. -/
theorem exists_explicit_controlledPhase_quantum_iterated_log_bound
    (hQE : BasuPollackRoyExistentialElimination)
    (hTM : PolynomialTypeTranscendenceMeasureExpAngle)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq → 0 < ε → ε < Real.exp (-1) →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel.toLinearMap →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 Kq) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 Kq)) := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhaseLeastDeficit_lower_bound hQE hTM hθ0 hθ
  refine ⟨max 0 ((1 / 10 : ℝ) * Real.logb 2 (256 * CE)), le_max_left _ _, ?_⟩
  intro ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Kq ε hKq hε hεe
  have hKr : (0 : ℝ) < Kq := by exact_mod_cast hKq
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (CE * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2)) =
      Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) := by
    push_cast; ring_nf
  have key (hd : controlledPhaseLeastDeficit (16 * Kq ^ 5) θ ≤ ε) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) -
        max 0 ((1 / 10 : ℝ) * Real.logb 2 (256 * CE)) ≤ Real.logb 2 Kq := by
    have h := (hbound _ h64).trans hd
    rw [hexp] at h
    have := logb_iterated_log_le_of_double_exp (p := 10) (by positivity) hKr (by norm_num)
      hε hεe h
    push_cast at this
    linarith [le_max_right 0 ((1 / 10 : ℝ) * Real.logb 2 (256 * CE))]
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := θ) (ε := ε) hKq
  exact ⟨fun hK hs => key (hpure hK hs), fun n m hK hs => key (hmixed n m hK hs)⟩

end NLQCLean
