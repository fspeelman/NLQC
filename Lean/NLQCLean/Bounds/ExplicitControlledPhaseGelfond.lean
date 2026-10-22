import NLQCLean.Bounds.ExplicitControlledPhase
import NLQCLean.Arithmetic.GelfondMeasure

/-!
# The effective bound for `C₁` with the Gelfond measure for `e^i`

The polynomial-type measure `|P(e^i)| ≥ 2^{-N B (200 B^{31} + 1)}`
(`Gelfond.norm_eval_exp_I_ge`, proved by Gelfond's method) is used in the separation step
`gap_ge_of_separation`. A root `(g, cos 1)` of a nonzero integer polynomial of degree at most
`M` with coefficients below `2^τ` then gives `g ≥ exp(-202 (6M + τ + 128)^{33})`. With the
deformation eliminant and its sharp size bounds
(`exists_controlledPhase_certificate_eliminant_sharp`: `k ≤ 82 K²` coordinates, degree and
bit size `25^k · poly(k, K)`), `g_K(1) ≥ exp(-exp(9400 K²))`
(`controlledPhase_one_lower_bound`). The constant is `33 · 82 · 3.23 ≈ 8740` from the
measure exponent `33`, the coordinate count and `ln 25 < 3.23`, plus lower-order terms.

The forms with an unspecified constant (`exists_explicit_controlledPhase_one_*`) follow.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial ExplicitGate ClassicalCommunication

/-- The gap step: if `(g, cos 1)` is a root of a nonzero integer polynomial of degree at most
`M` with coefficients below `2^τ'`, and nonconstant integer polynomials of degree at most `2M`
and height at most `(M+1) 2^M 2^τ'` are at least `exp(-W)` at `e^i`, with `4M + τ' ≤ W`, then
`g ≥ exp(-2W)`. -/
theorem gap_ge_of_separation {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    {A : MvPolynomial (Fin 2) ℤ} (hA0 : A ≠ 0) {M τ' : ℕ}
    (hdeg : A.totalDegree ≤ M) (hbits : ∀ m, (A.coeff m).natAbs < 2 ^ τ')
    (hQzero : eval₂ (Int.castRingHom ℝ) ![g, Real.cos 1] A = 0) {W : ℝ}
    (hsmall : ((4 * M + τ' : ℕ) : ℝ) ≤ W)
    (hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      Real.exp (-W) ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖) :
    Real.exp (-(2 * W)) ≤ g := by
  have hzero : bivariateEval (bivariateOfMv A) (Real.cos 1) g = 0 := by
    rw [bivariateEval_bivariateOfMv]
    have hfun : (Fin.cons g (fun _ : Fin 1 => Real.cos 1) : Fin 2 → ℝ) = ![g, Real.cos 1] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]
    exact hQzero
  have hheight : BivariateHeightLE (bivariateOfMv A) ((2 : ℝ) ^ τ') :=
    bivariateOfMv_heightLE fun m => abs_intCast_le_of_natAbs_lt (hbits m)
  have hcert := bivariate_cosine_gap_lower_bound_of_complex_separation 1
    (bivariateOfMv_ne_zero hA0) (bivariateOfMv_degreeLE hdeg) (one_le_pow₀ (by norm_num))
    hheight hg0 hg1 hzero (Real.exp_pos _) hseparation
  have hW0 : (0 : ℝ) ≤ W := le_trans (Nat.cast_nonneg _) hsmall
  have hgap : Real.exp (-(2 * W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) /
      ((M + 1 : ℕ) ^ 3 * (2 : ℝ) ^ τ') := by
    have h2M : (2 : ℝ) ^ M ≤ Real.exp M := two_pow_nat_le_exp M
    have h2τ : (2 : ℝ) ^ τ' ≤ Real.exp τ' := two_pow_nat_le_exp τ'
    have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp M := natCast_succ_le_exp M
    have hmin : Real.exp (-((M : ℝ) + W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) := by
      apply le_min
      · rw [Real.exp_le_one_iff]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      · rw [show -((M : ℝ) + W) = -(M : ℝ) + -W by ring, Real.exp_add, Real.exp_neg]
        exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr h2M)
          (Real.exp_pos _).le
    have hden : ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ' ≤ Real.exp (3 * M + τ') := by
      rw [Real.exp_add, show (3 : ℝ) * M = M + M + M by ring, Real.exp_add, Real.exp_add]
      calc ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ'
          ≤ Real.exp M ^ 3 * Real.exp τ' := mul_le_mul (pow_le_pow_left₀ (by positivity) hM1 3)
            h2τ (by positivity) (by positivity)
        _ = _ := by ring
    have hdenpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ' := by positivity
    rw [le_div_iff₀ hdenpos]
    calc Real.exp (-(2 * W)) * (((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ')
        ≤ Real.exp (-(2 * W)) * Real.exp (3 * M + τ') :=
          mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-(2 * W) + (3 * M + τ')) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-((M : ℝ) + W)) := by
          apply Real.exp_le_exp.mpr
          have := hsmall; push_cast at this; linarith
      _ ≤ _ := hmin
  exact hgap.trans hcert

theorem pow_2718_le_exp (n : ℕ) : (2.718 : ℝ) ^ n ≤ Real.exp n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n

/-- The separation step with the Gelfond measure: a root `(g, cos 1)` of a nonzero integer
polynomial of degree at most `M` with coefficients below `2^τ'` forces
`g ≥ exp(-202 B^{33})`, `B = 6M + τ' + 128`. -/
theorem gap_ge_of_cos_one_eliminant_gelfond {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    {A : MvPolynomial (Fin 2) ℤ} (hA0 : A ≠ 0) {M τ' : ℕ} (hM : 1 ≤ M)
    (hdeg : A.totalDegree ≤ M) (hbits : ∀ m, (A.coeff m).natAbs < 2 ^ τ')
    (hQzero : eval₂ (Int.castRingHom ℝ) ![g, Real.cos 1] A = 0) :
    Real.exp (-(202 * ((6 * M + τ' + 128 : ℕ) : ℝ) ^ 33)) ≤ g := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = 6 * M + τ' + 128 := ⟨_, rfl⟩
  rw [← hBdef]
  obtain ⟨KB, hKB⟩ : ∃ KB, KB = B * (200 * B ^ 31 + 1) := ⟨_, rfl⟩
  have hB : 128 ≤ B := by omega
  have hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      Real.exp (-((2 * M * KB : ℕ) : ℝ)) ≤
        ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖ := by
    intro S hS hSdeg hScoeff
    have hS0 : S ≠ 0 := by rintro rfl; simp at hS
    have hHB : (2 : ℝ) ^ (2 * M) * ((((2 * M : ℕ) : ℝ) + 1) *
        (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ')) ≤ 2 ^ B := by
      have hnat : 2 ^ (2 * M) * ((2 * M + 1) * ((M + 1) * 2 ^ M * 2 ^ τ')) ≤ 2 ^ B := by
        have h1 : 2 * M + 1 ≤ 2 ^ (2 * M) := Nat.lt_two_pow_self
        have h2 : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
        calc 2 ^ (2 * M) * ((2 * M + 1) * ((M + 1) * 2 ^ M * 2 ^ τ'))
            ≤ 2 ^ (2 * M) * (2 ^ (2 * M) * (2 ^ M * 2 ^ M * 2 ^ τ')) := by gcongr
          _ = 2 ^ (2 * M + (2 * M + (M + M + τ'))) := by simp only [pow_add]
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast hnat
    have h := Gelfond.norm_eval_exp_I_ge hS0 hB hSdeg (by omega) hScoeff hHB
    rw [← hKB] at h
    have hζ : Complex.exp (((1 : ℝ) : ℂ) * Complex.I) = Complex.exp Complex.I := by simp
    rw [hζ]
    refine le_trans ?_ h
    have h2 := two_pow_nat_le_exp (2 * M * KB)
    rw [one_div, inv_pow, Real.exp_neg]
    exact inv_anti₀ (by positivity) h2
  have hsmall : ((4 * M + τ' : ℕ) : ℝ) ≤ ((2 * M * KB : ℕ) : ℝ) := by
    have h1 : B ≤ KB := hKB ▸ Nat.le_mul_of_pos_right _ (by positivity)
    have h2 : KB ≤ 2 * M * KB := Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast (show 4 * M + τ' ≤ B by omega).trans (h1.trans h2)
  have hgap := gap_ge_of_separation hg0 hg1 hA0 hdeg hbits hQzero hsmall hseparation
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  have hnat : 2 * (2 * M * KB) ≤ 202 * B ^ 33 := by
    have h4M : 4 * M ≤ B := by omega
    have hB31 : 200 * B ^ 31 + 1 ≤ 201 * B ^ 31 := by
      have := Nat.one_le_pow 31 B (by omega)
      omega
    calc 2 * (2 * M * KB) = (4 * M) * B * (200 * B ^ 31 + 1) := by rw [hKB]; ring
      _ ≤ B * B * (201 * B ^ 31) := by gcongr
      _ = 201 * B ^ 33 := by ring
      _ ≤ 202 * B ^ 33 := by gcongr; norm_num
  exact_mod_cast hnat

/-! ### The double-exponential bound with explicit constant -/

/-- Size of the Gelfond level for the sharp eliminant: with `k ≤ 82 K²` coordinates,
`6 d_Nrm(k) + sharpExp k (56 + 14K) + 129 ≤ 26 · 2²¹ · K⁴ · 25^k`. -/
theorem sharp_level_le {K k : ℕ} (hK : 1 ≤ K) (hk : k ≤ 82 * K ^ 2) :
    6 * Deformation.dNrm k + (Deformation.sharpExp k (56 + 14 * K) + 1) + 128 ≤
      26 * 2 ^ 21 * K ^ 4 * 25 ^ k := by
  unfold Deformation.dNrm Deformation.dPhi Deformation.sharpExp Deformation.NB Deformation.DB
  obtain ⟨N, hN⟩ : ∃ N, N = 25 ^ k := ⟨_, rfl⟩
  rw [← hN]
  have hN1 : 1 ≤ N := hN ▸ Nat.one_le_pow _ _ (by norm_num)
  have hK2 : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
  have hK4 : K ^ 4 = K ^ 2 * K ^ 2 := by ring
  have hKK : K ≤ K ^ 2 := by nlinarith
  -- the bracket `Q` with `LHS ≤ 26 N Q`
  have hQ : 789 + 586 * k + (26 + 24 * k) * (2 * k + 470 + 56 * K) ≤ 2 ^ 21 * K ^ 4 := by
    have h1 : 26 + 24 * k ≤ 1994 * K ^ 2 := by omega
    have h2 : 2 * k + 470 + 56 * K ≤ 690 * K ^ 2 := by omega
    have h3 : (26 + 24 * k) * (2 * k + 470 + 56 * K) ≤ 1994 * K ^ 2 * (690 * K ^ 2) :=
      Nat.mul_le_mul h1 h2
    have h4 : 789 + 586 * k ≤ 48841 * K ^ 2 * K ^ 2 := by nlinarith
    rw [hK4]; nlinarith
  calc 6 * (4 * (26 * N * (26 + 24 * k)) + 2) +
        (12 + 26 * N * (10 * k + 12 + (26 + 24 * k) * (2 * k + 246 + 4 * (56 + 14 * K))) + 1) +
        128
      ≤ 26 * N * (789 + 586 * k + (26 + 24 * k) * (2 * k + 470 + 56 * K)) := by
        have h : 2 * k + 246 + 4 * (56 + 14 * K) = 2 * k + 470 + 56 * K := by ring
        rw [h]; nlinarith
    _ ≤ 26 * N * (2 ^ 21 * K ^ 4) := Nat.mul_le_mul_left _ hQ
    _ = 26 * 2 ^ 21 * K ^ 4 * N := by ring

theorem twentyfive_le_exp : (25 : ℝ) ≤ Real.exp 3.23 := by
  have h3 : (2.718 : ℝ) ^ 3 ≤ Real.exp 3 := by exact_mod_cast pow_2718_le_exp 3
  have h023 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.23 by norm_num)
  have : Real.exp 3.23 = Real.exp 3 * Real.exp 0.23 := by rw [← Real.exp_add]; norm_num
  rw [this]
  calc (25 : ℝ) ≤ 2.718 ^ 3 * (1 + 0.23 + 0.23 ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 3 * Real.exp 0.23 := by gcongr

/-- `202 B³³ ≤ exp(9400 K²)` for the Gelfond level `B` of the sharp eliminant. -/
theorem sharp_tower_le {K k : ℕ} (hK : 1 ≤ K) (hk : k ≤ 82 * K ^ 2) :
    202 * ((6 * Deformation.dNrm k + (Deformation.sharpExp k (56 + 14 * K) + 1) + 128 : ℕ) :
      ℝ) ^ 33 ≤ Real.exp (9400 * (K : ℝ) ^ 2) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkr : (k : ℝ) ≤ 82 * (K : ℝ) ^ 2 := by exact_mod_cast hk
  have hB : ((6 * Deformation.dNrm k + (Deformation.sharpExp k (56 + 14 * K) + 1) + 128 : ℕ) :
      ℝ) ≤ Real.exp (14 + 4 * K + 264.86 * (K : ℝ) ^ 2) := by
    have hnat := sharp_level_le hK hk
    have hcast : ((6 * Deformation.dNrm k + (Deformation.sharpExp k (56 + 14 * K) + 1) + 128 : ℕ)
        : ℝ) ≤ 26 * 2 ^ 21 * (K : ℝ) ^ 4 * 25 ^ k := by exact_mod_cast hnat
    have h18 : (26 * 2 ^ 21 : ℝ) ≤ Real.exp 18 := by
      have := pow_2718_le_exp 18; norm_num at this ⊢; linarith
    have hKe : (K : ℝ) ≤ Real.exp (K - 1) := by linarith [Real.add_one_le_exp ((K : ℝ) - 1)]
    have hK4 : (K : ℝ) ^ 4 ≤ Real.exp (4 * K - 4) := by
      calc (K : ℝ) ^ 4 ≤ Real.exp (K - 1) ^ 4 := by gcongr
        _ = Real.exp (4 * K - 4) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h25 : (25 : ℝ) ^ k ≤ Real.exp (264.86 * (K : ℝ) ^ 2) := by
      calc (25 : ℝ) ^ k ≤ Real.exp 3.23 ^ k := by gcongr; exact twentyfive_le_exp
        _ = Real.exp (3.23 * k) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (264.86 * (K : ℝ) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    calc _ ≤ 26 * 2 ^ 21 * (K : ℝ) ^ 4 * 25 ^ k := hcast
      _ ≤ Real.exp 18 * Real.exp (4 * K - 4) * Real.exp (264.86 * (K : ℝ) ^ 2) := by
          gcongr
      _ = Real.exp (14 + 4 * K + 264.86 * (K : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h202 : (202 : ℝ) ≤ Real.exp 6 := by
    have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
  calc 202 * ((6 * Deformation.dNrm k + (Deformation.sharpExp k (56 + 14 * K) + 1) + 128 : ℕ) :
        ℝ) ^ 33
      ≤ Real.exp 6 * Real.exp (14 + 4 * K + 264.86 * (K : ℝ) ^ 2) ^ 33 := by gcongr
    _ = Real.exp (468 + 132 * K + 8740.38 * (K : ℝ) ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (9400 * (K : ℝ) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

/-- **Theorem E for `C₁` with explicit constant.** For every footprint `K ≥ 1`,
`g_K(1) ≥ exp(-exp(9400 K²))`. -/
theorem controlledPhase_one_lower_bound {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-Real.exp (9400 * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K 1 := by
  obtain ⟨t, -, hcount, hCdeg, hSdeg, hCm, hSm, hupper, hattain⟩ :=
    exists_controlledPhaseLeastDeficit_polynomial_certificate hK 1
  set g := controlledPhaseLeastDeficit K 1 with hgdef
  have hg0 : 0 < g := controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : g ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  obtain ⟨A, hA0, hdeg, hbits, hzero⟩ := exists_controlledPhase_certificate_eliminant_sharp hK 1 g
    t hg0 hg1 hCdeg hSdeg hCm hSm hupper hattain
  have hM : 1 ≤ Deformation.dNrm (physicalRawRealCoordinateCount 2 t) := by
    unfold Deformation.dNrm; omega
  have hgap := gap_ge_of_cos_one_eliminant_gelfond hg0 hg1 hA0 hM hdeg hbits hzero
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  exact sharp_tower_le hK hcount

/-- **Theorem E for `C₁`, protocol form, explicit constant.** Every pure or common-map mixed
protocol of footprint `K ≥ 1` implementing `C₁` with score deficit at most `ε` has
`ε ≥ exp(-exp(9400 K²))`; with free standard-Borel classical messages and quantum footprint
`Kq ≥ 1`, `ε ≥ exp(-exp(2406400 Kq¹⁰))`. -/
theorem controlledPhase_one_protocol_bound :
    (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
        Real.exp (-Real.exp (9400 * (K : ℝ) ^ 2)) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (2406400 * (Kq : ℝ) ^ 10)) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (2406400 * (Kq : ℝ) ^ 10)) ≤ ε))) := by
  refine ⟨fun P K ε hK hP hs => (controlledPhase_one_lower_bound hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (2406400 * (Kq : ℝ) ^ 10)) =
      Real.exp (-Real.exp (9400 * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2)) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := 1) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (controlledPhase_one_lower_bound h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (controlledPhase_one_lower_bound h64).trans (hmixed n m hK hs)⟩

/-- **Theorem E for `C₁`, iterated-logarithm form, explicit constant.** For `0 < ε < 1/e`, a
charged footprint `K ≥ 1` with least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln(1/ε) - ½ log₂ 9400`. -/
theorem controlledPhase_one_iterated_log_bound (K : ℕ) (ε : ℝ) (hK : 1 ≤ K) (hε : 0 < ε)
    (hεe : ε < Real.exp (-1)) (hle : controlledPhaseLeastDeficit K 1 ≤ ε) :
    (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) -
      (1 / 2 : ℝ) * Real.logb 2 9400 ≤ Real.logb 2 K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := (controlledPhase_one_lower_bound hK).trans hle
  have hL1 : 1 < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-1)) := Real.log_lt_log hε hεe
      _ = -1 := Real.log_exp _
  have hlog : Real.log (1 / ε) ≤ Real.exp (9400 * (K : ℝ) ^ 2) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hloglog : Real.log (Real.log (1 / ε)) ≤ 9400 * (K : ℝ) ^ 2 := by
    have := Real.log_le_log (by linarith) hlog
    rwa [Real.log_exp] at this
  have hll0 : 0 < Real.log (Real.log (1 / ε)) := Real.log_pos hL1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hll0 hloglog
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at hb
  push_cast at hb
  linarith

/-! ### Existential-constant forms

The statements with an unspecified constant, as consequences of the explicit theorems above
(`C = 9400`, free-classical constant `256 · 9400 = 2406400`, offset `b = ½ log₂ 9400`). -/

set_option maxHeartbeats 1000000 in
/-- The eliminant of the epigraph of `g_K(1)` (`exists_controlledPhase_certificate_eliminant`,
with `a = 4`): the point `(g_K(1), cos 1)` is
a zero of a nonzero integer polynomial of degree at most `M ≤ exp(252 a K²)` with coefficients
below `2^{(56 + 14K) M}`. -/
theorem exists_controlledPhase_one_eliminant :
    ∃ a : ℕ, ∀ K : ℕ, 1 ≤ K → ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ Real.exp (252 * a * (K : ℝ) ^ 2) ∧
      ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧ A.totalDegree ≤ M ∧
        (∀ m, (A.coeff m).natAbs < 2 ^ ((56 + 14 * K) * M)) ∧
        eval₂ (Int.castRingHom ℝ) ![controlledPhaseLeastDeficit K 1, Real.cos 1] A = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 4 := ⟨4, rfl⟩
  refine ⟨a, fun K hK => ?_⟩
  obtain ⟨t, hbox, hcount, hCdeg, hSdeg, hCm, hSm, hupper, hattain⟩ :=
    exists_controlledPhaseLeastDeficit_polynomial_certificate hK 1
  set g := controlledPhaseLeastDeficit K 1 with hgdef
  have hg0 : 0 < g := controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : g ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  obtain ⟨A, hQ0, hdeg, hbits, hQzero⟩ := exists_controlledPhase_certificate_eliminant hK 1 g t
    hg0 hg1 hCdeg hSdeg hCm hSm hupper hattain
  rw [← ha] at hdeg hbits
  set M := 12 ^ (a * (Fintype.card (BoundIndex t) + 1)) with hMdef
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by norm_num)
  have hMexp : (M : ℝ) ≤ Real.exp (252 * a * (K : ℝ) ^ 2) := by
    have hcard : Fintype.card (BoundIndex t) ≤ 1 + 82 * K ^ 2 := by
      rw [Fintype.card_sum, Fintype.card_unit, card_physicalCoordinateIndex]
      omega
    have h12 := twelve_pow_le_exp (a * (Fintype.card (BoundIndex t) + 1))
    have hMcast : (M : ℝ) = (12 : ℝ) ^ (a * (Fintype.card (BoundIndex t) + 1)) := by
      rw [hMdef]; push_cast; ring
    rw [hMcast]
    push_cast at h12
    refine h12.trans (Real.exp_le_exp.mpr ?_)
    have hc : ((Fintype.card (BoundIndex t) : ℕ) : ℝ) ≤ 1 + 82 * (K : ℝ) ^ 2 := by
      exact_mod_cast hcard
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hK2 ha]
  exact ⟨M, hM, hMexp, A, hQ0, hdeg, hbits, hQzero⟩

/-- **Theorem E for `C₁`.** There is `C > 0` with `exp(-exp(C K²)) ≤ g_K(1)` for every
footprint `K ≥ 1`; `controlledPhase_one_lower_bound` gives `C = 9400`. -/
theorem exists_explicit_controlledPhase_one_lower_bound :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K 1 :=
  ⟨9400, by norm_num, fun _ hK => controlledPhase_one_lower_bound hK⟩

/-- **Theorem E for `C₁`, protocol form.**
Every pure or common-map mixed protocol of footprint `K ≥ 1` implementing `C₁` with score
deficit at most `ε` has `ε ≥ exp(-exp(C K²))`; with free standard-Borel classical messages and
quantum footprint `Kq ≥ 1`, `ε ≥ exp(-exp(256 C Kq¹⁰))`. `controlledPhase_one_protocol_bound`
is the form with `C = 9400`. -/
theorem exists_explicit_controlledPhase_one_protocol_bound :
    ∃ CE : ℝ, 0 < CE ∧
      (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
        Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε))) := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_lower_bound
  refine ⟨CE, hCE, fun P K ε hK hP hs => (hbound K hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) =
      Real.exp (-Real.exp (CE * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2)) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := 1) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (hbound _ h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (hbound _ h64).trans (hmixed n m hK hs)⟩

/-- **Theorem E for `C₁`, iterated-logarithm form.** For
`0 < ε < 1/e`, a charged footprint `K ≥ 1` with least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln(1/ε) - b`; `controlledPhase_one_iterated_log_bound` gives
`b = ½ log₂ 9400`. -/
theorem exists_explicit_controlledPhase_one_iterated_log_bound :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (K : ℕ) (ε : ℝ), 1 ≤ K → 0 < ε → ε < Real.exp (-1) →
      controlledPhaseLeastDeficit K 1 ≤ ε →
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 K :=
  ⟨(1 / 2 : ℝ) * Real.logb 2 9400,
    mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) (by norm_num)),
    controlledPhase_one_iterated_log_bound⟩

end NLQCLean
