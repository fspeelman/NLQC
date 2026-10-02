import NLQCLean.Bounds.ExplicitControlledPhase
import NLQCLean.Arithmetic.ExpITranscendence

/-!
# The effective bound for `C₁` with quantifier elimination as the only input

The hypothesis-free transcendence measure for `e^i`
(`ExpITranscendence.normSq_aeval_exp_I_ge`) replaces the polynomial-type measure. It is
weaker, `|S(e^i)| ≥ Z^{-Z^{2N+9}}/…` with `Z` polynomial in the degree and height, so the
bound acquires one more exponential:

`g_K(1) ≥ exp(-exp(exp(C K²)))`, assuming only `BasuPollackRoyExistentialElimination`.

The two-input theorem `exists_explicit_controlledPhase_one_lower_bound` (with the weak E-TM)
keeps the double-exponential bound.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial ExplicitGate ClassicalCommunication

/-- The separation at the named angle `1` from the hypothesis-free measure: for a nonconstant
integer polynomial of degree at most `2M` and height at most `Hn`,
`‖S(e^i)‖ ≥ exp(-W)` with `W = Z^{4M+10}`, `Z = measureZ (2M) Hn`. -/
theorem exp_neg_le_norm_eval_exp_I {M Hn : ℕ} (hM : 1 ≤ M) (S : Polynomial ℤ)
    (hS : 0 < S.natDegree) (hSdeg : S.natDegree ≤ 2 * M) (hScoeff : ∀ i, |S.coeff i| ≤ Hn) :
    Real.exp (-((ExpITranscendence.measureZ (2 * M) Hn : ℝ) ^ (4 * M + 10))) ≤
      ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖ := by
  set Z := ExpITranscendence.measureZ (2 * M) Hn with hZ
  have hS0 : S ≠ 0 := by rintro rfl; simp at hS
  have hmeas := ExpITranscendence.normSq_aeval_exp_I_ge hS0 (N := 2 * M) (by omega) hSdeg hScoeff
  rw [← hZ, show 2 * (2 * M) + 9 = 4 * M + 9 by ring] at hmeas
  have hZ1 : (1 : ℝ) ≤ Z := by
    have : 1 ≤ Z := Nat.one_le_iff_ne_zero.mpr (by rw [hZ, ExpITranscendence.measureZ]; positivity)
    exact_mod_cast this
  have hZpos : (0 : ℝ) < Z := by linarith
  -- `Z^{-Z^{4M+9}} ≥ exp(-2 Z^{4M+10})`
  have hlog : Real.log Z ≤ Z := (Real.log_le_sub_one_of_pos hZpos).trans (by linarith)
  have hstep : Real.exp (-(2 * (Z : ℝ) ^ (4 * M + 10))) ≤ 1 / (Z : ℝ) ^ (Z ^ (4 * M + 9)) := by
    rw [show (Z : ℝ) ^ (Z ^ (4 * M + 9)) = Real.exp (((Z ^ (4 * M + 9) : ℕ) : ℝ) * Real.log Z) by
      rw [← Real.log_pow, Real.exp_log (pow_pos hZpos _)], one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    push_cast
    have hE : (0 : ℝ) ≤ (Z : ℝ) ^ (4 * M + 9) := by positivity
    calc (Z : ℝ) ^ (4 * M + 9) * Real.log Z ≤ (Z : ℝ) ^ (4 * M + 9) * Z :=
          mul_le_mul_of_nonneg_left hlog hE
      _ = (Z : ℝ) ^ (4 * M + 10) := by ring
      _ ≤ _ := by have : (0 : ℝ) ≤ (Z : ℝ) ^ (4 * M + 10) := by positivity
                  linarith
  have heval : S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I)) =
      Polynomial.aeval (Complex.exp Complex.I) S := by
    rw [Polynomial.aeval_def, algebraMap_int_eq]; norm_num
  rw [heval, Complex.norm_def]
  calc Real.exp (-((Z : ℝ) ^ (4 * M + 10)))
      = Real.sqrt (Real.exp (-(2 * (Z : ℝ) ^ (4 * M + 10)))) := by
        rw [show Real.exp (-(2 * (Z : ℝ) ^ (4 * M + 10))) = Real.exp (-((Z : ℝ) ^ (4 * M + 10))) ^ 2 by
          rw [sq, ← Real.exp_add]; ring_nf, Real.sqrt_sq (Real.exp_pos _).le]
    _ ≤ _ := Real.sqrt_le_sqrt (hstep.trans hmeas)

/-- `Z = 6(2M+1)²(Hn+1)² ≤ exp(152 K M)` for the explicit height `Hn = (M+1) 2^M 2^{τM}`,
`τ = 56 + 14K`. -/
theorem measureZ_le_exp {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) :
    (ExpITranscendence.measureZ (2 * M)
      ((M + 1) * 2 ^ M * 2 ^ ((56 + 14 * K) * M)) : ℝ) ≤ Real.exp (152 * K * M) := by
  set Hn : ℕ := (M + 1) * 2 ^ M * 2 ^ ((56 + 14 * K) * M) with hHn
  have hHn1 : 1 ≤ Hn := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlog := log_explicit_height_le M (56 + 14 * K)
  have hHnexp : (Hn : ℝ) ≤ Real.exp ((2 + ((56 + 14 * K : ℕ) : ℝ)) * M) := by
    rw [← Real.log_le_iff_le_exp (by exact_mod_cast hHn1)]
    exact hlog
  have hZle : ExpITranscendence.measureZ (2 * M) Hn ≤ 24 * (2 * M + 1) ^ 2 * Hn ^ 2 := by
    rw [ExpITranscendence.measureZ]
    have : (Hn + 1) ^ 2 ≤ 4 * Hn ^ 2 := by nlinarith
    calc 6 * (2 * M + 1) ^ 2 * (Hn + 1) ^ 2 ≤ 6 * (2 * M + 1) ^ 2 * (4 * Hn ^ 2) :=
          Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h24 : (24 : ℝ) ≤ Real.exp 4 := by
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have := Real.exp_one_gt_d9
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 4
    norm_num at this ⊢
    linarith
  have h2M : ((2 * M + 1 : ℕ) : ℝ) ≤ Real.exp (2 * M) := by
    have := Real.add_one_le_exp (2 * (M : ℝ)); push_cast; linarith
  calc (ExpITranscendence.measureZ (2 * M) Hn : ℝ)
      ≤ ((24 * (2 * M + 1) ^ 2 * Hn ^ 2 : ℕ) : ℝ) := by exact_mod_cast hZle
    _ = 24 * ((2 * M + 1 : ℕ) : ℝ) ^ 2 * (Hn : ℝ) ^ 2 := by push_cast; ring
    _ ≤ Real.exp 4 * Real.exp (2 * M) ^ 2 *
          Real.exp ((2 + ((56 + 14 * K : ℕ) : ℝ)) * M) ^ 2 := by
        gcongr
    _ = Real.exp (4 + 4 * M + 2 * ((2 + ((56 + 14 * K : ℕ) : ℝ)) * M)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        push_cast; ring_nf
    _ ≤ Real.exp (152 * K * M) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [mul_le_mul hKr hMr zero_le_one (by linarith : (0 : ℝ) ≤ K)]

set_option maxHeartbeats 1000000 in
/-- Quantifier elimination applied to the epigraph of `g_K(1)`: the point `(g_K(1), cos 1)` is
a zero of a nonzero integer polynomial of degree at most `M ≤ exp(252 a K²)` with coefficients
below `2^{(56 + 14K) M}`. -/
theorem exists_controlledPhase_one_eliminant_of_QE
    (hQE : BasuPollackRoyExistentialElimination) :
    ∃ a : ℕ, ∀ K : ℕ, 1 ≤ K → ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ Real.exp (252 * a * (K : ℝ) ^ 2) ∧
      ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧ A.totalDegree ≤ M ∧
        (∀ m, (A.coeff m).natAbs < 2 ^ ((56 + 14 * K) * M)) ∧
        eval₂ (Int.castRingHom ℝ) ![controlledPhaseLeastDeficit K 1, Real.cos 1] A = 0 := by
  obtain ⟨a, hqe⟩ := hQE
  have hsin := sin_ne_zero_of_isAlgebraic one_ne_zero isAlgebraic_one
  refine ⟨a, fun K hK => ?_⟩
  obtain ⟨t, hbox, hcount, -, -, -, -, hupper, hattain⟩ :=
    exists_controlledPhaseLeastDeficit_polynomial_certificate hK 1
  set g := controlledPhaseLeastDeficit K 1 with hgdef
  have hg0 : 0 < g := controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  set σ : ℤ := if 0 < Real.sin 1 then 1 else -1 with hσdef
  have hσ : σ.natAbs = 1 := by by_cases h : 0 < Real.sin 1 <;> simp [σ, h]
  obtain ⟨Ψ, hΨbd, hΨ⟩ := hqe (BoundIndex t) 4 12 (56 + 14 * K) (by norm_num) (by omega)
    (epigraphPolynomials t σ) (epigraphPolynomials_totalDegree_le t σ)
    (epigraphPolynomials_bitsize t hK hbox hσ) epigraphFormula
  obtain ⟨hin, hout⟩ := epigraph_boundary hsin hupper hattain
  have hp : Ψ.Holds ![g, Real.cos 1] := (hΨ _).mpr hin
  have hnear : ∀ δ > 0, ∃ q, dist q ![g, Real.cos 1] < δ ∧ ¬ Ψ.Holds q := by
    intro δ hδ
    have hm : 0 < min (δ / 2) (g / 2) := lt_min (by linarith) (by linarith)
    refine ⟨![g - min (δ / 2) (g / 2), Real.cos 1], ?_, fun h => hout _ ?_ ((hΨ _).mp h)⟩
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
  exact ⟨M, hM, hMexp, A.polynomial, hQ0, hdeg, hbits, hQzero⟩

/-- **Theorem E for `C₁` with quantifier elimination as the only input.** Using the
hypothesis-free transcendence measure for `e^i`, there is `C > 0` with
`exp(-exp(exp(C K²))) ≤ g_K(1)` for every footprint `K ≥ 1`. -/
theorem exists_explicit_controlledPhase_one_lower_bound_of_QE
    (hQE : BasuPollackRoyExistentialElimination) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (Real.exp (CE * (K : ℝ) ^ 2))) ≤ controlledPhaseLeastDeficit K 1 := by
  obtain ⟨a, helim⟩ := exists_controlledPhase_one_eliminant_of_QE hQE
  refine ⟨504 * a + 9, by positivity, fun K hK => ?_⟩
  obtain ⟨M, hM, hMexp, A, hQ0, hdeg, hbits, hQzero⟩ := helim K hK
  set g := controlledPhaseLeastDeficit K 1 with hgdef
  have hg0 : 0 < g := controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : g ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  set τ' := (56 + 14 * K) * M with hτ'def
  set Hn : ℕ := (M + 1) * 2 ^ M * 2 ^ τ' with hHndef
  set Zn := ExpITranscendence.measureZ (2 * M) Hn with hZndef
  set W : ℝ := (Zn : ℝ) ^ (4 * M + 10) with hWdef
  have hzero : bivariateEval (bivariateOfMv A) (Real.cos 1) g = 0 := by
    rw [bivariateEval_bivariateOfMv]
    have hfun : (Fin.cons g (fun _ : Fin 1 => Real.cos 1) : Fin 2 → ℝ) = ![g, Real.cos 1] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]
    exact hQzero
  have hheight : BivariateHeightLE (bivariateOfMv A) ((2 : ℝ) ^ τ') :=
    bivariateOfMv_heightLE fun m => abs_intCast_le_of_natAbs_lt (hbits m)
  have hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      Real.exp (-W) ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖ := by
    intro S hS hSdeg hScoeff
    refine exp_neg_le_norm_eval_exp_I hM S hS hSdeg fun i => ?_
    have h := hScoeff i
    have hcast : ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ' = ((Hn : ℤ) : ℝ) := by
      simp [Hn]
    rw [hcast, ← Int.cast_abs] at h
    exact_mod_cast h
  have hcert := bivariate_cosine_gap_lower_bound_of_complex_separation 1
    (bivariateOfMv_ne_zero hQ0) (bivariateOfMv_degreeLE hdeg) (one_le_pow₀ (by norm_num))
    hheight hg0 hg1 hzero (Real.exp_pos _) hseparation
  -- arithmetic
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hZn1 : (1 : ℝ) ≤ Zn := by
    have : 1 ≤ Zn := Nat.one_le_iff_ne_zero.mpr (by rw [hZndef, ExpITranscendence.measureZ]; positivity)
    exact_mod_cast this
  have hW0 : (0 : ℝ) ≤ W := by positivity
  -- `4M + τ' ≤ W`
  have hsmall : (4 * M + τ' : ℕ) ≤ (W : ℝ) := by
    have h1 : 4 * M + τ' ≤ Hn := by
      have h2M : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
      have h2τ : τ' + 1 ≤ 2 ^ τ' := Nat.lt_two_pow_self
      have ha : 4 * M ≤ (M + 1) * 2 ^ M := by nlinarith
      rw [hHndef]
      nlinarith
    have h2 : Hn ≤ Zn := by
      rw [hZndef, ExpITranscendence.measureZ]
      calc Hn ≤ (Hn + 1) ^ 2 := by nlinarith
        _ ≤ 6 * (2 * M + 1) ^ 2 * (Hn + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    have h3 : (Zn : ℝ) ≤ W := by
      rw [hWdef]
      calc (Zn : ℝ) = (Zn : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hZn1 (by omega)
    exact le_trans (by exact_mod_cast h1.trans h2) h3
  have hgap : Real.exp (-(2 * W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) /
      ((M + 1 : ℕ) ^ 3 * (2 : ℝ) ^ τ') := by
    have h2M : (2 : ℝ) ^ M ≤ Real.exp M := two_pow_nat_le_exp M
    have h2τ : (2 : ℝ) ^ τ' ≤ Real.exp τ' := two_pow_nat_le_exp τ'
    have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp M := natCast_succ_le_exp M
    have hmin : Real.exp (-((M : ℝ) + W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) := by
      apply le_min
      · rw [Real.exp_le_one_iff]; linarith
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
  -- `2W ≤ exp(exp((504a + 9) K²))`
  have hZexp : (Zn : ℝ) ≤ Real.exp (152 * K * M) := measureZ_le_exp hM hK
  have h2W : 2 * W ≤ Real.exp (Real.exp ((504 * (a : ℝ) + 9) * (K : ℝ) ^ 2)) := by
    have hW : W ≤ Real.exp (2128 * K * (M : ℝ) ^ 2) := by
      rw [hWdef]
      calc (Zn : ℝ) ^ (4 * M + 10) ≤ Real.exp (152 * K * M) ^ (4 * M + 10) :=
            pow_le_pow_left₀ (by positivity) hZexp _
        _ = Real.exp ((4 * M + 10 : ℕ) * (152 * K * M)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (2128 * K * (M : ℝ) ^ 2) := by
            apply Real.exp_le_exp.mpr
            push_cast
            nlinarith [mul_le_mul hKr hMr zero_le_one (by linarith : (0 : ℝ) ≤ K)]
    have hlog2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h1 : 2 * W ≤ Real.exp (2129 * K * (M : ℝ) ^ 2) := by
      calc 2 * W ≤ Real.exp 1 * Real.exp (2128 * K * (M : ℝ) ^ 2) :=
            mul_le_mul hlog2 hW hW0 (Real.exp_pos _).le
        _ = Real.exp (1 + 2128 * K * (M : ℝ) ^ 2) := (Real.exp_add _ _).symm
        _ ≤ _ := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul hKr (pow_le_pow_left₀ zero_le_one hMr 2) (by norm_num)
              (by linarith : (0 : ℝ) ≤ K)]
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    -- `2129 K M² ≤ exp((504 a + 9) K²)`
    have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hKe : (K : ℝ) ≤ Real.exp ((K : ℝ) ^ 2) := by
      nlinarith [Real.add_one_le_exp ((K : ℝ) ^ 2)]
    have h2129 : (2129 : ℝ) ≤ Real.exp 8 := by
      have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h8]
      have := Real.exp_one_gt_d9
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) (by linarith : (2.7 : ℝ) ≤ Real.exp 1) 8
      norm_num at this ⊢
      linarith
    calc 2129 * (K : ℝ) * (M : ℝ) ^ 2
        ≤ Real.exp 8 * Real.exp ((K : ℝ) ^ 2) * Real.exp (252 * a * (K : ℝ) ^ 2) ^ 2 := by
          gcongr
      _ = Real.exp (8 + (K : ℝ) ^ 2 + 504 * (a : ℝ) * (K : ℝ) ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp ((504 * (a : ℝ) + 9) * (K : ℝ) ^ 2) :=
          Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-Real.exp (Real.exp ((504 * (a : ℝ) + 9) * (K : ℝ) ^ 2)))
      ≤ Real.exp (-(2 * W)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := hgap
    _ ≤ g := hcert

/-- **Theorem E for `C₁`, protocol form, quantifier elimination only.** Every pure or
common-map mixed protocol of footprint `K ≥ 1` implementing `C₁` with score deficit at most `ε`
has `ε ≥ exp(-exp(exp(C K²)))`; with free standard-Borel classical messages and quantum
footprint `Kq ≥ 1`, `ε ≥ exp(-exp(exp(256 C Kq¹⁰)))`. -/
theorem exists_explicit_controlledPhase_one_protocol_bound_of_QE
    (hQE : BasuPollackRoyExistentialElimination) :
    ∃ CE : ℝ, 0 < CE ∧
      (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
        Real.exp (-Real.exp (Real.exp (CE * (K : ℝ) ^ 2))) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (Real.exp (256 * CE * (Kq : ℝ) ^ 10))) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (Real.exp (256 * CE * (Kq : ℝ) ^ 10))) ≤ ε))) := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_lower_bound_of_QE hQE
  refine ⟨CE, hCE, fun P K ε hK hP hs => (hbound K hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (Real.exp (256 * CE * (Kq : ℝ) ^ 10))) =
      Real.exp (-Real.exp (Real.exp (CE * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2))) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := 1) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (hbound _ h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (hbound _ h64).trans (hmixed n m hK hs)⟩

/-- **Theorem E for `C₁`, triple-logarithm form, quantifier elimination only.** For
`0 < ε < exp(-e)`, a charged footprint `K ≥ 1` with least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln ln(1/ε) - b`. -/
theorem exists_explicit_controlledPhase_one_triple_log_bound_of_QE
    (hQE : BasuPollackRoyExistentialElimination) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (K : ℕ) (ε : ℝ), 1 ≤ K → 0 < ε → ε < Real.exp (-Real.exp 1) →
      controlledPhaseLeastDeficit K 1 ≤ ε →
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (Real.log (1 / ε)))) - b ≤
        Real.logb 2 K := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_lower_bound_of_QE hQE
  refine ⟨max 0 ((1 / 2 : ℝ) * Real.logb 2 CE), le_max_left _ _, ?_⟩
  intro K ε hK hε hεe hle
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := (hbound K hK).trans hle
  have hL1 : Real.exp 1 < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-Real.exp 1)) := Real.log_lt_log hε hεe
      _ = -Real.exp 1 := Real.log_exp _
  have hlog : Real.log (1 / ε) ≤ Real.exp (Real.exp (CE * (K : ℝ) ^ 2)) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hL0 : 0 < Real.log (1 / ε) := lt_trans (Real.exp_pos 1) hL1
  have hloglog : Real.log (Real.log (1 / ε)) ≤ Real.exp (CE * (K : ℝ) ^ 2) := by
    have := Real.log_le_log hL0 hlog
    rwa [Real.log_exp] at this
  have hll1 : 1 < Real.log (Real.log (1 / ε)) := by
    have := Real.log_lt_log (Real.exp_pos 1) hL1
    rwa [Real.log_exp] at this
  have hlll : Real.log (Real.log (Real.log (1 / ε))) ≤ CE * (K : ℝ) ^ 2 := by
    have := Real.log_le_log (by linarith) hloglog
    rwa [Real.log_exp] at this
  have hlll0 : 0 < Real.log (Real.log (Real.log (1 / ε))) := Real.log_pos hll1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hlll0 hlll
  rw [Real.logb_mul hCE.ne' (by positivity), Real.logb_pow] at hb
  have : (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (Real.log (1 / ε)))) -
      (1 / 2 : ℝ) * Real.logb 2 CE ≤ Real.logb 2 K := by
    push_cast at hb
    linarith
  linarith [le_max_right 0 ((1 / 2 : ℝ) * Real.logb 2 CE)]

end NLQCLean
