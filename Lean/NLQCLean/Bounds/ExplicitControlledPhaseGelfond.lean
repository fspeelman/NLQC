import NLQCLean.Bounds.ExplicitControlledPhaseResultant
import NLQCLean.Arithmetic.GelfondMeasure

/-!
# The effective bound for `C₁` with the Gelfond measure for `e^i`

The polynomial-type measure `|P(e^i)| ≥ 2^{-N B (200 B^{31} + 1)}`
(`Gelfond.norm_eval_exp_I_ge`, proved by Gelfond's method) is used in the separation step.
A root `(g, cos 1)` of a nonzero integer polynomial of degree at most `M` with coefficients
below `2^τ` then gives `g ≥ exp(-202 (6M + τ + 128)^{33})`, so:

* with the resultant eliminant, `g_K(1) ≥ exp(-exp(exp(175 K²)))` with an explicit constant;
* with the deformation eliminant (`exists_controlledPhase_certificate_eliminant`),
  `g_K(1) ≥ exp(-exp(C K²))`.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial ExplicitGate ClassicalCommunication

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

/-- `202 B^{33} ≤ exp(exp(175 K²))` for `B ≤ 204 K L³`, `L ≤ exp(9 K T)`,
`T ≤ exp(2 + 164 K²)`. -/
theorem tower_arith_gelfond {K : ℕ} (hK : 1 ≤ K) {L T B : ℝ} (hL0 : 0 ≤ L) (hT1 : 1 ≤ T)
    (hL : L ≤ Real.exp (T * (9 * K))) (hT : T ≤ Real.exp (2 + 164 * (K : ℝ) ^ 2))
    (hB0 : 0 ≤ B) (hB : B ≤ 204 * K * L ^ 3) :
    202 * B ^ 33 ≤ Real.exp (Real.exp (175 * (K : ℝ) ^ 2)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h204 : (204 : ℝ) ≤ Real.exp 6 := by
    have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
  have h1128 : (1128 : ℝ) ≤ Real.exp 8 := by
    have := pow_2718_le_exp 8; norm_num at this ⊢; linarith
  have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hKT : (1 : ℝ) ≤ K * T := one_le_mul_of_one_le_of_one_le hKr hT1
  have step1 : B ≤ Real.exp (34 * K * T) := by
    calc B ≤ 204 * K * L ^ 3 := hB
      _ ≤ Real.exp 6 * Real.exp K * Real.exp (T * (9 * K)) ^ 3 := by gcongr
      _ = Real.exp (6 + K + 27 * K * T) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (34 * K * T) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul hKr hT1 zero_le_one (by linarith : (0 : ℝ) ≤ K)]
  have step2 : 202 * B ^ 33 ≤ Real.exp (1128 * K * T) := by
    calc 202 * B ^ 33 ≤ Real.exp 6 * Real.exp (34 * K * T) ^ 33 := by gcongr; linarith
      _ = Real.exp (6 + 1122 * K * T) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (1128 * K * T) := Real.exp_le_exp.mpr (by nlinarith)
  have step3 : 1128 * K * T ≤ Real.exp (175 * (K : ℝ) ^ 2) := by
    calc 1128 * (K : ℝ) * T ≤ Real.exp 8 * Real.exp K * Real.exp (2 + 164 * (K : ℝ) ^ 2) := by
          gcongr
      _ = Real.exp (10 + K + 164 * (K : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (175 * (K : ℝ) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  exact step2.trans (Real.exp_le_exp.mpr step3)

/-- **Theorem E for `C₁` without external inputs, triple-exponential form.** For every
footprint `K ≥ 1`, `exp(-exp(exp(175 K²))) ≤ g_K(1)`. -/
theorem controlledPhase_one_triple_exp_bound {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-Real.exp (Real.exp (175 * (K : ℝ) ^ 2))) ≤ controlledPhaseLeastDeficit K 1 := by
  obtain ⟨α, hα0, hαzero, hαdeg, hαcoeff⟩ := exists_controlledPhase_one_resultant_eliminant hK
  generalize hN : 2 + 164 * K ^ 2 = N at hαdeg hαcoeff
  generalize hL : (5 * (167 * K ^ 2)) ^ (2 ^ N) = L at hαdeg hαcoeff
  have hL1 : 1 ≤ L := by rw [← hL]; exact Nat.one_le_pow _ _ (by positivity)
  have hbits : ∀ m, (α.coeff m).natAbs < 2 ^ ((55 + 14 * K) * L ^ 3 + 1) := by
    intro m
    have hK2 : K ≤ 2 ^ K := (Nat.lt_two_pow_self).le
    have hbase : 2 ^ 55 * K ^ 14 ≤ 2 ^ (55 + 14 * K) := by
      rw [pow_add, show 14 * K = K * 14 by ring, pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK2 14)
    calc (α.coeff m).natAbs ≤ (2 ^ 55 * K ^ 14) ^ (L ^ 3) := hαcoeff m
      _ ≤ (2 ^ (55 + 14 * K)) ^ (L ^ 3) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((55 + 14 * K) * L ^ 3) := (pow_mul _ _ _).symm
      _ < 2 ^ ((55 + 14 * K) * L ^ 3 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hg0 : 0 < controlledPhaseLeastDeficit K 1 :=
    controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : controlledPhaseLeastDeficit K 1 ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  have hgap := gap_ge_of_cos_one_eliminant_gelfond hg0 hg1 hα0 hL1 hαdeg hbits hαzero
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  have hBnat : 6 * L + ((55 + 14 * K) * L ^ 3 + 1) + 128 ≤ 204 * K * L ^ 3 := by
    have hL3 : L ≤ L ^ 3 := Nat.le_self_pow (by norm_num) L
    have h1 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL1
    have hKL : L ^ 3 ≤ K * L ^ 3 := Nat.le_mul_of_pos_left _ hK
    nlinarith
  have hB : ((6 * L + ((55 + 14 * K) * L ^ 3 + 1) + 128 : ℕ) : ℝ) ≤ 204 * K * (L : ℝ) ^ 3 := by
    exact_mod_cast hBnat
  have hbase : ((5 * (167 * K ^ 2) : ℕ) : ℝ) ≤ Real.exp (9 * K) := by
    have h835 : (835 : ℝ) ≤ Real.exp 7 := by
      have := pow_2718_le_exp 7; norm_num at this ⊢; linarith
    have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
    calc ((5 * (167 * K ^ 2) : ℕ) : ℝ) = 835 * (K : ℝ) ^ 2 := by push_cast; ring
      _ ≤ Real.exp 7 * Real.exp K ^ 2 := by gcongr
      _ = Real.exp (7 + 2 * K) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  have hLexp : (L : ℝ) ≤ Real.exp (((2 ^ N : ℕ) : ℝ) * (9 * K)) := by
    rw [← hL, Real.exp_nat_mul]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _
  have h2N : ((2 ^ N : ℕ) : ℝ) ≤ Real.exp (2 + 164 * (K : ℝ) ^ 2) := by
    have := two_pow_nat_le_exp N
    rw [← hN] at this ⊢
    push_cast at this ⊢
    exact this
  exact tower_arith_gelfond hK (by positivity) (by exact_mod_cast Nat.one_le_two_pow) hLexp h2N
    (by positivity) hB

/-- **Theorem E for `C₁` without external inputs, triple-exponential protocol form.** Every
pure or common-map mixed protocol of footprint `K ≥ 1` implementing `C₁` with score deficit at
most `ε` has `ε ≥ exp(-exp(exp(175 K²)))`; with free standard-Borel classical messages and
quantum footprint `Kq ≥ 1`, `ε ≥ exp(-exp(exp(44800 Kq¹⁰)))`. -/
theorem controlledPhase_one_protocol_triple_exp_bound :
    (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
        Real.exp (-Real.exp (Real.exp (175 * (K : ℝ) ^ 2))) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (Real.exp (44800 * (Kq : ℝ) ^ 10))) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (Real.exp (44800 * (Kq : ℝ) ^ 10))) ≤ ε))) := by
  refine ⟨fun P K ε hK hP hs => (controlledPhase_one_triple_exp_bound hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (Real.exp (44800 * (Kq : ℝ) ^ 10))) =
      Real.exp (-Real.exp (Real.exp (175 * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2))) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := 1) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (controlledPhase_one_triple_exp_bound h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (controlledPhase_one_triple_exp_bound h64).trans
      (hmixed n m hK hs)⟩

/-- **Theorem E for `C₁` without external inputs, triple-logarithm form.** For
`0 < ε < exp(-e)`, a charged footprint `K ≥ 1` with least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln ln(1/ε) - ½ log₂ 175`. -/
theorem controlledPhase_one_triple_log_bound (K : ℕ) (ε : ℝ) (hK : 1 ≤ K) (hε : 0 < ε)
    (hεe : ε < Real.exp (-Real.exp 1)) (hle : controlledPhaseLeastDeficit K 1 ≤ ε) :
    (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (Real.log (1 / ε)))) -
      (1 / 2 : ℝ) * Real.logb 2 175 ≤ Real.logb 2 K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := (controlledPhase_one_triple_exp_bound hK).trans hle
  have hL1 : Real.exp 1 < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-Real.exp 1)) := Real.log_lt_log hε hεe
      _ = -Real.exp 1 := Real.log_exp _
  have hL0 : 0 < Real.log (1 / ε) := lt_trans (Real.exp_pos _) hL1
  have hlog : Real.log (1 / ε) ≤ Real.exp (Real.exp (175 * (K : ℝ) ^ 2)) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hll1 : 1 < Real.log (Real.log (1 / ε)) := by
    have := Real.log_lt_log (Real.exp_pos _) hL1
    rwa [Real.log_exp] at this
  have hloglog : Real.log (Real.log (1 / ε)) ≤ Real.exp (175 * (K : ℝ) ^ 2) := by
    have := Real.log_le_log hL0 hlog
    rwa [Real.log_exp] at this
  have hlll : Real.log (Real.log (Real.log (1 / ε))) ≤ 175 * (K : ℝ) ^ 2 := by
    have := Real.log_le_log (by linarith) hloglog
    rwa [Real.log_exp] at this
  have hlll0 : 0 < Real.log (Real.log (Real.log (1 / ε))) := Real.log_pos hll1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hlll0 hlll
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at hb
  push_cast at hb
  linarith

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

/-- **Theorem E for `C₁`.** With the Gelfond measure for `e^i`, there is `C > 0` with
`exp(-exp(C K²)) ≤ g_K(1)` for every footprint `K ≥ 1`. -/
theorem exists_explicit_controlledPhase_one_lower_bound :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K 1 := by
  obtain ⟨a, helim⟩ := exists_controlledPhase_one_eliminant
  refine ⟨8316 * a + 237, by positivity, fun K hK => ?_⟩
  obtain ⟨M, hM, hMexp, A, hA0, hdeg, hbits, hzero⟩ := helim K hK
  have hg0 : 0 < controlledPhaseLeastDeficit K 1 :=
    controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : controlledPhaseLeastDeficit K 1 ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  have hgap := gap_ge_of_cos_one_eliminant_gelfond hg0 hg1 hA0 hM hdeg hbits hzero
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  have hBnat : 6 * M + (56 + 14 * K) * M + 128 ≤ 204 * K * M := by
    have hKM : M ≤ K * M := Nat.le_mul_of_pos_left _ hK
    nlinarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hB : ((6 * M + (56 + 14 * K) * M + 128 : ℕ) : ℝ) ≤ Real.exp (6 + K + 252 * a * (K : ℝ) ^ 2) := by
    have h204 : (204 : ℝ) ≤ Real.exp 6 := by
      have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
    have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    calc ((6 * M + (56 + 14 * K) * M + 128 : ℕ) : ℝ) ≤ 204 * K * (M : ℝ) := by
          exact_mod_cast hBnat
      _ ≤ Real.exp 6 * Real.exp K * Real.exp (252 * a * (K : ℝ) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have h202 : (202 : ℝ) ≤ Real.exp 6 := by
    have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
  calc 202 * ((6 * M + (56 + 14 * K) * M + 128 : ℕ) : ℝ) ^ 33
      ≤ Real.exp 6 * Real.exp (6 + K + 252 * a * (K : ℝ) ^ 2) ^ 33 := by gcongr
    _ = Real.exp (204 + 33 * K + 8316 * a * (K : ℝ) ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp ((8316 * (a : ℝ) + 237) * (K : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hK2 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
        nlinarith

/-- **Theorem E for `C₁`, protocol form.**
Every pure or common-map mixed protocol of footprint `K ≥ 1` implementing `C₁` with score
deficit at most `ε` has `ε ≥ exp(-exp(C K²))`; with free standard-Borel classical messages and
quantum footprint `Kq ≥ 1`, `ε ≥ exp(-exp(256 C Kq¹⁰))`. -/
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
`log₂ K ≥ ½ log₂ ln ln(1/ε) - b`. -/
theorem exists_explicit_controlledPhase_one_iterated_log_bound :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (K : ℕ) (ε : ℝ), 1 ≤ K → 0 < ε → ε < Real.exp (-1) →
      controlledPhaseLeastDeficit K 1 ≤ ε →
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 K := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_lower_bound
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

end NLQCLean
