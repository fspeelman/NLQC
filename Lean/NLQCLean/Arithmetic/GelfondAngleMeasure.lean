import NLQCLean.Arithmetic.GelfondAngleNumerics
import NLQCLean.Arithmetic.GelfondMeasure
import NLQCLean.External.EffectiveArithmetic

/-!
# A polynomial-type transcendence measure for `e^{iθ}`, `θ` real algebraic

For a nonzero `P ∈ ℤ[X]` of degree at most `N` with coefficients at most `H`, and any `B ≥ 128`
bounding `N`, `log₂(2^N (N+1) H)` and the data `a, m, 1+F, |θ|` of `θ`,

`|P(e^{iθ})| ≥ 2^{-N B (B⁴⁸ + 1)}`

(`norm_eval_exp_angle_ge`). Here `aθ` is a root of the monic `f ∈ ℤ[X]` of degree `m` whose
coefficients are at most `F`. As for `e^i`, `P` is factored into irreducibles of `ℤ[i][X]`.
Taking `B` linear in `N + log H` proves `PolynomialTypeTranscendenceMeasureExpAngle`
unconditionally (`polynomialTypeTranscendenceMeasureExpAngle`).
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

/-- **Measure at `e^{iθ}`.** -/
theorem norm_eval_exp_angle_ge {P : ℤ[X]} (hP : P ≠ 0) {N B : ℕ} (hB : 128 ≤ B)
    (hN : P.natDegree ≤ N) (hNB : N ≤ B) {H : ℝ} (hH : ∀ k, |(P.coeff k : ℝ)| ≤ H)
    (hHB : 2 ^ N * ((N + 1) * H) ≤ 2 ^ B) {a : ℕ} (ha1 : 1 ≤ a) (haB : a ≤ B)
    {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) (hm : 1 ≤ m) (hmB : m ≤ B)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθB : |θ| ≤ B) {ϑ : ℂ} (hϑa : ϑ = a * θ)
    (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) (hFB : 1 + F ≤ B) :
    (1 / 2 : ℝ) ^ (N * (B * (B ^ 48 + 1))) ≤
      ‖P.eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  classical
  set K := B * (B ^ 48 + 1)
  set ζ := Complex.exp ((θ : ℂ) * Complex.I)
  set P' : GaussianInt[X] := P.map (Int.castRingHom GaussianInt) with hP'
  have hinj : Function.Injective (Int.castRingHom GaussianInt) := by
    intro x y hxy
    have := congrArg Zsqrtd.re hxy
    simpa using this
  have hP'0 : P' ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hP
  have hP'deg : P'.natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hP'c : P'.map toComplex = P.map (Int.castRingHom ℂ) := by
    rw [hP', Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have heval : P.eval₂ (Int.castRingHom ℂ) ζ = (P'.map toComplex).eval ζ := by
    rw [hP'c, eval_map]
  have hP'coeff : ∀ k, ‖((P'.coeff k : GaussianInt) : ℂ)‖ ≤ H := fun k => by
    rw [hP', coeff_map]
    simpa [Complex.norm_intCast] using hH k
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hMP : (P'.map toComplex).mahlerMeasure ≤ (N + 1) * H := by
    refine (mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
    have hsup : (P'.map toComplex).supNorm ≤ H :=
      supNorm_le_of_coeff_le fun k => by rw [coeff_map]; exact hP'coeff k
    calc √(((P'.map toComplex).natDegree : ℝ) + 1) * (P'.map toComplex).supNorm
        ≤ √((N : ℝ) + 1) * H := by
          gcongr
          · exact supNorm_nonneg _
          · rw [natDegree_map_eq_of_injective toComplex_injective, hP'deg]
            exact_mod_cast hN
      _ ≤ (N + 1) * H := by
          gcongr
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hP'0
  set fs := UniqueFactorizationMonoid.factors P'
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hr0 : r ≠ 0 := hr.ne_zero
  have hfac : ∀ G ∈ fs, (1 / 2 : ℝ) ^ (K * G.natDegree) ≤ ‖(G.map toComplex).eval ζ‖ := by
    intro G hG
    have hirr := UniqueFactorizationMonoid.irreducible_of_factor G hG
    have hdvd := UniqueFactorizationMonoid.dvd_of_mem_factors hG
    have hG0 : G ≠ 0 := hirr.ne_zero
    by_cases hdeg : G.natDegree = 0
    · rw [hdeg, mul_zero, pow_zero, eq_C_of_natDegree_eq_zero hdeg, map_C, eval_C]
      have : G.coeff 0 ≠ 0 := by
        intro h0; apply hG0; rw [eq_C_of_natDegree_eq_zero hdeg, h0, C_0]
      exact one_le_norm_toComplex this
    · have hdegB : G.natDegree ≤ B :=
        (natDegree_le_of_dvd hdvd hP'0).trans (hP'deg ▸ hN |>.trans hNB)
      obtain ⟨W, hW⟩ := hdvd
      have hW0 : W ≠ 0 := by rintro rfl; rw [mul_zero] at hW; exact hP'0 hW
      have hW1 : 1 ≤ (W.map toComplex).mahlerMeasure := by
        refine one_le_mahlerMeasure_of_one_le_norm_leadingCoeff ?_
        rw [leadingCoeff_map_of_injective toComplex_injective]
        exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hW0)
      have hcoeffG : ∀ k, ‖((G.coeff k : GaussianInt) : ℂ)‖ ≤ 2 ^ B := by
        intro k
        have h1 := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure k
          (G.map toComplex) (W.map toComplex) hW1
        rw [← Polynomial.map_mul, ← hW, coeff_map] at h1
        refine h1.trans ?_
        have hch : ((G.map toComplex).natDegree.choose k : ℝ) ≤ 2 ^ N := by
          have h2 : (G.map toComplex).natDegree.choose k ≤ 2 ^ (G.map toComplex).natDegree :=
            Nat.choose_le_two_pow _ _
          have h3 : (G.map toComplex).natDegree ≤ N := by
            rw [natDegree_map_eq_of_injective toComplex_injective]
            exact (natDegree_le_of_dvd ⟨W, hW⟩ hP'0).trans (hP'deg ▸ hN)
          calc ((G.map toComplex).natDegree.choose k : ℝ)
              ≤ ((2 ^ (G.map toComplex).natDegree : ℕ) : ℝ) := by exact_mod_cast h2
            _ ≤ 2 ^ N := by push_cast; exact pow_le_pow_right₀ (by norm_num) h3
        calc ((G.map toComplex).natDegree.choose k : ℝ) * (P'.map toComplex).mahlerMeasure
            ≤ 2 ^ N * ((N + 1) * H) :=
              mul_le_mul hch hMP (mahlerMeasure_nonneg _) (by positivity)
          _ ≤ 2 ^ B := hHB
      have := norm_eval_exp_angle_ge_of_irreducible hirr (Nat.pos_of_ne_zero hdeg) hB hdegB
        hcoeffG ha1 haB hf hmf hm hmB hθ0 hθB hϑa hϑ hF0 hF hFB
      refine le_trans ?_ this
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hdeg))
  have hprod := prod_lower_bound fs (fun G => (G.map toComplex).eval ζ) natDegree K hfac
  have hsumdeg : (fs.map natDegree).sum ≤ N := by
    have h0 : (0 : GaussianInt[X]) ∉ fs := fun h =>
      (UniqueFactorizationMonoid.irreducible_of_factor 0 h).ne_zero rfl
    rw [← natDegree_multiset_prod _ h0]
    have : P' = fs.prod * C r := by rw [hru]; exact hu.symm
    have hdeg := congrArg natDegree this
    rw [natDegree_mul_C hr0] at hdeg
    rw [← hdeg, hP'deg]; exact hN
  have hPeval : (P'.map toComplex).eval ζ =
      (fs.map fun G => (G.map toComplex).eval ζ).prod * (r : ℂ) := by
    have : P' = fs.prod * C r := by rw [hru]; exact hu.symm
    conv_lhs => rw [this]
    rw [Polynomial.map_mul, eval_mul, map_C, eval_C, Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.map_map]
    rfl
  rw [heval, hPeval, norm_mul]
  have hNK : K * (fs.map natDegree).sum ≤ N * K := by
    rw [mul_comm]; exact Nat.mul_le_mul_right _ hsumdeg
  calc (1 / 2 : ℝ) ^ (N * K) ≤ (1 / 2 : ℝ) ^ (K * (fs.map natDegree).sum) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hNK
    _ ≤ ‖(fs.map fun G => (G.map toComplex).eval ζ).prod‖ := hprod
    _ ≤ _ := le_mul_of_one_le_right (norm_nonneg _) (one_le_norm_toComplex hr0)

/-- The arithmetic data of a real algebraic angle: `aθ` is a root of a monic integer polynomial
of positive degree. -/
theorem exists_angle_data {θ : ℝ} (hθ : IsAlgebraic ℚ θ) :
    ∃ (a : ℕ) (f : ℤ[X]), 1 ≤ a ∧ f.Monic ∧ 1 ≤ f.natDegree ∧
      f.eval₂ (Int.castRingHom ℂ) ((a : ℂ) * θ) = 0 := by
  have hθc : IsAlgebraic ℚ (θ : ℂ) := by
    simpa only [Complex.coe_algebraMap] using hθ.algebraMap (A := ℂ)
  have hθZ : IsAlgebraic ℤ (θ : ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hθc
  obtain ⟨y, hy0, hyint⟩ := hθZ.exists_integral_multiple
  have hcast : ((y.natAbs : ℕ) : ℂ) = ((|y| : ℤ) : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  have hint : IsIntegral ℤ ((y.natAbs : ℂ) * θ) := by
    rcases le_or_gt 0 y with hy | hy
    · have : (y.natAbs : ℂ) * θ = y • (θ : ℂ) := by
        rw [zsmul_eq_mul, hcast, abs_of_nonneg hy]
      rw [this]; exact hyint
    · have : (y.natAbs : ℂ) * θ = -(y • (θ : ℂ)) := by
        rw [zsmul_eq_mul, hcast, abs_of_neg hy]
        push_cast; ring
      rw [this]; exact hyint.neg
  refine ⟨y.natAbs, minpoly ℤ ((y.natAbs : ℂ) * θ), Int.natAbs_pos.mpr hy0,
    minpoly.monic hint, minpoly.natDegree_pos hint, ?_⟩
  have := minpoly.aeval ℤ ((y.natAbs : ℂ) * θ)
  rwa [aeval_def, algebraMap_int_eq] at this

end NLQCLean.Gelfond

namespace NLQCLean

open Polynomial Gelfond

/-- **Weak E-TM, proved.** For every nonzero real algebraic `θ`, `e^{iθ}` has a transcendence
measure of polynomial type `exp(-C (N + log H)^{50})` (Gelfond's method). -/
theorem polynomialTypeTranscendenceMeasureExpAngle :
    PolynomialTypeTranscendenceMeasureExpAngle := by
  intro θ hθ0 hθ
  obtain ⟨a, f, ha1, hf, hm, hfθ⟩ := exists_angle_data hθ
  set m := f.natDegree with hmdef
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = ∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)| :=
    ⟨_, rfl⟩
  have hF0 : 0 ≤ F := hFdef ▸ Finset.sum_nonneg fun i _ => abs_nonneg _
  have hF : ∀ i, |(f.coeff i : ℝ)| ≤ F := by
    intro i
    by_cases hi : i ≤ f.natDegree
    · rw [hFdef]
      exact Finset.single_le_sum (f := fun i => |(f.coeff i : ℝ)|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), Int.cast_zero, abs_zero]; exact hF0
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℕ, B₀ = 128 + a + m + ⌈F⌉₊ + ⌈|θ|⌉₊ + 1 := ⟨_, rfl⟩
  refine ⟨2 * ((B₀ : ℝ) + 3) ^ 50, 50, by positivity, fun N H P hP hPN hcoeff => ?_⟩
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hH : 1 ≤ H := by
    by_contra h
    have hP0' : P = 0 := by
      ext i
      have := hcoeff i
      simp only [show H = 0 by omega, Nat.cast_zero, abs_nonpos_iff] at this
      simpa using this
    exact hP0 hP0'
  have hN1 : 1 ≤ N := hP.trans_le hPN
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = B₀ + 2 * N + Nat.log 2 H + 1 := ⟨_, rfl⟩
  have hB : 128 ≤ B := by omega
  have hNB : N ≤ B := by omega
  have haB : a ≤ B := by omega
  have hmB : m ≤ B := by omega
  have hFB : 1 + F ≤ B := by
    have : F ≤ ⌈F⌉₊ := Nat.le_ceil F
    have : ((⌈F⌉₊ : ℕ) : ℝ) + 1 ≤ B := by exact_mod_cast (show ⌈F⌉₊ + 1 ≤ B by omega)
    linarith
  have hθB : |θ| ≤ B := by
    have : |θ| ≤ ⌈|θ|⌉₊ := Nat.le_ceil _
    have : ((⌈|θ|⌉₊ : ℕ) : ℝ) ≤ B := by exact_mod_cast (show ⌈|θ|⌉₊ ≤ B by omega)
    linarith
  have hHr : ∀ k, |(P.coeff k : ℝ)| ≤ (H : ℝ) := fun k => by exact_mod_cast hcoeff k
  have hHB : (2 : ℝ) ^ N * ((N + 1) * (H : ℝ)) ≤ 2 ^ B := by
    have h1 : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
    have h2 : H < 2 ^ (Nat.log 2 H + 1) := Nat.lt_pow_succ_log_self (by norm_num) H
    have hnat : 2 ^ N * ((N + 1) * H) ≤ 2 ^ B := by
      calc 2 ^ N * ((N + 1) * H) ≤ 2 ^ N * (2 ^ N * 2 ^ (Nat.log 2 H + 1)) := by
            gcongr
      _ = 2 ^ (N + N + (Nat.log 2 H + 1)) := by simp only [pow_add]; ring
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hnat
  have hmeas := norm_eval_exp_angle_ge hP0 hB hPN hNB hHr hHB ha1 haB hf rfl hm hmB hθ0 hθB rfl
    hfθ hF0 hF hFB
  refine le_trans ?_ hmeas
  -- `(1/2)^{N B (B⁴⁸+1)} ≥ exp(-2 B⁵⁰)`
  have hexp : N * (B * (B ^ 48 + 1)) ≤ 2 * B ^ 50 := by
    have h1 : B ^ 48 + 1 ≤ 2 * B ^ 48 := by have := Nat.one_le_pow 48 B (by omega); omega
    calc N * (B * (B ^ 48 + 1)) ≤ B * (B * (2 * B ^ 48)) := by gcongr
      _ = 2 * B ^ 50 := by ring
  have hhalf : Real.exp (-((2 * B ^ 50 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (N * (B * (B ^ 48 + 1))) := by
    calc Real.exp (-((2 * B ^ 50 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (2 * B ^ 50) := by
          rw [one_div, inv_pow, Real.exp_neg]
          refine inv_anti₀ (by positivity) ?_
          have := Real.add_one_le_exp (1 : ℝ)
          calc (2 : ℝ) ^ (2 * B ^ 50) ≤ Real.exp 1 ^ (2 * B ^ 50) :=
                pow_le_pow_left₀ (by norm_num) (by linarith) _
            _ = Real.exp ((2 * B ^ 50 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ (1 / 2 : ℝ) ^ (N * (B * (B ^ 48 + 1))) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  refine le_trans (Real.exp_le_exp.mpr ?_) hhalf
  rw [neg_le_neg_iff]
  -- `B ≤ (B₀ + 3) (N + log H)`
  set X := (N : ℝ) + Real.log H with hX
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hlog2 : ((Nat.log 2 H : ℕ) : ℝ) ≤ 2 * Real.log H := by
    have hpow : ((2 ^ Nat.log 2 H : ℕ) : ℝ) ≤ H := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : H ≠ 0)
    have hl := Real.log_le_log (by positivity) hpow
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hl
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 H)]
  have hBX : (B : ℝ) ≤ ((B₀ : ℝ) + 3) * X := by
    have hB' : (B : ℝ) = B₀ + 2 * N + (Nat.log 2 H : ℕ) + 1 := by rw [hBdef]; push_cast; ring
    have hB0 : (0 : ℝ) ≤ B₀ := Nat.cast_nonneg _
    nlinarith
  have hpow : ((B : ℝ)) ^ 50 ≤ (((B₀ : ℝ) + 3) * X) ^ 50 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hBX 50
  push_cast
  calc 2 * (B : ℝ) ^ 50 ≤ 2 * (((B₀ : ℝ) + 3) * X) ^ 50 := by gcongr
    _ = 2 * ((B₀ : ℝ) + 3) ^ 50 * X ^ 50 := by rw [mul_pow]; ring

end NLQCLean
