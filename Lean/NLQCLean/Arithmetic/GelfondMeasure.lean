import NLQCLean.Arithmetic.GelfondNumerics

/-!
# A polynomial-type transcendence measure for `e^i`

For a nonzero `P ∈ ℤ[X]` of degree at most `N` with coefficients at most `H`, and any `B ≥ 128`
with `N ≤ B` and `2^N (N+1) H ≤ 2^B`,

`|P(e^i)| ≥ 2^{-N B (200 B^{31} + 1)}`.

`P` is factored into irreducibles of `ℤ[i][X]`; constant factors have absolute value at least
one, and each factor of positive degree has coefficients at most `2^N (N+1) H` (Mignotte's
bound through the Mahler measure) and obeys the Gelfond bound. Taking `B` linear in
`N + log H` gives a measure of polynomial type `exp(-C (N + log H)^{33})`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

theorem prod_lower_bound {α : Type*} (s : Multiset α) (f : α → ℂ) (g : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ s, (1 / 2 : ℝ) ^ (K * g x) ≤ ‖f x‖) :
    (1 / 2 : ℝ) ^ (K * (s.map g).sum) ≤ ‖(s.map f).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, norm_mul,
      mul_add, pow_add]
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (by positivity) (norm_nonneg _)

/-- **Polynomial-type measure for `e^i`.** -/
theorem norm_eval_exp_I_ge {P : ℤ[X]} (hP : P ≠ 0) {N B : ℕ} (hB : 128 ≤ B)
    (hN : P.natDegree ≤ N) (hNB : N ≤ B) {H : ℝ} (hH : ∀ k, |(P.coeff k : ℝ)| ≤ H)
    (hHB : 2 ^ N * ((N + 1) * H) ≤ 2 ^ B) :
    (1 / 2 : ℝ) ^ (N * (B * (200 * B ^ 31 + 1))) ≤
      ‖P.eval₂ (Int.castRingHom ℂ) (Complex.exp Complex.I)‖ := by
  classical
  set K := B * (200 * B ^ 31 + 1)
  set ζ := Complex.exp Complex.I
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
  -- the Mahler measure of `P`
  have hMP : (P'.map toComplex).mahlerMeasure ≤ (N + 1) * H := by
    refine (mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
    have hdeg : ((P'.map toComplex).natDegree : ℝ) + 1 ≤ N + 1 := by
      rw [natDegree_map_eq_of_injective toComplex_injective, hP'deg]; exact_mod_cast
        Nat.succ_le_succ hN
    have hsup : (P'.map toComplex).supNorm ≤ H :=
      supNorm_le_of_coeff_le fun k => by rw [coeff_map]; exact hP'coeff k
    calc √(((P'.map toComplex).natDegree : ℝ) + 1) * (P'.map toComplex).supNorm
        ≤ √((N : ℝ) + 1) * H := by gcongr; exact supNorm_nonneg _
      _ ≤ (N + 1) * H := by
          gcongr
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  -- factorization
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
      have := norm_eval_exp_I_ge_of_irreducible hirr (Nat.pos_of_ne_zero hdeg) hB hdegB hcoeffG
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

end NLQCLean.Gelfond
