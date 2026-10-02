import NLQCLean.Arithmetic.GelfondAngleLiouville

/-!
# The auxiliary function of Gelfond's method for `e^ω`

For integers `c_{jl}` (`j ≤ J`, `l < L`) and `ω ∈ ℂ` put `F(z) = Σ c_{jl} z^l e^{jωz}`. Its
derivatives at integer points are values at `ζ = e^ω` of the complex polynomials
`S_{t,s} = Σ c_{jl} κ_ω(t,s,j,l) X^{js}`. For `ω = θ i` with `aθ = ϑ` a root of a monic
`f ∈ ℤ[X]` of degree `m`, `a^t S_{t,s} = Σ_{e<m} ϑ^e Q_{t,s,e}` with `Q_{t,s,e} ∈ ℤ[i][X]`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt Filter Topology

/-! ### Analysis -/

/-- The truncated auxiliary function with frequencies `jω`. -/
noncomputable def angF {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (D : ℕ) : ℂ[X] :=
  ∑ j : Fin (J + 1), ∑ l : Fin L,
    C (c j l : ℂ) * (X ^ (l : ℕ) * (expPoly D).comp (C ((j : ℂ) * ω) * X))

/-- `κ_ω(t,s,j,l) = Σ_{k ≤ t} C(t,k) (l)_{t-k} s^{l-(t-k)} (jω)^k`. -/
noncomputable def angKappa (ω : ℂ) (t s j l : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (t + 1), ((t.choose k * l.descFactorial (t - k) : ℕ) : ℂ) *
    (s : ℂ) ^ (l - (t - k)) * ((j : ℂ) * ω) ^ k

/-- The complex polynomials `S_{t,s}`. -/
noncomputable def angS {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) : ℂ[X] :=
  ∑ j : Fin (J + 1), ∑ l : Fin L, C ((c j l : ℂ) * angKappa ω t s j l) * X ^ ((j : ℕ) * s)

theorem eval_iterate_derivative_angF {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ)
    (D t : ℕ) (w : ℂ) :
    (derivative^[t] (angF ω c D)).eval w =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) *
        ∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          w ^ ((l : ℕ) - (t - k)) * (((j : ℂ) * ω) ^ k *
            (expPoly (D - k)).eval ((j : ℂ) * ω * w)) := by
  rw [angF]
  simp only [iterate_derivative_sum, iterate_derivative_C_mul, eval_finsetSum, eval_mul, eval_C,
    eval_iterate_derivative_term]

theorem eval_angS {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) (z : ℂ) :
    (angS ω c t s).eval z =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) * angKappa ω t s j l * z ^ ((j : ℕ) * s) := by
  simp only [angS, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- **Convergence.** `F_D^{(t)}(s) → S_{t,s}(e^ω)`. -/
theorem tendsto_angF_derivative {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) :
    Tendsto (fun D => (derivative^[t] (angF ω c D)).eval (s : ℂ)) atTop
      (𝓝 ((angS ω c t s).eval (Complex.exp ω))) := by
  simp_rw [eval_iterate_derivative_angF, eval_angS, angKappa]
  have hlim : (fun j : Fin (J + 1) => ∑ l : Fin L, (c j l : ℂ) *
        (∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * ((j : ℂ) * ω) ^ k) *
          Complex.exp ω ^ ((j : ℕ) * s)) =
      fun j => ∑ l : Fin L, (c j l : ℂ) *
        ∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * (((j : ℂ) * ω) ^ k *
            Complex.exp ((j : ℂ) * ω * s)) := by
    funext j
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show Complex.exp ((j : ℂ) * ω * s) = Complex.exp ω ^ ((j : ℕ) * s) by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [show (∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) *
        (∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * ((j : ℂ) * ω) ^ k) *
          Complex.exp ω ^ ((j : ℕ) * s)) = _ from congrArg (fun f => ∑ j, f j) hlim]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun l _ => ?_
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_)
  exact Tendsto.const_mul _ (tendsto_eval_expPoly _ k)

/-- **Growth.** -/
theorem norm_eval_angF_le {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ}
    (hCc : 0 ≤ Cc) (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc) (D : ℕ) {R : ℝ} (hR : 1 ≤ R) {w : ℂ}
    (hw : ‖w‖ ≤ R) :
    ‖(angF ω c D).eval w‖ ≤ (J + 1) * L * Cc * R ^ L * Real.exp (J * ‖ω‖ * R) := by
  simp only [angF, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ (j : Fin (J + 1)) (l : Fin L),
      ‖(c j l : ℂ) * (w ^ (l : ℕ) * (expPoly D).eval ((j : ℂ) * ω * w))‖ ≤
        Cc * (R ^ L * Real.exp (J * ‖ω‖ * R)) := by
    intro j l
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_intCast]
    refine mul_le_mul (hc j l) (mul_le_mul ?_ ?_ (_root_.norm_nonneg _) (by positivity))
      (by positivity) hCc
    · calc ‖w‖ ^ (l : ℕ) ≤ R ^ (l : ℕ) := pow_le_pow_left₀ (_root_.norm_nonneg _) hw _
        _ ≤ R ^ L := pow_le_pow_right₀ hR l.isLt.le
    · refine (norm_eval_expPoly_le D _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hj : (j : ℝ) ≤ J := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
      have := _root_.norm_nonneg ω
      calc (j : ℝ) * ‖ω‖ * ‖w‖ ≤ J * ‖ω‖ * R := by gcongr
        _ = J * ‖ω‖ * R := rfl
  calc ∑ j : Fin (J + 1), ‖∑ l : Fin L, (c j l : ℂ) *
        (w ^ (l : ℕ) * (expPoly D).eval ((j : ℂ) * ω * w))‖
      ≤ ∑ _j : Fin (J + 1), ∑ _l : Fin L, Cc * (R ^ L * Real.exp (J * ‖ω‖ * R)) :=
        Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm j l)
    _ = (J + 1) * L * Cc * R ^ L * Real.exp (J * ‖ω‖ * R) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem norm_angKappa_le (ω : ℂ) {t s j l h J L : ℕ} (hs : s ≤ h) (hh : 1 ≤ h) (hj : j ≤ J)
    (hl : l ≤ L) : ‖angKappa ω t s j l‖ ≤ (h : ℝ) ^ L * ((J : ℝ) * ‖ω‖ + L) ^ t := by
  rw [angKappa]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (t + 1),
      ‖((t.choose k * l.descFactorial (t - k) : ℕ) : ℂ) * (s : ℂ) ^ (l - (t - k)) *
        ((j : ℂ) * ω) ^ k‖ ≤
        (h : ℝ) ^ L * (((J : ℝ) * ‖ω‖) ^ k * (L : ℝ) ^ (t - k) * (t.choose k : ℝ)) := by
    intro k _
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
      norm_mul, Complex.norm_natCast]
    push_cast
    have h1 : ((l.descFactorial (t - k) : ℕ) : ℝ) ≤ (L : ℝ) ^ (t - k) := by
      exact_mod_cast (Nat.descFactorial_le_pow l _).trans (Nat.pow_le_pow_left hl _)
    have h2 : (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ L := by
      calc (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ (l - (t - k)) :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) _
        _ ≤ (h : ℝ) ^ L := pow_le_pow_right₀ (by exact_mod_cast hh) (by omega)
    have h3 : ((j : ℝ) * ‖ω‖) ^ k ≤ ((J : ℝ) * ‖ω‖) ^ k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
        (_root_.norm_nonneg _)) _
    calc (t.choose k : ℝ) * (l.descFactorial (t - k) : ℝ) * (s : ℝ) ^ (l - (t - k)) *
          ((j : ℝ) * ‖ω‖) ^ k
        ≤ (t.choose k : ℝ) * (L : ℝ) ^ (t - k) * (h : ℝ) ^ L * ((J : ℝ) * ‖ω‖) ^ k := by
          gcongr
      _ = (h : ℝ) ^ L * (((J : ℝ) * ‖ω‖) ^ k * (L : ℝ) ^ (t - k) * (t.choose k : ℝ)) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← add_pow]

theorem natDegree_angS_le {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) :
    (angS ω c t s).natDegree ≤ J * s := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.isLt)

theorem norm_coeff_angS_le {J L h : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ}
    (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc) {t s : ℕ} (hs : s ≤ h) (hh : 1 ≤ h) (m : ℕ) :
    ‖(angS ω c t s).coeff m‖ ≤
      (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) * ‖ω‖ + L) ^ t)) := by
  have hcoeff : (angS ω c t s).coeff m = ∑ j : Fin (J + 1), ∑ l : Fin L,
      if (j : ℕ) * s = m then (c j l : ℂ) * angKappa ω t s j l else 0 := by
    simp only [angS, finsetSum_coeff, coeff_C_mul_X_pow]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  rw [hcoeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin (J + 1), ‖∑ l : Fin L, if (j : ℕ) * s = m then
        (c j l : ℂ) * angKappa ω t s j l else 0‖
      ≤ ∑ _j : Fin (J + 1), ∑ _l : Fin L, Cc * ((h : ℝ) ^ L * ((J : ℝ) * ‖ω‖ + L) ^ t) := by
        refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun l _ => ?_)
        have hCc : 0 ≤ Cc := (abs_nonneg _).trans (hc j l)
        split_ifs
        · rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul (hc j l) (norm_angKappa_le ω hs hh (Nat.lt_succ_iff.mp j.isLt)
            l.isLt.le) (_root_.norm_nonneg _) hCc
        · rw [norm_zero]; positivity
    _ = (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) * ‖ω‖ + L) ^ t)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem angKappa_zero (ω : ℂ) (t j l : ℕ) :
    angKappa ω t 0 j l = (t.descFactorial l : ℂ) * ((j : ℂ) * ω) ^ (t - l) := by
  rw [angKappa]
  by_cases hlt : l ≤ t
  · rw [Finset.sum_eq_single (t - l)]
    · rw [show t - (t - l) = l by omega, Nat.sub_self, pow_zero, mul_one,
        Nat.descFactorial_self, Nat.choose_symm hlt, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast; ring
    · intro k hk hkne
      have hk1 := Finset.mem_range.mp hk
      by_cases hk' : t - k ≤ l
      · have hne : l - (t - k) ≠ 0 := by omega
        simp [zero_pow hne]
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; simp
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hne : l - (t - k) ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow hne]

theorem angS_zero {J L : ℕ} (ω : ℂ) (c : Fin (J + 1) → Fin L → ℤ) (t : ℕ) :
    angS ω c t 0 = C (∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) * angKappa ω t 0 j l) := by
  simp [angS, map_sum]

/-! ### Arithmetic -/

/-- The Gaussian-integer coefficients `κ_e(t,s,j,l) = Σ_k C(t,k) (l)_{t-k} s^{l-(t-k)} a^{t-k}
π(k,e) (ij)^k`. -/
noncomputable def angKappaE (a : ℕ) (f : ℤ[X]) (t s j l e : ℕ) : GaussianInt :=
  ∑ k ∈ Finset.range (t + 1),
    ((t.choose k * l.descFactorial (t - k) * s ^ (l - (t - k)) * a ^ (t - k) : ℕ) : GaussianInt) *
      ((redCoeff f k e : ℤ) : GaussianInt) * ijG j ^ k

/-- The Gaussian-integer polynomials `Q_{t,s,e}`. -/
noncomputable def angQ {J L : ℕ} (a : ℕ) (f : ℤ[X]) (c : Fin (J + 1) → Fin L → ℤ)
    (t s e : ℕ) : GaussianInt[X] :=
  ∑ j : Fin (J + 1), ∑ l : Fin L, C ((c j l : GaussianInt) * angKappaE a f t s j l e) *
    X ^ ((j : ℕ) * s)

/-- `Σ_e ϑ^e κ_e = a^t κ_{θi}`. -/
theorem sum_angKappaE {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) {a : ℕ}
    {θ : ℝ} {ϑ : ℂ} (hϑa : ϑ = a * θ) (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0)
    (t s j l : ℕ) :
    ∑ e : Fin m, ϑ ^ (e : ℕ) * ((angKappaE a f t s j l e : GaussianInt) : ℂ) =
      (a : ℂ) ^ t * angKappa ((θ : ℂ) * Complex.I) t s j l := by
  simp only [angKappaE, angKappa, map_sum, map_mul, map_pow, map_natCast, map_intCast,
    toComplex_ijG]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hs := sum_redCoeff hf hmf hϑ k
  have hsplit : (a : ℂ) ^ t = (a : ℂ) ^ (t - k) * (a : ℂ) ^ k := by
    rw [← pow_add]; congr 1; omega
  calc ∑ e : Fin m, ϑ ^ (e : ℕ) * ((((t.choose k * l.descFactorial (t - k) * s ^ (l - (t - k)) *
          a ^ (t - k) : ℕ) : ℂ)) * ((redCoeff f k e : ℤ) : ℂ) * ((j : ℂ) * Complex.I) ^ k)
      = (((t.choose k * l.descFactorial (t - k) * s ^ (l - (t - k)) * a ^ (t - k) : ℕ) : ℂ)) *
          ((j : ℂ) * Complex.I) ^ k * ∑ e : Fin m, ((redCoeff f k e : ℤ) : ℂ) * ϑ ^ (e : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = _ := by
        rw [hs, hϑa, hsplit]
        push_cast
        ring

/-- **Decomposition.** `a^t S_{t,s}(z) = Σ_e ϑ^e Q_{t,s,e}(z)`. -/
theorem eval_angS_eq_sum {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) {a : ℕ}
    {θ : ℝ} {ϑ : ℂ} (hϑa : ϑ = a * θ) (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) {J L : ℕ}
    (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) (z : ℂ) :
    (a : ℂ) ^ t * (angS ((θ : ℂ) * Complex.I) c t s).eval z =
      ∑ e : Fin m, ϑ ^ (e : ℕ) * ((angQ a f c t s e).map toComplex).eval z := by
  simp only [eval_angS, angQ, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
    map_X, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_mul, map_intCast,
    Polynomial.map_intCast, eval_intCast]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := sum_angKappaE hf hmf hϑa hϑ t s j l
  calc (a : ℂ) ^ t * ((c j l : ℂ) * angKappa ((θ : ℂ) * Complex.I) t s j l * z ^ ((j : ℕ) * s))
      = (c j l : ℂ) * z ^ ((j : ℕ) * s) * ((a : ℂ) ^ t * angKappa ((θ : ℂ) * Complex.I) t s j l) := by
        ring
    _ = (c j l : ℂ) * z ^ ((j : ℕ) * s) *
          ∑ e : Fin m, ϑ ^ (e : ℕ) * ((angKappaE a f t s j l e : GaussianInt) : ℂ) := by rw [this]
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

theorem norm_angKappaE_le {a : ℕ} {f : ℤ[X]} (hf : f.Monic) (hm : 1 ≤ f.natDegree) {F : ℝ}
    (hF0 : 0 ≤ F) (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) {t s j l h J L e : ℕ} (hs : s ≤ h)
    (hh : 1 ≤ h) (hj : j ≤ J) (hl : l ≤ L) :
    ‖((angKappaE a f t s j l e : GaussianInt) : ℂ)‖ ≤
      (h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ t := by
  simp only [angKappaE, map_sum, map_mul, map_pow, map_natCast, map_intCast, toComplex_ijG]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (t + 1),
      ‖(((t.choose k * l.descFactorial (t - k) * s ^ (l - (t - k)) * a ^ (t - k) : ℕ) : ℂ)) *
        ((redCoeff f k e : ℤ) : ℂ) * ((j : ℂ) * Complex.I) ^ k‖ ≤
        (h : ℝ) ^ L * ((J * (1 + F)) ^ k * ((a : ℝ) * L) ^ (t - k) * (t.choose k : ℝ)) := by
    intro k _
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_natCast, Complex.norm_intCast]
    push_cast
    have h1 : ((l.descFactorial (t - k) : ℕ) : ℝ) ≤ (L : ℝ) ^ (t - k) := by
      exact_mod_cast (Nat.descFactorial_le_pow l _).trans (Nat.pow_le_pow_left hl _)
    have h2 : (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ L := by
      calc (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ (l - (t - k)) :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) _
        _ ≤ (h : ℝ) ^ L := pow_le_pow_right₀ (by exact_mod_cast hh) (by omega)
    have h3 : (j : ℝ) ^ k ≤ (J : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hj) _
    have h4 : |((redCoeff f k e : ℤ) : ℝ)| ≤ (1 + F) ^ k := abs_redCoeff_le hf hm hF0 hF k e
    calc (t.choose k : ℝ) * (l.descFactorial (t - k) : ℝ) * (s : ℝ) ^ (l - (t - k)) *
          (a : ℝ) ^ (t - k) * |((redCoeff f k e : ℤ) : ℝ)| * (j : ℝ) ^ k
        ≤ (t.choose k : ℝ) * (L : ℝ) ^ (t - k) * (h : ℝ) ^ L * (a : ℝ) ^ (t - k) *
            (1 + F) ^ k * (J : ℝ) ^ k := by gcongr
      _ = (h : ℝ) ^ L * ((J * (1 + F)) ^ k * ((a : ℝ) * L) ^ (t - k) * (t.choose k : ℝ)) := by
          rw [mul_pow, mul_pow]; ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← add_pow]
  ring

theorem natDegree_angQ_le {J L : ℕ} (a : ℕ) (f : ℤ[X]) (c : Fin (J + 1) → Fin L → ℤ)
    (t s e : ℕ) : (angQ a f c t s e).natDegree ≤ J * s := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.isLt)

theorem norm_coeff_angQ_le {a : ℕ} {f : ℤ[X]} (hf : f.Monic) (hm : 1 ≤ f.natDegree) {F : ℝ}
    (hF0 : 0 ≤ F) (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) {J L h : ℕ} (c : Fin (J + 1) → Fin L → ℤ)
    {Cc : ℝ} (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc) {t s : ℕ} (hs : s ≤ h) (hh : 1 ≤ h) (e k : ℕ) :
    ‖(((angQ a f c t s e).coeff k : GaussianInt) : ℂ)‖ ≤
      (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ t)) := by
  have hcoeff : (((angQ a f c t s e).coeff k : GaussianInt) : ℂ) = ∑ j : Fin (J + 1),
      ∑ l : Fin L, if (j : ℕ) * s = k then
        (c j l : ℂ) * ((angKappaE a f t s j l e : GaussianInt) : ℂ) else 0 := by
    simp only [angQ, finsetSum_coeff, coeff_C_mul_X_pow, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [hcoeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin (J + 1), ‖∑ l : Fin L, if (j : ℕ) * s = k then
        (c j l : ℂ) * ((angKappaE a f t s j l e : GaussianInt) : ℂ) else 0‖
      ≤ ∑ _j : Fin (J + 1), ∑ _l : Fin L,
          Cc * ((h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ t) := by
        refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun l _ => ?_)
        have hCc : 0 ≤ Cc := (abs_nonneg _).trans (hc j l)
        split_ifs
        · rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul (hc j l) (norm_angKappaE_le hf hm hF0 hF hs hh
            (Nat.lt_succ_iff.mp j.isLt) l.isLt.le) (_root_.norm_nonneg _) hCc
        · rw [norm_zero]; positivity
    _ = (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ t)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end NLQCLean.Gelfond
