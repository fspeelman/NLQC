import NLQCLean.Arithmetic.GelfondSchwarz
import NLQCLean.Arithmetic.GelfondLiouville
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The auxiliary function of Gelfond's method for `e^i`

For integers `c_{jl}` (`j ≤ J`, `l < L`) put `F(z) = Σ c_{jl} z^l e^{ijz}`. Its derivatives at
integer points are values at `ζ = e^i` of explicit Gaussian-integer polynomials:
`F^{(t)}(s) = Q_{t,s}(ζ)`, `Q_{t,s} = Σ c_{jl} κ(t,s,j,l) X^{js}`. All analysis is done on
the polynomial truncations `F_D` (exponentials truncated at degree `D`), whose derivatives at
`s` converge to `Q_{t,s}(ζ)` and which are bounded by `Σ|c| R^L e^{JR}` on `|w| ≤ R`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt Filter Topology

/-- `j i` as a Gaussian integer. -/
def ijG (j : ℕ) : GaussianInt := ⟨0, j⟩

theorem toComplex_ijG (j : ℕ) : ((ijG j : GaussianInt) : ℂ) = j * Complex.I := by
  simp [ijG, toComplex_def']

/-- `κ(t,s,j,l) = Σ_{k ≤ t} C(t,k) (l)_{t-k} s^{l-(t-k)} (ij)^k`. -/
def kappa (t s j l : ℕ) : GaussianInt :=
  ∑ k ∈ Finset.range (t + 1),
    ((t.choose k * l.descFactorial (t - k) * s ^ (l - (t - k)) : ℕ) : GaussianInt) * ijG j ^ k

/-- The Gaussian-integer polynomials `Q_{t,s}`. -/
noncomputable def auxQ {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) : GaussianInt[X] :=
  ∑ j : Fin (J + 1), ∑ l : Fin L, C ((c j l : GaussianInt) * kappa t s j l) * X ^ ((j : ℕ) * s)

/-- The exponential truncated below degree `D`. -/
noncomputable def expPoly (D : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range D, C ((i.factorial : ℂ)⁻¹) * X ^ i

/-- The truncated auxiliary function. -/
noncomputable def auxF {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (D : ℕ) : ℂ[X] :=
  ∑ j : Fin (J + 1), ∑ l : Fin L,
    C (c j l : ℂ) * (X ^ (l : ℕ) * (expPoly D).comp (C ((j : ℂ) * Complex.I) * X))

/-! ### Derivatives -/

theorem coeff_expPoly (D m : ℕ) :
    (expPoly D).coeff m = if m < D then ((m.factorial : ℂ)⁻¹) else 0 := by
  rw [expPoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem derivative_expPoly (D : ℕ) : derivative (expPoly D) = expPoly (D - 1) := by
  ext m
  rw [coeff_derivative, coeff_expPoly, coeff_expPoly]
  by_cases hm : m + 1 < D
  · rw [ite_eq_left hm, ite_eq_left (by omega), Nat.factorial_succ]
    push_cast
    field_simp
  · rw [ite_eq_right hm, ite_eq_right (by omega), zero_mul]

theorem iterate_derivative_expPoly (D k : ℕ) :
    derivative^[k] (expPoly D) = expPoly (D - k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, derivative_expPoly]; rfl

theorem iterate_derivative_comp_C_mul_X (p : ℂ[X]) (a : ℂ) (k : ℕ) :
    derivative^[k] (p.comp (C a * X)) = C (a ^ k) * (derivative^[k] p).comp (C a * X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, derivative_comp, derivative_C_mul_X, iterate_derivative_C_mul,
      ih, Function.iterate_succ_apply]
    simp only [pow_succ, C_mul]
    ring

/-- Explicit derivatives of one term at a point. -/
theorem eval_iterate_derivative_term (D t l : ℕ) (a w : ℂ) :
    (derivative^[t] (X ^ l * (expPoly D).comp (C a * X))).eval w =
      ∑ k ∈ Finset.range (t + 1), ((t.choose k * l.descFactorial (t - k) : ℕ) : ℂ) *
        w ^ (l - (t - k)) * (a ^ k * (expPoly (D - k)).eval (a * w)) := by
  rw [iterate_derivative_mul, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_X_pow_eq_smul, iterate_derivative_comp_C_mul_X,
    iterate_derivative_expPoly]
  simp only [nsmul_eq_mul, eval_mul, eval_natCast, eval_smul, eval_pow, eval_X, eval_C, eval_comp,
    smul_eq_mul]
  push_cast
  ring

theorem eval_iterate_derivative_auxF {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (D t : ℕ) (w : ℂ) :
    (derivative^[t] (auxF c D)).eval w =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) *
        ∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          w ^ ((l : ℕ) - (t - k)) * (((j : ℂ) * Complex.I) ^ k *
            (expPoly (D - k)).eval ((j : ℂ) * Complex.I * w)) := by
  rw [auxF]
  simp only [iterate_derivative_sum, iterate_derivative_C_mul, eval_finsetSum, eval_mul, eval_C,
    eval_iterate_derivative_term]

/-! ### Convergence to `Q_{t,s}(ζ)` -/

theorem tendsto_eval_expPoly (w : ℂ) (k : ℕ) :
    Tendsto (fun D => (expPoly (D - k)).eval w) atTop (𝓝 (Complex.exp w)) := by
  have hsum : Tendsto (fun m => ∑ i ∈ Finset.range m, w ^ i / (i.factorial : ℂ)) atTop
      (𝓝 (Complex.exp w)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp w).tendsto_sum_nat
  have heval : ∀ m, (expPoly m).eval w = ∑ i ∈ Finset.range m, w ^ i / (i.factorial : ℂ) := by
    intro m
    simp only [expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [heval]
  exact hsum.comp (tendsto_sub_atTop_nat k)

theorem toComplex_kappa (t s j l : ℕ) :
    ((kappa t s j l : GaussianInt) : ℂ) = ∑ k ∈ Finset.range (t + 1),
      ((t.choose k * l.descFactorial (t - k) : ℕ) : ℂ) * (s : ℂ) ^ (l - (t - k)) *
        ((j : ℂ) * Complex.I) ^ k := by
  simp only [kappa, map_sum, map_mul, map_pow, map_natCast, toComplex_ijG]
  push_cast
  rfl

theorem eval_auxQ {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) (z : ℂ) :
    ((auxQ c t s).map toComplex).eval z =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) * ((kappa t s j l : GaussianInt) : ℂ) *
        z ^ ((j : ℕ) * s) := by
  simp only [auxQ, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_mul, map_intCast,
    Polynomial.map_intCast, eval_intCast]

/-- **Convergence.** `F_D^{(t)}(s) → Q_{t,s}(e^i)`. -/
theorem tendsto_auxF_derivative {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) :
    Tendsto (fun D => (derivative^[t] (auxF c D)).eval (s : ℂ)) atTop
      (𝓝 (((auxQ c t s).map toComplex).eval (Complex.exp Complex.I))) := by
  simp_rw [eval_iterate_derivative_auxF, eval_auxQ, toComplex_kappa]
  have hlim : (fun j : Fin (J + 1) => ∑ l : Fin L, (c j l : ℂ) *
        (∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * ((j : ℂ) * Complex.I) ^ k) *
          Complex.exp Complex.I ^ ((j : ℕ) * s)) =
      fun j => ∑ l : Fin L, (c j l : ℂ) *
        ∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * (((j : ℂ) * Complex.I) ^ k *
            Complex.exp ((j : ℂ) * Complex.I * s)) := by
    funext j
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show Complex.exp ((j : ℂ) * Complex.I * s) = Complex.exp Complex.I ^ ((j : ℕ) * s) by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [show (∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) *
        (∑ k ∈ Finset.range (t + 1), ((t.choose k * (l : ℕ).descFactorial (t - k) : ℕ) : ℂ) *
          (s : ℂ) ^ ((l : ℕ) - (t - k)) * ((j : ℂ) * Complex.I) ^ k) *
          Complex.exp Complex.I ^ ((j : ℕ) * s)) = _ from congrArg (fun f => ∑ j, f j) hlim]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun l _ => ?_
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_)
  exact Tendsto.const_mul _ (tendsto_eval_expPoly _ k)

/-! ### Size bounds -/

theorem norm_eval_expPoly_le (D : ℕ) (w : ℂ) : ‖(expPoly D).eval w‖ ≤ Real.exp ‖w‖ := by
  simp only [expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range D, ‖((i.factorial : ℂ))⁻¹ * w ^ i‖
      = ∑ i ∈ Finset.range D, ‖w‖ ^ i / i.factorial := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow]; ring
    _ ≤ Real.exp ‖w‖ := Real.sum_le_exp_of_nonneg (_root_.norm_nonneg _) D

/-- **Growth.** -/
theorem norm_eval_auxF_le {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ} (hCc : 0 ≤ Cc)
    (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc) (D : ℕ) {R : ℝ} (hR : 1 ≤ R) {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖(auxF c D).eval w‖ ≤ (J + 1) * L * Cc * R ^ L * Real.exp (J * R) := by
  simp only [auxF, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ (j : Fin (J + 1)) (l : Fin L),
      ‖(c j l : ℂ) * (w ^ (l : ℕ) * (expPoly D).eval ((j : ℂ) * Complex.I * w))‖ ≤
        Cc * (R ^ L * Real.exp (J * R)) := by
    intro j l
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_intCast]
    refine mul_le_mul (hc j l) (mul_le_mul ?_ ?_ (_root_.norm_nonneg _) (by positivity))
      (by positivity) hCc
    · calc ‖w‖ ^ (l : ℕ) ≤ R ^ (l : ℕ) := pow_le_pow_left₀ (_root_.norm_nonneg _) hw _
        _ ≤ R ^ L := pow_le_pow_right₀ hR l.isLt.le
    · refine (norm_eval_expPoly_le D _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast]
      have hj : (j : ℝ) ≤ J := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
      exact mul_le_mul hj hw (_root_.norm_nonneg _) (by positivity)
  calc ∑ j : Fin (J + 1), ‖∑ l : Fin L, (c j l : ℂ) *
        (w ^ (l : ℕ) * (expPoly D).eval ((j : ℂ) * Complex.I * w))‖
      ≤ ∑ _j : Fin (J + 1), ∑ _l : Fin L, Cc * (R ^ L * Real.exp (J * R)) :=
        Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm j l)
    _ = (J + 1) * L * Cc * R ^ L * Real.exp (J * R) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem norm_kappa_le {t s j l h J L : ℕ} (hs : s ≤ h) (hh : 1 ≤ h) (hj : j ≤ J) (hl : l ≤ L) :
    ‖((kappa t s j l : GaussianInt) : ℂ)‖ ≤ (h : ℝ) ^ L * ((J : ℝ) + L) ^ t := by
  rw [toComplex_kappa]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (t + 1),
      ‖((t.choose k * l.descFactorial (t - k) : ℕ) : ℂ) * (s : ℂ) ^ (l - (t - k)) *
        ((j : ℂ) * Complex.I) ^ k‖ ≤
        (h : ℝ) ^ L * ((J : ℝ) ^ k * (L : ℝ) ^ (t - k) * (t.choose k : ℝ)) := by
    intro k _
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast]
    push_cast
    have h1 : ((l.descFactorial (t - k) : ℕ) : ℝ) ≤ (L : ℝ) ^ (t - k) := by
      exact_mod_cast (Nat.descFactorial_le_pow l _).trans (Nat.pow_le_pow_left hl _)
    have h2 : (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ L := by
      calc (s : ℝ) ^ (l - (t - k)) ≤ (h : ℝ) ^ (l - (t - k)) :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) _
        _ ≤ (h : ℝ) ^ L := pow_le_pow_right₀ (by exact_mod_cast hh) (by omega)
    have h3 : (j : ℝ) ^ k ≤ (J : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hj) _
    calc (t.choose k : ℝ) * (l.descFactorial (t - k) : ℝ) * (s : ℝ) ^ (l - (t - k)) * (j : ℝ) ^ k
        ≤ (t.choose k : ℝ) * (L : ℝ) ^ (t - k) * (h : ℝ) ^ L * (J : ℝ) ^ k := by gcongr
      _ = (h : ℝ) ^ L * ((J : ℝ) ^ k * (L : ℝ) ^ (t - k) * (t.choose k : ℝ)) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← add_pow]

theorem natDegree_auxQ_le {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (t s : ℕ) :
    (auxQ c t s).natDegree ≤ J * s := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.isLt)

theorem norm_coeff_auxQ_le {J L h : ℕ} (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ}
    (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc) {t s : ℕ} (hs : s ≤ h) (hh : 1 ≤ h) (m : ℕ) :
    ‖(((auxQ c t s).coeff m : GaussianInt) : ℂ)‖ ≤
      (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ t)) := by
  have hcoeff : (((auxQ c t s).coeff m : GaussianInt) : ℂ) = ∑ j : Fin (J + 1), ∑ l : Fin L,
      if (j : ℕ) * s = m then (c j l : ℂ) * ((kappa t s j l : GaussianInt) : ℂ) else 0 := by
    simp only [auxQ, finsetSum_coeff, coeff_C_mul_X_pow, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [hcoeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin (J + 1), ‖∑ l : Fin L, if (j : ℕ) * s = m then
        (c j l : ℂ) * ((kappa t s j l : GaussianInt) : ℂ) else 0‖
      ≤ ∑ _j : Fin (J + 1), ∑ _l : Fin L, Cc * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ t) := by
        refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun l _ => ?_)
        have hCc : 0 ≤ Cc := (abs_nonneg _).trans (hc j l)
        split_ifs
        · rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul (hc j l) (norm_kappa_le hs hh (Nat.lt_succ_iff.mp j.isLt) l.isLt.le)
            (_root_.norm_nonneg _) hCc
        · rw [norm_zero]; positivity
    _ = (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ t)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem toComplex_kappa_zero (t j l : ℕ) :
    ((kappa t 0 j l : GaussianInt) : ℂ) = (t.descFactorial l : ℂ) * ((j : ℂ) * Complex.I) ^ (t - l) := by
  rw [toComplex_kappa]
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

theorem auxQ_zero {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ) (t : ℕ) :
    auxQ c t 0 = C (∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : GaussianInt) * kappa t 0 j l) := by
  simp [auxQ, map_sum]

end NLQCLean.Gelfond
