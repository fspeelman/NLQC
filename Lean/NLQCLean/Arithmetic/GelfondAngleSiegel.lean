import NLQCLean.Arithmetic.GelfondAngleAuxiliary

/-!
# The Siegel step of Gelfond's method for `e^{iθ}`

For an irreducible `G ∈ ℤ[i][X]` of degree `g ≥ 1` with coefficients at most `a_G`, Siegel's
lemma gives integers `c_{jl}`, not all zero, with `G ∣ Q_{t,s,e}` for all `t < T₀`, `s < h`,
`e < m`, as long as `2 · 2 T₀ h g m ≤ (J+1)L`. The linearization is the one of the case `θ = 1`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt
open scoped Matrix

/-- Matrix entries: the condition coefficient of `c_{jl}`. -/
noncomputable def angEntry (G : GaussianInt[X]) (a : ℕ) (f : ℤ[X]) (q t s r j l e : ℕ) :
    GaussianInt :=
  remFun G q r (C (angKappaE a f t s j l e) * X ^ (j * s))

theorem remFun_angQ (G : GaussianInt[X]) (q r : ℕ) {J L : ℕ} (a : ℕ) (f : ℤ[X])
    (c : Fin (J + 1) → Fin L → ℤ) (t s e : ℕ) : remFun G q r (angQ a f c t s e) =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : GaussianInt) * angEntry G a f q t s r j l e := by
  have : angQ a f c t s e = ∑ j : Fin (J + 1), ∑ l : Fin L,
      (c j l : GaussianInt) • (C (angKappaE a f t s j l e) * X ^ ((j : ℕ) * s)) := by
    simp only [angQ, smul_eq_C_mul, C_mul, mul_assoc]
  rw [this, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul, angEntry]

theorem norm_remFun_C_mul_X_pow_le {G : GaussianInt[X]} (hdeg : 0 < G.natDegree) {aG : ℝ}
    (ha : 1 ≤ aG) (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ aG) {q r n : ℕ} (hn : n ≤ q)
    (κ : GaussianInt) :
    ‖((remFun G q r (C κ * X ^ n) : GaussianInt) : ℂ)‖ ≤
      ‖(κ : ℂ)‖ * aG ^ q * (1 + aG ^ G.natDegree) ^ q := by
  have hG0 : G ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; exact lt_irrefl _ hdeg
  set g := G.natDegree
  set Gs := integralNormalization G
  have hGs : Gs.Monic := monic_integralNormalization hG0
  have hGsdeg : Gs.natDegree = g := natDegree_integralNormalization
  have hentry : remFun G q r (C κ * X ^ n) =
      (κ * G.leadingCoeff ^ (q - n)) * ((X ^ n : GaussianInt[X]) %ₘ Gs).coeff r := by
    simp only [remFun, LinearMap.coe_comp, Function.comp_apply, starPoly_C_mul_X_pow _ _ hn]
    change ((C (κ * G.leadingCoeff ^ (q - n)) * X ^ n) %ₘ Gs).coeff r = _
    rw [← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]
  have hlc : ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ≤ aG := hcoeff _
  have h1 : ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (q - n) ≤ aG ^ q :=
    (pow_le_pow_left₀ (_root_.norm_nonneg _) hlc _).trans (pow_le_pow_right₀ ha (Nat.sub_le _ _))
  have hmap : (((X ^ n : GaussianInt[X]) %ₘ Gs).coeff r : ℂ) =
      (((X ^ n : ℂ[X]) %ₘ (Gs.map toComplex)).coeff r) := by
    rw [← coeff_map, map_modByMonic _ hGs, Polynomial.map_pow, map_X]
  have hGsc : (Gs.map toComplex).Monic := hGs.map _
  have hGscdeg : (Gs.map toComplex).natDegree = g := by
    rw [natDegree_map_eq_of_injective toComplex_injective, hGsdeg]
  have h2 : ‖(((X ^ n : GaussianInt[X]) %ₘ Gs).coeff r : ℂ)‖ ≤ (1 + aG ^ g) ^ q := by
    rw [hmap]
    refine (norm_coeff_X_pow_modByMonic_le hGsc (by omega) (by positivity) ?_ _ r).trans
      (pow_le_pow_right₀ (by linarith [one_le_pow₀ (n := g) ha]) hn)
    intro i hi
    rw [hGscdeg] at hi
    rw [coeff_map, integralNormalization_coeff, ite_eq_right]
    · rw [map_mul, map_pow, norm_mul, norm_pow]
      calc ‖((G.coeff i : GaussianInt) : ℂ)‖ * ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (g - 1 - i)
          ≤ aG * aG ^ (g - 1 - i) := mul_le_mul (hcoeff i)
            (pow_le_pow_left₀ (_root_.norm_nonneg _) hlc _) (by positivity) (by linarith)
        _ = aG ^ (g - i) := by rw [← pow_succ']; congr 1; omega
        _ ≤ aG ^ g := pow_le_pow_right₀ ha (Nat.sub_le _ _)
    · rw [degree_eq_natDegree hG0]; exact_mod_cast hi.ne'
  rw [hentry, map_mul, map_mul, map_pow, norm_mul, norm_mul, norm_pow]
  calc ‖(κ : ℂ)‖ * ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (q - n) *
        ‖(((X ^ n : GaussianInt[X]) %ₘ Gs).coeff r : ℂ)‖
      ≤ ‖(κ : ℂ)‖ * aG ^ q * (1 + aG ^ g) ^ q := by gcongr

/-- The coefficient bound produced by Siegel's lemma. -/
noncomputable def angSiegelBound (G : GaussianInt[X]) (aG : ℝ) (a : ℕ) (F : ℝ)
    (J L h T₀ : ℕ) : ℝ :=
  ((J + 1) * L : ℕ) * ((h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ T₀ * aG ^ (J * h) *
    (1 + aG ^ G.natDegree) ^ (J * h))

section Siegel

attribute [local instance] Matrix.seminormedAddCommGroup

/-- **Siegel step.** -/
theorem exists_siegel_coefficients_angle {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {aG : ℝ} (ha : 1 ≤ aG) (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ aG)
    {a : ℕ} (ha1 : 1 ≤ a) {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m)
    (hm : 1 ≤ m) {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F)
    {J L h T₀ : ℕ} (hh : 1 ≤ h) (hT₀ : 1 ≤ T₀)
    (hcount : 2 * (T₀ * h * G.natDegree * m * 2) ≤ (J + 1) * L) :
    ∃ c : Fin (J + 1) → Fin L → ℤ, c ≠ 0 ∧
      (∀ j l, |(c j l : ℝ)| ≤ angSiegelBound G aG a F J L h T₀) ∧
      ∀ t < T₀, ∀ s < h, ∀ e < m, G ∣ angQ a f c t s e := by
  classical
  set g := G.natDegree with hg
  set q := J * h with hq
  set Abd : ℝ := (h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ T₀ * aG ^ q * (1 + aG ^ g) ^ q
    with hAbd
  have hm0 : 0 < T₀ * h * g * m * 2 := by positivity
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, mul_zero] at hcount; omega
    · exact h0
  have hbase1 : (1 : ℝ) ≤ (a : ℝ) * L + J * (1 + F) := by
    have h1 : (1 : ℝ) ≤ (a : ℝ) * L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast ha1)
      (by exact_mod_cast hL1)
    have h2 : (0 : ℝ) ≤ J * (1 + F) := by positivity
    linarith
  have hAbd1 : 1 ≤ Abd := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) ^ L := one_le_pow₀ (by exact_mod_cast hh)
    have h2 : (1 : ℝ) ≤ ((a : ℝ) * L + J * (1 + F)) ^ T₀ := one_le_pow₀ hbase1
    have h3 : (1 : ℝ) ≤ aG ^ q := one_le_pow₀ ha
    have h4 : (1 : ℝ) ≤ (1 + aG ^ g) ^ q := one_le_pow₀ (by linarith [one_le_pow₀ (n := g) ha])
    rw [hAbd]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4
  let A : Matrix (Fin T₀ × Fin h × Fin g × Fin m × Fin 2) (Fin (J + 1) × Fin L) ℤ := fun i k =>
    if i.2.2.2.2 = 0 then (angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1).re
    else (angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1).im
  have hentry : ∀ i k, ‖A i k‖ ≤ Abd := by
    intro i k
    have hjs : (k.1 : ℕ) * i.2.1 ≤ q :=
      Nat.mul_le_mul (Nat.lt_succ_iff.mp k.1.isLt) i.2.1.isLt.le
    have hE := norm_remFun_C_mul_X_pow_le hdeg ha hcoeff (r := i.2.2.1) hjs
      (angKappaE a f i.1 i.2.1 k.1 k.2 i.2.2.2.1)
    have hK := norm_angKappaE_le (a := a) hf (hmf ▸ hm) hF0 hF (t := i.1) (j := k.1) (l := k.2)
      (e := i.2.2.2.1) (J := J) (L := L) i.2.1.isLt.le hh (Nat.lt_succ_iff.mp k.1.isLt)
      k.2.isLt.le
    have hKt : ((a : ℝ) * L + J * (1 + F)) ^ (i.1 : ℕ) ≤ ((a : ℝ) * L + J * (1 + F)) ^ T₀ :=
      pow_le_pow_right₀ hbase1 i.1.isLt.le
    have hEb : ‖((angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1 : GaussianInt) : ℂ)‖ ≤
        Abd := by
      refine hE.trans ?_
      rw [hAbd]
      gcongr
      exact hK.trans (mul_le_mul_of_nonneg_left hKt (by positivity))
    simp only [A, Int.norm_eq_abs]
    split_ifs
    · rw [← Int.cast_abs]
      calc ((|(angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1).re| : ℤ) : ℝ)
          = |((angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1 : GaussianInt) : ℂ).re| := by
            rw [← intCast_re]; push_cast; rfl
        _ ≤ Abd := (Complex.abs_re_le_norm _).trans hEb
    · rw [← Int.cast_abs]
      calc ((|(angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1).im| : ℤ) : ℝ)
          = |((angEntry G a f q i.1 i.2.1 i.2.2.1 k.1 k.2 i.2.2.2.1 : GaussianInt) : ℂ).im| := by
            rw [← intCast_im]; push_cast; rfl
        _ ≤ Abd := (Complex.abs_im_le_norm _).trans hEb
  have hA : ‖A‖ ≤ Abd := (Matrix.norm_le_iff (by linarith)).mpr hentry
  have hcard_rows : Fintype.card (Fin T₀ × Fin h × Fin g × Fin m × Fin 2) =
      T₀ * h * g * m * 2 := by
    simp [Fintype.card_prod]; ring
  have hcard_cols : Fintype.card (Fin (J + 1) × Fin L) = (J + 1) * L := by
    simp [Fintype.card_prod]
  have hmn : Fintype.card (Fin T₀ × Fin h × Fin g × Fin m × Fin 2) <
      Fintype.card (Fin (J + 1) × Fin L) := by
    rw [hcard_rows, hcard_cols]; omega
  obtain ⟨c', hc'0, hAc', hc'norm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hmn (by rw [hcard_rows]; exact hm0)
  rw [hcard_rows, hcard_cols] at hc'norm
  refine ⟨fun j l => c' (j, l), ?_, ?_, ?_⟩
  · intro h0
    apply hc'0
    funext k
    exact congrFun (congrFun h0 k.1) k.2
  · intro j l
    have hn1 : (1 : ℝ) ≤ (((J + 1) * L : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hb1 : 1 ≤ (((J + 1) * L : ℕ) : ℝ) * max 1 ‖A‖ :=
      one_le_mul_of_one_le_of_one_le hn1 (le_max_left _ _)
    have hexp : ((T₀ * h * g * m * 2 : ℕ) : ℝ) /
        ((((J + 1) * L : ℕ) : ℝ) - ((T₀ * h * g * m * 2 : ℕ) : ℝ)) ≤ 1 := by
      have h2m : (2 * (T₀ * h * g * m * 2 : ℕ) : ℝ) ≤ (((J + 1) * L : ℕ) : ℝ) := by
        exact_mod_cast hcount
      have hm' : (0 : ℝ) < ((T₀ * h * g * m * 2 : ℕ) : ℝ) := by exact_mod_cast hm0
      have hpos : (0 : ℝ) < (((J + 1) * L : ℕ) : ℝ) - ((T₀ * h * g * m * 2 : ℕ) : ℝ) := by
        linarith
      rw [div_le_one hpos]; linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le hb1 hexp
    rw [Real.rpow_one] at hrpow
    calc |(c' (j, l) : ℝ)| = ‖c' (j, l)‖ := by rw [Int.norm_eq_abs]
      _ ≤ ‖c'‖ := norm_le_pi_norm c' (j, l)
      _ ≤ _ := hc'norm
      _ ≤ (((J + 1) * L : ℕ) : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ (((J + 1) * L : ℕ) : ℝ) * Abd :=
          mul_le_mul_of_nonneg_left (max_le hAbd1 hA) (by positivity)
      _ = angSiegelBound G aG a F J L h T₀ := by rw [angSiegelBound, hAbd]
  · intro t ht s hs e he
    have hG0 : G ≠ 0 := hG.ne_zero
    set Gs := integralNormalization G
    have hGs : Gs.Monic := monic_integralNormalization hG0
    have hGs1 : Gs ≠ 1 := fun h1 => by
      have := natDegree_integralNormalization (p := G)
      rw [show integralNormalization G = Gs from rfl, h1, natDegree_one] at this
      omega
    have hQdeg : (angQ a f (fun j l => c' (j, l)) t s e).natDegree ≤ q :=
      (natDegree_angQ_le _ _ _ t s e).trans (Nat.mul_le_mul_left _ hs.le)
    refine dvd_of_dvd_starPoly hG hdeg hQdeg ((modByMonic_eq_zero_iff_dvd hGs).mp ?_)
    refine Polynomial.ext fun r => ?_
    rw [coeff_zero]
    by_cases hr : g ≤ r
    · refine coeff_eq_zero_of_natDegree_lt ?_
      have := natDegree_modByMonic_lt
        (starPoly G.leadingCoeff q (angQ a f (fun j l => c' (j, l)) t s e)) hGs hGs1
      rw [natDegree_integralNormalization] at this
      omega
    replace hr := not_le.mp hr
    have hrem : (starPoly G.leadingCoeff q (angQ a f (fun j l => c' (j, l)) t s e) %ₘ Gs).coeff r =
        remFun G q r (angQ a f (fun j l => c' (j, l)) t s e) := rfl
    rw [hrem, remFun_angQ]
    have hrow : ∀ b : Fin 2, (A *ᵥ c') (⟨t, ht⟩, ⟨s, hs⟩, ⟨r, hr⟩, ⟨e, he⟩, b) = 0 := fun b => by
      rw [hAc']; rfl
    apply Zsqrtd.ext
    · have h0 := hrow 0
      simp only [Matrix.mulVec, dotProduct, A, ite_eq_left rfl, Fintype.sum_prod_type] at h0
      rw [Zsqrtd.re_zero, ← Finset.sum_product', re_sum_intCast_mul]
      rw [← Finset.sum_product'] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · have h1 := hrow 1
      simp only [Matrix.mulVec, dotProduct, A, ite_eq_right one_ne_zero,
        Fintype.sum_prod_type] at h1
      rw [Zsqrtd.im_zero, ← Finset.sum_product', im_sum_intCast_mul]
      rw [← Finset.sum_product'] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Siegel

end NLQCLean.Gelfond
