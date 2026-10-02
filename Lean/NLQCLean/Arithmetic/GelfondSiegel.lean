import NLQCLean.Arithmetic.GelfondAuxiliary
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# The Siegel step of Gelfond's method

For an irreducible `G ∈ ℤ[i][X]` of degree `g ≥ 1` with coefficients at most `a`, Siegel's lemma
gives integers `c_{jl}`, not all zero, of size at most `(J+1)L · A`, with `G ∣ Q_{t,s}` for all
`t < T₀`, `s < h`, as long as `2 T₀ h g · 2 ≤ (J+1)L`. Divisibility is linearized by the monic
transform `G* = lc^{g-1} G(X/lc)`: the remainder of `lc^q Q(X/lc)` modulo `G*` is linear in `c`,
its real and imaginary parts give the integer equations, and the coefficients of `X^k mod G*`
grow at most like `(1 + a^g)^k`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt
open scoped Matrix

/-! ### Remainders modulo a monic polynomial -/

theorem norm_coeff_X_pow_modByMonic_le {P : ℂ[X]} (hP : P.Monic) (hg : 1 ≤ P.natDegree)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ α) (k r : ℕ) :
    ‖((X ^ k : ℂ[X]) %ₘ P).coeff r‖ ≤ (1 + α) ^ k := by
  set g := P.natDegree with hgdef
  have hP1 : P ≠ 1 := fun h => by rw [h, natDegree_one] at hgdef; omega
  have hdegP : P.degree = (g : WithBot ℕ) := degree_eq_natDegree hP.ne_zero
  induction k generalizing r with
  | zero =>
    rw [pow_zero, (modByMonic_eq_self_iff hP).mpr (by rw [degree_one, hdegP]; exact_mod_cast hg)]
    rw [coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    set R := (X ^ k : ℂ[X]) %ₘ P with hRdef
    have hR : R.natDegree < g := natDegree_modByMonic_lt _ hP hP1
    have hstep : (X ^ (k + 1) : ℂ[X]) %ₘ P = (X * R) %ₘ P := by
      refine modByMonic_eq_of_dvd_sub hP ⟨X * (X ^ k /ₘ P), ?_⟩
      have := modByMonic_add_div (X ^ k : ℂ[X]) P
      rw [← hRdef] at this
      have h' : (X ^ k : ℂ[X]) - R = P * (X ^ k /ₘ P) := (eq_sub_of_add_eq' this).symm
      calc (X ^ (k + 1) : ℂ[X]) - X * R = X * (X ^ k - R) := by ring
        _ = X * (P * (X ^ k /ₘ P)) := by rw [h']
        _ = P * (X * (X ^ k /ₘ P)) := by ring
    set c := R.coeff (g - 1) with hc
    have hdeg : (X * R - C c * P).degree < P.degree := by
      rw [hdegP, degree_lt_iff_coeff_zero]
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases eq_or_lt_of_le hm with heq | hlt
      · have : m' = g - 1 := by omega
        rw [this, ← hc, show g - 1 + 1 = g by omega, hP.coeff_natDegree, mul_one, sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < m'),
          coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m' + 1), mul_zero, sub_zero]
    have hrem : (X * R) %ₘ P = X * R - C c * P :=
      (div_modByMonic_unique (C c) (X * R - C c * P) hP ⟨by ring, hdeg⟩).2
    rw [hstep, hrem]
    by_cases hr : g ≤ r
    · have := (degree_lt_iff_coeff_zero _ _).mp (hdegP ▸ hdeg) r (by exact_mod_cast hr)
      rw [this, norm_zero]; positivity
    replace hr := not_le.mp hr
    rw [coeff_sub, coeff_C_mul]
    have hXR : ‖(X * R).coeff r‖ ≤ (1 + α) ^ k := by
      rcases r with _ | r
      · rw [coeff_X_mul_zero, norm_zero]; positivity
      · rw [coeff_X_mul]; exact ih r
    calc ‖(X * R).coeff r - c * P.coeff r‖ ≤ ‖(X * R).coeff r‖ + ‖c‖ * ‖P.coeff r‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ (1 + α) ^ k + (1 + α) ^ k * α :=
          add_le_add hXR (mul_le_mul (ih _) (hα r hr) (_root_.norm_nonneg _) (by positivity))
      _ = (1 + α) ^ (k + 1) := by ring

/-! ### The monic transform -/

/-- `p ↦ Σ_{k ≤ q} p_k lc^{q-k} X^k`, i.e. `lc^q p(X/lc)`. -/
noncomputable def starPoly (lc : GaussianInt) (q : ℕ) : GaussianInt[X] →ₗ[GaussianInt] GaussianInt[X] where
  toFun p := ∑ k ∈ Finset.range (q + 1), C (p.coeff k * lc ^ (q - k)) * X ^ k
  map_add' p p' := by
    simp only [coeff_add, add_mul, C_add, ← Finset.sum_add_distrib]
  map_smul' a p := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_smul, smul_eq_C_mul, smul_eq_mul, C_mul, C_mul, C_mul]
    ring

theorem starPoly_comp (lc : GaussianInt) {q : ℕ} {p : GaussianInt[X]} (hp : p.natDegree ≤ q) :
    (starPoly lc q p).comp (C lc * X) = C (lc ^ q) * p := by
  conv_rhs => rw [as_sum_range' p (q + 1) (Nat.lt_succ_of_le hp)]
  simp only [starPoly, LinearMap.coe_mk, AddHom.coe_mk, sum_comp, mul_comp, C_comp, X_pow_comp,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← C_mul_X_pow_eq_monomial, mul_pow, ← C_pow]
  calc C (p.coeff k * lc ^ (q - k)) * (C (lc ^ k) * X ^ k)
      = C (p.coeff k * (lc ^ (q - k) * lc ^ k)) * X ^ k := by rw [C_mul, C_mul, C_mul]; ring
    _ = C (lc ^ q) * (C (p.coeff k) * X ^ k) := by
        rw [← pow_add, Nat.sub_add_cancel hk', C_mul]; ring

theorem integralNormalization_comp (G : GaussianInt[X]) (h : 1 ≤ G.natDegree) :
    (integralNormalization G).comp (C G.leadingCoeff * X) =
      C (G.leadingCoeff ^ (G.natDegree - 1)) * G := by
  have := integralNormalization_eval₂_leadingCoeff_mul h (C : GaussianInt →+* GaussianInt[X]) X
  rw [eval₂_C_X, ← C_pow] at this
  exact this

theorem dvd_of_dvd_starPoly {G p : GaussianInt[X]} (hG : Irreducible G) (hdeg : 0 < G.natDegree)
    {q : ℕ} (hp : p.natDegree ≤ q)
    (h : integralNormalization G ∣ starPoly G.leadingCoeff q p) : G ∣ p := by
  have h1 := map_dvd (Polynomial.compRingHom (C G.leadingCoeff * X)) h
  simp only [coe_compRingHom_apply] at h1
  rw [integralNormalization_comp G hdeg, starPoly_comp _ hp] at h1
  have h2 : G ∣ C (G.leadingCoeff ^ q) * p := (dvd_mul_left G _).trans h1
  have hprim := hG.isPrimitive hdeg.ne'
  refine hprim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing GaussianInt) ?_
  have h3 := map_dvd (Polynomial.mapRingHom (algebraMap GaussianInt (FractionRing GaussianInt))) h2
  simp only [coe_mapRingHom, Polynomial.map_mul, map_C] at h3
  have hu : IsUnit (C ((algebraMap GaussianInt (FractionRing GaussianInt)) (G.leadingCoeff ^ q)) :
      (FractionRing GaussianInt)[X]) := by
    refine isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [map_pow]
    exact pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (leadingCoeff_ne_zero.mpr hG.ne_zero))
  exact (hu.dvd_mul_left).mp h3

/-! ### The linear conditions -/

/-- The `r`-th coefficient of the remainder of the monic transform. -/
noncomputable def remFun (G : GaussianInt[X]) (q r : ℕ) : GaussianInt[X] →ₗ[GaussianInt] GaussianInt :=
  (lcoeff GaussianInt r).comp ((modByMonicHom (integralNormalization G)).comp
    (starPoly G.leadingCoeff q))

/-- Matrix entries: the condition coefficient of `c_{jl}`. -/
noncomputable def entryG (G : GaussianInt[X]) (q t s r j l : ℕ) : GaussianInt :=
  remFun G q r (C (kappa t s j l) * X ^ (j * s))

theorem remFun_auxQ (G : GaussianInt[X]) (q r : ℕ) {J L : ℕ} (c : Fin (J + 1) → Fin L → ℤ)
    (t s : ℕ) : remFun G q r (auxQ c t s) =
      ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : GaussianInt) * entryG G q t s r j l := by
  have : auxQ c t s = ∑ j : Fin (J + 1), ∑ l : Fin L,
      (c j l : GaussianInt) • (C (kappa t s j l) * X ^ ((j : ℕ) * s)) := by
    simp only [auxQ, smul_eq_C_mul, C_mul, mul_assoc]
  rw [this, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul, entryG]

theorem starPoly_C_mul_X_pow (lc κ : GaussianInt) {q n : ℕ} (hn : n ≤ q) :
    starPoly lc q (C κ * X ^ n) = C (κ * lc ^ (q - n)) * X ^ n := by
  simp only [starPoly, LinearMap.coe_mk, AddHom.coe_mk, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · rw [ite_eq_left rfl]
  · intro k _ hk; rw [ite_eq_right hk, zero_mul, C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) h

theorem norm_entryG_le {G : GaussianInt[X]} (hdeg : 0 < G.natDegree) {a : ℝ} (ha : 1 ≤ a)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ a) {q t s r j l : ℕ} (hjs : j * s ≤ q) :
    ‖((entryG G q t s r j l : GaussianInt) : ℂ)‖ ≤
      ‖((kappa t s j l : GaussianInt) : ℂ)‖ * a ^ q * (1 + a ^ G.natDegree) ^ q := by
  have hG0 : G ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; exact lt_irrefl _ hdeg
  set g := G.natDegree
  set Gs := integralNormalization G
  have hGs : Gs.Monic := monic_integralNormalization hG0
  have hGsdeg : Gs.natDegree = g := natDegree_integralNormalization
  have hentry : entryG G q t s r j l =
      (kappa t s j l * G.leadingCoeff ^ (q - j * s)) * ((X ^ (j * s) : GaussianInt[X]) %ₘ Gs).coeff r := by
    simp only [entryG, remFun, LinearMap.coe_comp, Function.comp_apply, starPoly_C_mul_X_pow _ _ hjs]
    change ((C (kappa t s j l * G.leadingCoeff ^ (q - j * s)) * X ^ (j * s)) %ₘ Gs).coeff r = _
    rw [← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]
  have hlc : ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ≤ a := hcoeff _
  have h1 : ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (q - j * s) ≤ a ^ q :=
    (pow_le_pow_left₀ (_root_.norm_nonneg _) hlc _).trans (pow_le_pow_right₀ ha (Nat.sub_le _ _))
  have hmap : (((X ^ (j * s) : GaussianInt[X]) %ₘ Gs).coeff r : ℂ) =
      (((X ^ (j * s) : ℂ[X]) %ₘ (Gs.map toComplex)).coeff r) := by
    rw [← coeff_map, map_modByMonic _ hGs, Polynomial.map_pow, map_X]
  have hGsc : (Gs.map toComplex).Monic := hGs.map _
  have hGscdeg : (Gs.map toComplex).natDegree = g := by
    rw [natDegree_map_eq_of_injective toComplex_injective, hGsdeg]
  have h2 : ‖(((X ^ (j * s) : GaussianInt[X]) %ₘ Gs).coeff r : ℂ)‖ ≤ (1 + a ^ g) ^ q := by
    rw [hmap]
    refine (norm_coeff_X_pow_modByMonic_le hGsc (by omega) (by positivity) ?_ _ r).trans
      (pow_le_pow_right₀ (by linarith [one_le_pow₀ (n := g) ha]) hjs)
    intro i hi
    rw [hGscdeg] at hi
    rw [coeff_map, integralNormalization_coeff, ite_eq_right]
    · rw [map_mul, map_pow, norm_mul, norm_pow]
      calc ‖((G.coeff i : GaussianInt) : ℂ)‖ * ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (g - 1 - i)
          ≤ a * a ^ (g - 1 - i) := mul_le_mul (hcoeff i)
            (pow_le_pow_left₀ (_root_.norm_nonneg _) hlc _) (by positivity) (by linarith)
        _ = a ^ (g - i) := by rw [← pow_succ']; congr 1; omega
        _ ≤ a ^ g := pow_le_pow_right₀ ha (Nat.sub_le _ _)
    · rw [degree_eq_natDegree hG0]; exact_mod_cast hi.ne'
  rw [hentry, map_mul, map_mul, map_pow, norm_mul, norm_mul, norm_pow]
  calc ‖((kappa t s j l : GaussianInt) : ℂ)‖ * ‖((G.leadingCoeff : GaussianInt) : ℂ)‖ ^ (q - j * s) *
        ‖(((X ^ (j * s) : GaussianInt[X]) %ₘ Gs).coeff r : ℂ)‖
      ≤ ‖((kappa t s j l : GaussianInt) : ℂ)‖ * a ^ q * (1 + a ^ g) ^ q := by gcongr

theorem re_sum_intCast_mul {ι : Type*} (s : Finset ι) (c : ι → ℤ) (e : ι → GaussianInt) :
    (∑ i ∈ s, (c i : GaussianInt) * e i).re = ∑ i ∈ s, c i * (e i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Zsqrtd.re_add, ih, Zsqrtd.re_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast]
    ring

theorem im_sum_intCast_mul {ι : Type*} (s : Finset ι) (c : ι → ℤ) (e : ι → GaussianInt) :
    (∑ i ∈ s, (c i : GaussianInt) * e i).im = ∑ i ∈ s, c i * (e i).im := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Zsqrtd.im_add, ih, Zsqrtd.im_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast]
    ring

section Siegel

attribute [local instance] Matrix.seminormedAddCommGroup

/-- **Siegel step.** -/
theorem exists_siegel_coefficients {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {a : ℝ} (ha : 1 ≤ a) (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ a)
    {J L h T₀ : ℕ} (hh : 1 ≤ h) (hT₀ : 1 ≤ T₀)
    (hcount : 2 * (T₀ * h * G.natDegree * 2) ≤ (J + 1) * L) :
    ∃ c : Fin (J + 1) → Fin L → ℤ, c ≠ 0 ∧
      (∀ j l, |(c j l : ℝ)| ≤ ((J + 1) * L : ℕ) * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ T₀ *
        a ^ (J * h) * (1 + a ^ G.natDegree) ^ (J * h))) ∧
      ∀ t < T₀, ∀ s < h, G ∣ auxQ c t s := by
  classical
  set g := G.natDegree with hg
  set q := J * h with hq
  set Abd : ℝ := (h : ℝ) ^ L * ((J : ℝ) + L) ^ T₀ * a ^ q * (1 + a ^ g) ^ q with hAbd
  have hm0 : 0 < T₀ * h * g * 2 := by positivity
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, mul_zero] at hcount; omega
    · exact h0
  have hAbd1 : 1 ≤ Abd := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) ^ L := one_le_pow₀ (by exact_mod_cast hh)
    have h2 : (1 : ℝ) ≤ ((J : ℝ) + L) ^ T₀ := one_le_pow₀ (by
      have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)])
    have h3 : (1 : ℝ) ≤ a ^ q := one_le_pow₀ ha
    have h4 : (1 : ℝ) ≤ (1 + a ^ g) ^ q := one_le_pow₀ (by linarith [one_le_pow₀ (n := g) ha])
    rw [hAbd]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4
  let A : Matrix (Fin T₀ × Fin h × Fin g × Fin 2) (Fin (J + 1) × Fin L) ℤ := fun i k =>
    if i.2.2.2 = 0 then (entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2).re
    else (entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2).im
  have hentry : ∀ i k, ‖A i k‖ ≤ Abd := by
    intro i k
    have hjs : (k.1 : ℕ) * i.2.1 ≤ q :=
      Nat.mul_le_mul (Nat.lt_succ_iff.mp k.1.isLt) i.2.1.isLt.le
    have hE := norm_entryG_le hdeg ha hcoeff (t := i.1) (r := i.2.2.1) (l := k.2) hjs
    have hK := norm_kappa_le (t := i.1) (j := k.1) (l := k.2) (J := J) (L := L)
      i.2.1.isLt.le hh (Nat.lt_succ_iff.mp k.1.isLt) k.2.isLt.le
    have hKt : ((J : ℝ) + L) ^ (i.1 : ℕ) ≤ ((J : ℝ) + L) ^ T₀ :=
      pow_le_pow_right₀ (by
        have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
        linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]) i.1.isLt.le
    have hEb : ‖((entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2 : GaussianInt) : ℂ)‖ ≤ Abd := by
      refine hE.trans ?_
      rw [hAbd]
      gcongr
      exact hK.trans (mul_le_mul_of_nonneg_left hKt (by positivity))
    simp only [A, Int.norm_eq_abs]
    split_ifs
    · rw [← Int.cast_abs]
      calc ((|(entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2).re| : ℤ) : ℝ)
          = |((entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2 : GaussianInt) : ℂ).re| := by
            rw [← intCast_re]; push_cast; rfl
        _ ≤ Abd := (Complex.abs_re_le_norm _).trans hEb
    · rw [← Int.cast_abs]
      calc ((|(entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2).im| : ℤ) : ℝ)
          = |((entryG G q i.1 i.2.1 i.2.2.1 k.1 k.2 : GaussianInt) : ℂ).im| := by
            rw [← intCast_im]; push_cast; rfl
        _ ≤ Abd := (Complex.abs_im_le_norm _).trans hEb
  have hA : ‖A‖ ≤ Abd := (Matrix.norm_le_iff (by linarith)).mpr hentry
  have hcard_rows : Fintype.card (Fin T₀ × Fin h × Fin g × Fin 2) = T₀ * h * g * 2 := by
    simp [Fintype.card_prod]; ring
  have hcard_cols : Fintype.card (Fin (J + 1) × Fin L) = (J + 1) * L := by
    simp [Fintype.card_prod]
  have hmn : Fintype.card (Fin T₀ × Fin h × Fin g × Fin 2) < Fintype.card (Fin (J + 1) × Fin L) := by
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
    have hbase1 : 1 ≤ (((J + 1) * L : ℕ) : ℝ) * max 1 ‖A‖ :=
      one_le_mul_of_one_le_of_one_le hn1 (le_max_left _ _)
    have hexp : ((T₀ * h * g * 2 : ℕ) : ℝ) /
        ((((J + 1) * L : ℕ) : ℝ) - ((T₀ * h * g * 2 : ℕ) : ℝ)) ≤ 1 := by
      have h2m : (2 * (T₀ * h * g * 2 : ℕ) : ℝ) ≤ (((J + 1) * L : ℕ) : ℝ) := by
        exact_mod_cast hcount
      have hm : (0 : ℝ) < ((T₀ * h * g * 2 : ℕ) : ℝ) := by exact_mod_cast hm0
      have hpos : (0 : ℝ) < (((J + 1) * L : ℕ) : ℝ) - ((T₀ * h * g * 2 : ℕ) : ℝ) := by
        linarith
      rw [div_le_one hpos]; linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le hbase1 hexp
    rw [Real.rpow_one] at hrpow
    calc |(c' (j, l) : ℝ)| = ‖c' (j, l)‖ := by rw [Int.norm_eq_abs]
      _ ≤ ‖c'‖ := norm_le_pi_norm c' (j, l)
      _ ≤ _ := hc'norm
      _ ≤ (((J + 1) * L : ℕ) : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ (((J + 1) * L : ℕ) : ℝ) * Abd :=
          mul_le_mul_of_nonneg_left (max_le hAbd1 hA) (by positivity)
  · intro t ht s hs
    have hG0 : G ≠ 0 := hG.ne_zero
    set Gs := integralNormalization G
    have hGs : Gs.Monic := monic_integralNormalization hG0
    have hGs1 : Gs ≠ 1 := fun h1 => by
      have := natDegree_integralNormalization (p := G)
      rw [show integralNormalization G = Gs from rfl, h1, natDegree_one] at this
      omega
    have hQdeg : (auxQ (fun j l => c' (j, l)) t s).natDegree ≤ q :=
      (natDegree_auxQ_le _ t s).trans (Nat.mul_le_mul_left _ hs.le)
    refine dvd_of_dvd_starPoly hG hdeg hQdeg ((modByMonic_eq_zero_iff_dvd hGs).mp ?_)
    refine Polynomial.ext fun r => ?_
    rw [coeff_zero]
    by_cases hr : g ≤ r
    · refine coeff_eq_zero_of_natDegree_lt ?_
      have := natDegree_modByMonic_lt (starPoly G.leadingCoeff q (auxQ (fun j l => c' (j, l)) t s))
        hGs hGs1
      rw [natDegree_integralNormalization] at this
      omega
    replace hr := not_le.mp hr
    have hrem : (starPoly G.leadingCoeff q (auxQ (fun j l => c' (j, l)) t s) %ₘ Gs).coeff r =
        remFun G q r (auxQ (fun j l => c' (j, l)) t s) := rfl
    rw [hrem, remFun_auxQ]
    have hrow : ∀ b : Fin 2, (A *ᵥ c') (⟨t, ht⟩, ⟨s, hs⟩, ⟨r, hr⟩, b) = 0 := fun b => by
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
