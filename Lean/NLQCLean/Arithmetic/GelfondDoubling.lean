import NLQCLean.Arithmetic.GelfondEstimates
import NLQCLean.Arithmetic.GelfondSiegel

/-!
# The doubling step of Gelfond's method

If `G ∣ Q_{t,s}` for all `t < T` and `s < h`, and `|G(e^i)| < ρ^g`, then the truncated auxiliary
function has derivatives of order `< T` at `0, …, h-1` of size `≲ ρ`; the approximate Schwarz
lemma makes the derivatives of order `< 2T` small; at a root `β₀` of `G` within `ρ` of `e^i`,
`|Q_{t,s}(β₀)|` is below the Liouville threshold, so `G ∣ Q_{t,s}` for all `t < 2T`. The numeric
conditions are explicit hypotheses.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt Filter Topology

/-- Coefficient bound for `Q_{t,s}`, `s ≤ h`. -/
noncomputable def heightQ (J L h : ℕ) (Cc : ℝ) (t : ℕ) : ℝ :=
  (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ t))

/-- The inverse Liouville threshold for `Q_{t,s}`. -/
noncomputable def deltaInv (G : GaussianInt[X]) (J L h : ℕ) (Cc : ℝ) (t : ℕ) : ℝ :=
  ((((J * h : ℕ) : ℝ) + 1) * heightQ J L h Cc t) ^ (G.natDegree - 1) *
    (G.map toComplex).mahlerMeasure ^ (J * h)

/-- Growth bound for the auxiliary function on `|w| = 8h`. -/
noncomputable def growthF (J L h : ℕ) (Cc : ℝ) : ℝ :=
  (J + 1) * L * Cc * (8 * (h : ℝ)) ^ L * Real.exp (J * (8 * h))

/-- Quotient bound. -/
noncomputable def quotB (J L h : ℕ) (Cc : ℝ) (T : ℕ) : ℝ :=
  2 ^ (J * h) * ((((J * h : ℕ) : ℝ) + 1) * heightQ J L h Cc T)

/-- Lipschitz constant. -/
noncomputable def lipQ (J L h : ℕ) (Cc : ℝ) (t : ℕ) : ℝ :=
  (((J * h : ℕ) : ℝ) + 1) * (((J * h : ℕ) : ℝ) * (heightQ J L h Cc t * 2 ^ (J * h)))

theorem heightQ_mono {J L h : ℕ} (hL : 1 ≤ L) {Cc : ℝ} (hCc : 0 ≤ Cc) {t t' : ℕ} (htt : t ≤ t') :
    heightQ J L h Cc t ≤ heightQ J L h Cc t' := by
  unfold heightQ
  have : (1 : ℝ) ≤ (J : ℝ) + L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  gcongr

/-- **Doubling step.** -/
theorem doubling {G : GaussianInt[X]} (hG : Irreducible G) (hdeg : 0 < G.natDegree)
    {J L h T : ℕ} (hh : 1 ≤ h) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ} (hCc : 0 ≤ Cc) (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmallG : ‖(G.map toComplex).eval (Complex.exp Complex.I)‖ < ρ ^ G.natDegree)
    (hH1 : ∀ t < 2 * T, t.factorial * growthF J L h Cc / 7 ^ (h * T) *
      deltaInv G J L h Cc t ≤ 1 / 4)
    (hH2 : ∀ t < 2 * T, deltaInv G J L h Cc t *
      (ρ * (quotB J L h Cc T + 1) * (t.factorial * ((((h * T : ℕ) : ℝ)) * interpConst h T *
        (8 * h) ^ (h * T)) / 7 ^ (h * T) + (((h * T : ℕ) : ℝ)) * interpConst h T *
          ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T))) + ρ + ρ * lipQ J L h Cc t) ≤ 1 / 2)
    (hC : ∀ s < h, ∀ t < T, G ∣ auxQ c t s) :
    ∀ s < h, ∀ t < 2 * T, G ∣ auxQ c t s := by
  classical
  intro s₀ hs₀ t ht
  set ζ := Complex.exp Complex.I with hζdef
  have hζ : ‖ζ‖ = 1 := by
    have := Complex.norm_exp_ofReal_mul_I 1
    simpa using this
  set g := G.natDegree with hg
  have hG0 := hG.ne_zero
  set q := J * h with hq
  set ε₀ := ‖(G.map toComplex).eval ζ‖ with hε₀
  set θ := ρ ^ g with hθ
  have hθ0 : 0 < θ := pow_pos hρ0 _
  have hθρ : θ ≤ ρ := pow_le_of_le_one hρ0.le hρ1 (by omega)
  have hQdeg : ∀ t' s, s ≤ h → (auxQ c t' s).natDegree ≤ q := fun t' s hs =>
    (natDegree_auxQ_le c t' s).trans (Nat.mul_le_mul_left J hs)
  have hQcoeff : ∀ t' s, s ≤ h → ∀ k, ‖((auxQ c t' s).coeff k : ℂ)‖ ≤ heightQ J L h Cc t' :=
    fun t' s hs k => norm_coeff_auxQ_le c hc hs hh k
  have hquot0 : 0 ≤ quotB J L h Cc T := by
    unfold quotB heightQ; positivity
  -- data at `ζ` for low orders
  have hdataQ : ∀ s < h, ∀ t' < T,
      ‖((auxQ c t' s).map toComplex).eval ζ‖ ≤ ε₀ * quotB J L h Cc T := by
    intro s hs t' ht'
    refine (norm_eval_le_of_dvd hG0 (hC s hs t' ht') (hQdeg t' s hs.le) (hQcoeff t' s hs.le)
      hζ).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    unfold quotB
    gcongr
    exact heightQ_mono hL hCc ht'.le
  -- truncation
  have hev : ∀ᶠ D in atTop, ∀ i : Fin (2 * T) × Fin h,
      dist ((derivative^[i.1] (auxF c D)).eval (((i.2 : ℕ)) : ℂ))
        (((auxQ c i.1 i.2).map toComplex).eval ζ) < θ := by
    rw [eventually_all]
    intro i
    exact (Metric.tendsto_nhds.mp (tendsto_auxF_derivative c i.1 i.2)) θ hθ0
  obtain ⟨D, hD⟩ := hev.exists
  have hDbound : ∀ t' < 2 * T, ∀ s < h, ‖(derivative^[t'] (auxF c D)).eval (s : ℂ) -
      ((auxQ c t' s).map toComplex).eval ζ‖ < θ := fun t' ht' s hs => by
    have := hD (⟨t', ht'⟩, ⟨s, hs⟩)
    rwa [dist_eq_norm] at this
  set ε := ε₀ * quotB J L h Cc T + θ with hεdef
  have hdataF : ∀ s < h, ∀ t' < T, ‖(derivative^[t'] (auxF c D)).eval (s : ℂ)‖ ≤ ε := by
    intro s hs t' ht'
    calc ‖(derivative^[t'] (auxF c D)).eval (s : ℂ)‖
        ≤ ‖((auxQ c t' s).map toComplex).eval ζ‖ + ‖(derivative^[t'] (auxF c D)).eval (s : ℂ) -
            ((auxQ c t' s).map toComplex).eval ζ‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ε₀ * quotB J L h Cc T + θ := add_le_add (hdataQ s hs t' ht') (hDbound t' (by omega) s hs).le
  have hh8 : (1 : ℝ) ≤ 8 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hgrowth : ∀ w : ℂ, ‖w‖ = 8 * h → ‖(auxF c D).eval w‖ ≤ growthF J L h Cc := fun w hw =>
    norm_eval_auxF_le c hCc hc D hh8 hw.le
  have hschwarz := norm_iterate_derivative_le_schwarz (auxF c D) hh hT hdataF hgrowth hs₀ t
  -- value at `ζ`
  have hQζ : ‖((auxQ c t s₀).map toComplex).eval ζ‖ ≤
      t.factorial * (growthF J L h Cc + (((h * T : ℕ) : ℝ)) * (ε * interpConst h T) *
        (8 * h) ^ (h * T)) / 7 ^ (h * T) + (((h * T : ℕ) : ℝ)) * (ε * interpConst h T) *
          ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T)) + θ := by
    calc ‖((auxQ c t s₀).map toComplex).eval ζ‖
        ≤ ‖(derivative^[t] (auxF c D)).eval (s₀ : ℂ)‖ + ‖((auxQ c t s₀).map toComplex).eval ζ -
            (derivative^[t] (auxF c D)).eval (s₀ : ℂ)‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := add_le_add hschwarz (by rw [norm_sub_rev]; exact (hDbound t ht s₀ hs₀).le)
  -- the nearest root
  obtain ⟨β₀, hβ₀, hnear⟩ := exists_root_near hG0 hdeg ζ
  have hη : ‖ζ - β₀‖ < ρ := by
    by_contra hge
    have := pow_le_pow_left₀ hρ0.le (not_lt.mp hge) g
    linarith
  have hβ2 : ‖β₀‖ ≤ 2 := by
    calc ‖β₀‖ ≤ ‖ζ‖ + ‖β₀ - ζ‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ 1 + 1 := by rw [norm_sub_rev, hζ]; linarith
      _ = 2 := by norm_num
  have hQdegc : ((auxQ c t s₀).map toComplex).natDegree ≤ q := by
    rw [natDegree_map_eq_of_injective toComplex_injective]; exact hQdeg t s₀ hs₀.le
  have hQcoeffc : ∀ k, ‖((auxQ c t s₀).map toComplex).coeff k‖ ≤ heightQ J L h Cc t := fun k => by
    rw [coeff_map]; exact hQcoeff t s₀ hs₀.le k
  have hlip := norm_eval_sub_eval_le hQdegc hQcoeffc (x := ζ) (y := β₀) (by rw [hζ]; norm_num) hβ2
  have hQβ : ‖((auxQ c t s₀).map toComplex).eval β₀‖ ≤
      ‖((auxQ c t s₀).map toComplex).eval ζ‖ + ρ * lipQ J L h Cc t := by
    have hlip0 : 0 ≤ lipQ J L h Cc t := by unfold lipQ heightQ; positivity
    calc ‖((auxQ c t s₀).map toComplex).eval β₀‖
        ≤ ‖((auxQ c t s₀).map toComplex).eval ζ‖ + ‖((auxQ c t s₀).map toComplex).eval β₀ -
            ((auxQ c t s₀).map toComplex).eval ζ‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖((auxQ c t s₀).map toComplex).eval ζ‖ + ρ * lipQ J L h Cc t := by
          gcongr
          rw [norm_sub_rev]
          refine hlip.trans ?_
          unfold lipQ
          exact mul_le_mul_of_nonneg_right hη.le (by unfold heightQ; positivity)
  -- combine
  have hε : ε ≤ ρ * (quotB J L h Cc T + 1) := by
    have hε₀θ : ε₀ ≤ θ := hsmallG.le
    calc ε = ε₀ * quotB J L h Cc T + θ := rfl
      _ ≤ θ * quotB J L h Cc T + θ := by gcongr
      _ = θ * (quotB J L h Cc T + 1) := by ring
      _ ≤ ρ * (quotB J L h Cc T + 1) := by gcongr
  have hdinv0 : 0 ≤ deltaInv G J L h Cc t := by
    unfold deltaInv heightQ
    have := (G.map toComplex).mahlerMeasure_nonneg
    positivity
  have hK0 : (0 : ℝ) ≤ interpConst h T := by positivity
  have hfinal : ‖((auxQ c t s₀).map toComplex).eval β₀‖ * deltaInv G J L h Cc t < 1 := by
    have hA := hH1 t ht
    have hB := hH2 t ht
    set n : ℝ := (((h * T : ℕ) : ℝ))
    have hn0 : 0 ≤ n := by positivity
    set K : ℝ := (interpConst h T : ℝ)
    have hbound : ‖((auxQ c t s₀).map toComplex).eval β₀‖ ≤
        t.factorial * growthF J L h Cc / 7 ^ (h * T) +
        (ρ * (quotB J L h Cc T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
          n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipQ J L h Cc t) := by
      refine hQβ.trans ?_
      have hstep : t.factorial * (growthF J L h Cc + n * (ε * K) * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
          n * (ε * K) * (n ^ t * h ^ (h * T)) + θ ≤
          t.factorial * growthF J L h Cc / 7 ^ (h * T) +
          (ρ * (quotB J L h Cc T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
            n * K * (n ^ t * h ^ (h * T))) + ρ) := by
        have e1 : t.factorial * (growthF J L h Cc + n * (ε * K) * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
            n * (ε * K) * (n ^ t * h ^ (h * T)) =
            t.factorial * growthF J L h Cc / 7 ^ (h * T) +
            ε * (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
              n * K * (n ^ t * h ^ (h * T))) := by ring
        rw [e1]
        have hX : 0 ≤ t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
            n * K * (n ^ t * h ^ (h * T)) := by positivity
        have := mul_le_mul_of_nonneg_right hε hX
        linarith
      linarith [hQζ, hstep]
    calc ‖((auxQ c t s₀).map toComplex).eval β₀‖ * deltaInv G J L h Cc t
        ≤ (t.factorial * growthF J L h Cc / 7 ^ (h * T) +
          (ρ * (quotB J L h Cc T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
            n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipQ J L h Cc t)) *
              deltaInv G J L h Cc t := mul_le_mul_of_nonneg_right hbound hdinv0
      _ = t.factorial * growthF J L h Cc / 7 ^ (h * T) * deltaInv G J L h Cc t +
          deltaInv G J L h Cc t * (ρ * (quotB J L h Cc T + 1) *
            (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
              n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipQ J L h Cc t) := by ring
      _ ≤ 1 / 4 + 1 / 2 := add_le_add hA hB
      _ < 1 := by norm_num
  refine dvd_of_norm_eval_root_small hG hdeg hβ₀ (hQdeg t s₀ hs₀.le) (hQcoeff t s₀ hs₀.le) ?_
  unfold deltaInv at hfinal
  exact hfinal

/-- The coefficient bound produced by Siegel's lemma. -/
noncomputable def siegelBound (G : GaussianInt[X]) (a : ℝ) (J L h T₀ : ℕ) : ℝ :=
  ((J + 1) * L : ℕ) * ((h : ℝ) ^ L * ((J : ℝ) + L) ^ T₀ * a ^ (J * h) *
    (1 + a ^ G.natDegree) ^ (J * h))

/-- **Abstract lower bound.** Under the numeric conditions of the doubling step along the
whole chain `T₀ ≤ T < (J+1)L`, `|G(e^i)| ≥ ρ^g`. -/
theorem lower_bound_of_conditions {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {a : ℝ} (ha : 1 ≤ a) (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ a)
    {J L h T₀ : ℕ} (hh : 1 ≤ h) (hT₀ : 1 ≤ T₀) (hL : 1 ≤ L)
    (hcount : 2 * (T₀ * h * G.natDegree * 2) ≤ (J + 1) * L)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hH1 : ∀ T, T₀ ≤ T → T < (J + 1) * L → ∀ t < 2 * T,
      t.factorial * growthF J L h (siegelBound G a J L h T₀) / 7 ^ (h * T) *
        deltaInv G J L h (siegelBound G a J L h T₀) t ≤ 1 / 4)
    (hH2 : ∀ T, T₀ ≤ T → T < (J + 1) * L → ∀ t < 2 * T,
      deltaInv G J L h (siegelBound G a J L h T₀) t *
      (ρ * (quotB J L h (siegelBound G a J L h T₀) T + 1) *
        (t.factorial * ((((h * T : ℕ) : ℝ)) * interpConst h T * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
          (((h * T : ℕ) : ℝ)) * interpConst h T * ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T))) + ρ +
        ρ * lipQ J L h (siegelBound G a J L h T₀) t) ≤ 1 / 2) :
    ρ ^ G.natDegree ≤ ‖(G.map toComplex).eval (Complex.exp Complex.I)‖ := by
  classical
  by_contra hlt
  replace hlt := not_le.mp hlt
  obtain ⟨c, hc0, hcbound, hC₀⟩ := exists_siegel_coefficients hG hdeg ha hcoeff hh hT₀ hcount
  set Cc := siegelBound G a J L h T₀ with hCc
  have hCc0 : 0 ≤ Cc := by
    rw [hCc, siegelBound]
    have : (0 : ℝ) ≤ (1 + a ^ G.natDegree) := by positivity
    positivity
  set U := (J + 1) * L with hU
  let P : ℕ → Prop := fun T => ∀ s < h, ∀ t < T, G ∣ auxQ c t s
  have hmono : ∀ {T T'}, T' ≤ T → P T → P T' := fun hTT hP s hs t ht => hP s hs t (by omega)
  have hstep : ∀ T, T₀ ≤ T → T < U → P T → P (2 * T) := fun T hT₀T hTU hP =>
    doubling hG hdeg hh (by omega) hL c hCc0 hcbound hρ0 hρ1 hlt (hH1 T hT₀T hTU)
      (hH2 T hT₀T hTU) hP
  have hchain : ∀ k, P (min (T₀ * 2 ^ k) U) := by
    intro k
    induction k with
    | zero => simpa using hmono (min_le_left _ _) (fun s hs t ht => hC₀ t ht s hs : P T₀)
    | succ k ih =>
      by_cases hk : U ≤ T₀ * 2 ^ k
      · rw [min_eq_right (hk.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
          (Nat.le_succ k))))]
        rwa [min_eq_right hk] at ih
      · replace hk := not_le.mp hk
        rw [min_eq_left hk.le] at ih
        have := hstep _ (Nat.le_mul_of_pos_right _ (by positivity)) hk ih
        refine hmono (min_le_left _ _) ?_
        rwa [show T₀ * 2 ^ (k + 1) = 2 * (T₀ * 2 ^ k) by ring]
  have hPU : P U := by
    have := hchain U
    rwa [min_eq_right] at this
    calc U ≤ 2 ^ U := (Nat.lt_two_pow_self).le
      _ ≤ T₀ * 2 ^ U := Nat.le_mul_of_pos_left _ (by omega)
  -- the Taylor data at `0` vanish
  have hφ : ∀ t < U, ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : GaussianInt) * kappa t 0 j l = 0 := by
    intro t ht
    have hdvd := hPU 0 (by omega) t ht
    rw [auxQ_zero] at hdvd
    by_contra hne
    have := natDegree_le_of_dvd hdvd (C_ne_zero.mpr hne)
    rw [natDegree_C] at this
    omega
  apply hc0
  have hz := coeff_eq_zero_of_taylor_vanish (K := ℂ) (J := J) (L := L)
    (fun j => ((j : ℕ) : ℂ) * Complex.I) (fun j₁ j₂ hj => by
      have := mul_right_cancel₀ Complex.I_ne_zero hj
      exact Fin.ext (by exact_mod_cast this))
    (fun j l => (c j l : ℂ)) (fun t ht => by
      have := congrArg (fun z : GaussianInt => (z : ℂ)) (hφ t ht)
      simp only [map_sum, map_mul, map_intCast, toComplex_kappa_zero, map_zero] at this
      rw [← this])
  funext j l
  have := congrFun (congrFun hz j) l
  simpa using this

end NLQCLean.Gelfond
