import NLQCLean.Arithmetic.GelfondAngleSiegel

/-!
# The doubling step of Gelfond's method for `e^{iθ}`

Fix a root `β₀` of `G` with `|e^{iθ} - β₀| < ρ`. If `S_{t,s}(β₀) = 0` for all `t < T` and
`s < h`, then the truncated auxiliary function has derivatives of order `< T` at `0, …, h-1` of
size `≲ ρ` (Lipschitz bound between `β₀` and `e^{iθ}`); the approximate Schwarz lemma makes the
derivatives of order `< 2T` small; then `a^t S_{t,s}(β₀) = Σ_e ϑ^e Q_{t,s,e}(β₀)` is below the
Liouville threshold over `ℤ[i][ϑ]`, so it vanishes. The numeric conditions are explicit
hypotheses.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt Filter Topology

/-- Coefficient bound for `S_{t,s}`, `s ≤ h`. -/
noncomputable def heightS (J L h : ℕ) (Cc w : ℝ) (t : ℕ) : ℝ :=
  (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((J : ℝ) * w + L) ^ t))

/-- Lipschitz constant of `S_{t,s}` on the disc of radius `2`. -/
noncomputable def lipS (J L h : ℕ) (Cc w : ℝ) (t : ℕ) : ℝ :=
  (((J * h : ℕ) : ℝ) + 1) * (((J * h : ℕ) : ℝ) * (heightS J L h Cc w t * 2 ^ (J * h)))

/-- Coefficient bound for `Q_{t,s,e}`, `s ≤ h`. -/
noncomputable def heightQA (a : ℕ) (F : ℝ) (J L h : ℕ) (Cc : ℝ) (t : ℕ) : ℝ :=
  (J + 1) * L * (Cc * ((h : ℝ) ^ L * ((a : ℝ) * L + J * (1 + F)) ^ t))

/-- The inverse Liouville threshold for `S_{t,s}`. -/
noncomputable def deltaInvA (G : GaussianInt[X]) (a m : ℕ) (F : ℝ) (J L h : ℕ) (Cc : ℝ)
    (t : ℕ) : ℝ :=
  (a : ℝ) ^ t * angleLiouville G m F (J * h) (heightQA a F J L h Cc t)

/-- Growth bound for the auxiliary function on `|w| = 8h`. -/
noncomputable def growthA (J L h : ℕ) (Cc w : ℝ) : ℝ :=
  (J + 1) * L * Cc * (8 * (h : ℝ)) ^ L * Real.exp (J * w * (8 * h))

theorem heightS_mono {J L h : ℕ} (hL : 1 ≤ L) {Cc w : ℝ} (hCc : 0 ≤ Cc) (hw : 0 ≤ w)
    {t t' : ℕ} (htt : t ≤ t') : heightS J L h Cc w t ≤ heightS J L h Cc w t' := by
  unfold heightS
  have : (1 : ℝ) ≤ (J : ℝ) * w + L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have : (0 : ℝ) ≤ J * w := by positivity
    linarith
  gcongr

theorem lipS_mono {J L h : ℕ} (hL : 1 ≤ L) {Cc w : ℝ} (hCc : 0 ≤ Cc) (hw : 0 ≤ w)
    {t t' : ℕ} (htt : t ≤ t') : lipS J L h Cc w t ≤ lipS J L h Cc w t' := by
  unfold lipS
  gcongr
  exact heightS_mono hL hCc hw htt

theorem heightS_nonneg {J L h : ℕ} {Cc w : ℝ} (hCc : 0 ≤ Cc) (hw : 0 ≤ w) (t : ℕ) :
    0 ≤ heightS J L h Cc w t := by
  unfold heightS; positivity

theorem lipS_nonneg {J L h : ℕ} {Cc w : ℝ} (hCc : 0 ≤ Cc) (hw : 0 ≤ w) (t : ℕ) :
    0 ≤ lipS J L h Cc w t := by
  unfold lipS; have := heightS_nonneg (J := J) (L := L) (h := h) hCc hw t; positivity

theorem one_le_heightQA {a : ℕ} (ha : 1 ≤ a) {F : ℝ} (hF0 : 0 ≤ F) {J L h : ℕ} (hL : 1 ≤ L)
    (hh : 1 ≤ h) {Cc : ℝ} (hCc : 1 ≤ Cc) (t : ℕ) : 1 ≤ heightQA a F J L h Cc t := by
  unfold heightQA
  have h1 : (1 : ℝ) ≤ (J + 1) * L := one_le_mul_of_one_le_of_one_le
    (by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]) (by exact_mod_cast hL)
  have h2 : (1 : ℝ) ≤ (h : ℝ) ^ L := one_le_pow₀ (by exact_mod_cast hh)
  have h3 : (1 : ℝ) ≤ ((a : ℝ) * L + J * (1 + F)) ^ t := by
    refine one_le_pow₀ ?_
    have : (1 : ℝ) ≤ (a : ℝ) * L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast ha)
      (by exact_mod_cast hL)
    have : (0 : ℝ) ≤ J * (1 + F) := by positivity
    linarith
  exact one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le hCc
    (one_le_mul_of_one_le_of_one_le h2 h3))

/-- **Doubling step.** -/
theorem doubling_angle {G : GaussianInt[X]} (hG : Irreducible G) (hdeg : 0 < G.natDegree)
    {a : ℕ} (ha1 : 1 ≤ a) {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m)
    (hm : 1 ≤ m) {θ : ℝ} {ϑ : ℂ} (hϑa : ϑ = a * θ) (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0)
    {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F)
    {J L h T : ℕ} (hh : 1 ≤ h) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (c : Fin (J + 1) → Fin L → ℤ) {Cc : ℝ} (hCc : 1 ≤ Cc) (hc : ∀ j l, |(c j l : ℝ)| ≤ Cc)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {β₀ : ℂ} (hβ : (G.map toComplex).eval β₀ = 0)
    (hnear : ‖Complex.exp ((θ : ℂ) * Complex.I) - β₀‖ < ρ)
    (hH1 : ∀ t < 2 * T, t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) *
      deltaInvA G a m F J L h Cc t ≤ 1 / 4)
    (hH2 : ∀ t < 2 * T, deltaInvA G a m F J L h Cc t *
      (ρ * (lipS J L h Cc |θ| T + 1) * (t.factorial * ((((h * T : ℕ) : ℝ)) * interpConst h T *
        (8 * h) ^ (h * T)) / 7 ^ (h * T) + (((h * T : ℕ) : ℝ)) * interpConst h T *
          ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T))) + ρ + ρ * lipS J L h Cc |θ| t) ≤ 1 / 2)
    (hC : ∀ s < h, ∀ t < T, (angS ((θ : ℂ) * Complex.I) c t s).eval β₀ = 0) :
    ∀ s < h, ∀ t < 2 * T, (angS ((θ : ℂ) * Complex.I) c t s).eval β₀ = 0 := by
  classical
  intro s₀ hs₀ t ht
  set ω : ℂ := (θ : ℂ) * Complex.I with hωdef
  have hω : ‖ω‖ = |θ| := by
    rw [hωdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  set ζ := Complex.exp ω with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, hωdef]; exact Complex.norm_exp_ofReal_mul_I θ
  have hCc0 : 0 ≤ Cc := by linarith
  have hθ0 : 0 ≤ |θ| := abs_nonneg θ
  have hβ2 : ‖β₀‖ ≤ 2 := by
    calc ‖β₀‖ ≤ ‖ζ‖ + ‖β₀ - ζ‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ 1 + 1 := by rw [norm_sub_rev, hζ]; linarith
      _ = 2 := by norm_num
  set q := J * h with hq
  have hSdeg : ∀ t' s, s ≤ h → (angS ω c t' s).natDegree ≤ q := fun t' s hs =>
    (natDegree_angS_le ω c t' s).trans (Nat.mul_le_mul_left J hs)
  have hScoeff : ∀ t' s, s ≤ h → ∀ k, ‖(angS ω c t' s).coeff k‖ ≤ heightS J L h Cc |θ| t' :=
    fun t' s hs k => by
      have := norm_coeff_angS_le ω c hc hs hh k (t := t')
      rwa [hω] at this
  have hlipζ : ∀ t' s, s ≤ h → ‖(angS ω c t' s).eval ζ - (angS ω c t' s).eval β₀‖ ≤
      ρ * lipS J L h Cc |θ| t' := by
    intro t' s hs
    have h1 := norm_eval_sub_eval_le (hSdeg t' s hs) (hScoeff t' s hs) (x := ζ) (y := β₀)
      (by rw [hζ]; norm_num) hβ2
    refine h1.trans ?_
    unfold lipS
    exact mul_le_mul_of_nonneg_right hnear.le (by
      have := heightS_nonneg (J := J) (L := L) (h := h) hCc0 hθ0 t'; positivity)
  -- data at `ζ` for low orders
  have hdataS : ∀ s < h, ∀ t' < T, ‖(angS ω c t' s).eval ζ‖ ≤ ρ * lipS J L h Cc |θ| T := by
    intro s hs t' ht'
    have h1 := hlipζ t' s hs.le
    rw [hC s hs t' ht', sub_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (lipS_mono hL hCc0 hθ0 ht'.le) hρ0.le)
  -- truncation
  have hev : ∀ᶠ D in atTop, ∀ i : Fin (2 * T) × Fin h,
      dist ((derivative^[i.1] (angF ω c D)).eval (((i.2 : ℕ)) : ℂ))
        ((angS ω c i.1 i.2).eval ζ) < ρ := by
    rw [eventually_all]
    intro i
    exact (Metric.tendsto_nhds.mp (tendsto_angF_derivative ω c i.1 i.2)) ρ hρ0
  obtain ⟨D, hD⟩ := hev.exists
  have hDbound : ∀ t' < 2 * T, ∀ s < h, ‖(derivative^[t'] (angF ω c D)).eval (s : ℂ) -
      (angS ω c t' s).eval ζ‖ < ρ := fun t' ht' s hs => by
    have := hD (⟨t', ht'⟩, ⟨s, hs⟩)
    rwa [dist_eq_norm] at this
  set ε := ρ * lipS J L h Cc |θ| T + ρ with hεdef
  have hdataF : ∀ s < h, ∀ t' < T, ‖(derivative^[t'] (angF ω c D)).eval (s : ℂ)‖ ≤ ε := by
    intro s hs t' ht'
    calc ‖(derivative^[t'] (angF ω c D)).eval (s : ℂ)‖
        ≤ ‖(angS ω c t' s).eval ζ‖ + ‖(derivative^[t'] (angF ω c D)).eval (s : ℂ) -
            (angS ω c t' s).eval ζ‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ρ * lipS J L h Cc |θ| T + ρ :=
          add_le_add (hdataS s hs t' ht') (hDbound t' (by omega) s hs).le
  have hh8 : (1 : ℝ) ≤ 8 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hgrowth : ∀ w : ℂ, ‖w‖ = 8 * h → ‖(angF ω c D).eval w‖ ≤ growthA J L h Cc |θ| :=
    fun w hw => by
      have := norm_eval_angF_le ω c hCc0 hc D hh8 hw.le
      rwa [hω] at this
  have hschwarz := norm_iterate_derivative_le_schwarz (angF ω c D) hh hT hdataF hgrowth hs₀ t
  -- value at `ζ`, then at `β₀`
  have hSζ : ‖(angS ω c t s₀).eval ζ‖ ≤
      t.factorial * (growthA J L h Cc |θ| + (((h * T : ℕ) : ℝ)) * (ε * interpConst h T) *
        (8 * h) ^ (h * T)) / 7 ^ (h * T) + (((h * T : ℕ) : ℝ)) * (ε * interpConst h T) *
          ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T)) + ρ := by
    calc ‖(angS ω c t s₀).eval ζ‖
        ≤ ‖(derivative^[t] (angF ω c D)).eval (s₀ : ℂ)‖ + ‖(angS ω c t s₀).eval ζ -
            (derivative^[t] (angF ω c D)).eval (s₀ : ℂ)‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := add_le_add hschwarz (by rw [norm_sub_rev]; exact (hDbound t ht s₀ hs₀).le)
  have hSβ : ‖(angS ω c t s₀).eval β₀‖ ≤ ‖(angS ω c t s₀).eval ζ‖ + ρ * lipS J L h Cc |θ| t := by
    calc ‖(angS ω c t s₀).eval β₀‖
        ≤ ‖(angS ω c t s₀).eval ζ‖ + ‖(angS ω c t s₀).eval β₀ - (angS ω c t s₀).eval ζ‖ :=
          norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := by
          gcongr
          rw [norm_sub_rev]
          exact hlipζ t s₀ hs₀.le
  have hε : ε ≤ ρ * (lipS J L h Cc |θ| T + 1) := by rw [hεdef]; ring_nf; rfl
  have hdinv0 : 0 ≤ deltaInvA G a m F J L h Cc t := by
    unfold deltaInvA
    have := one_le_angleLiouville hG.ne_zero hm hF0 (q := J * h)
      (one_le_heightQA ha1 hF0 (J := J) hL hh hCc t)
    positivity
  have hK0 : (0 : ℝ) ≤ interpConst h T := by positivity
  have hfinal : ‖(angS ω c t s₀).eval β₀‖ * deltaInvA G a m F J L h Cc t < 1 := by
    have hA := hH1 t ht
    have hB := hH2 t ht
    set n : ℝ := (((h * T : ℕ) : ℝ))
    have hn0 : 0 ≤ n := by positivity
    set K : ℝ := (interpConst h T : ℝ)
    have hbound : ‖(angS ω c t s₀).eval β₀‖ ≤
        t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) +
        (ρ * (lipS J L h Cc |θ| T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) /
          7 ^ (h * T) + n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipS J L h Cc |θ| t) := by
      refine hSβ.trans ?_
      have hstep : t.factorial * (growthA J L h Cc |θ| + n * (ε * K) * (8 * h) ^ (h * T)) /
          7 ^ (h * T) + n * (ε * K) * (n ^ t * h ^ (h * T)) + ρ ≤
          t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) +
          (ρ * (lipS J L h Cc |θ| T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) /
            7 ^ (h * T) + n * K * (n ^ t * h ^ (h * T))) + ρ) := by
        have e1 : t.factorial * (growthA J L h Cc |θ| + n * (ε * K) * (8 * h) ^ (h * T)) /
            7 ^ (h * T) + n * (ε * K) * (n ^ t * h ^ (h * T)) =
            t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) +
            ε * (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
              n * K * (n ^ t * h ^ (h * T))) := by ring
        rw [e1]
        have hX : 0 ≤ t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
            n * K * (n ^ t * h ^ (h * T)) := by positivity
        have := mul_le_mul_of_nonneg_right hε hX
        linarith
      linarith [hSζ, hstep]
    calc ‖(angS ω c t s₀).eval β₀‖ * deltaInvA G a m F J L h Cc t
        ≤ (t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) +
          (ρ * (lipS J L h Cc |θ| T + 1) * (t.factorial * (n * K * (8 * h) ^ (h * T)) /
            7 ^ (h * T) + n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipS J L h Cc |θ| t)) *
              deltaInvA G a m F J L h Cc t := mul_le_mul_of_nonneg_right hbound hdinv0
      _ = t.factorial * growthA J L h Cc |θ| / 7 ^ (h * T) * deltaInvA G a m F J L h Cc t +
          deltaInvA G a m F J L h Cc t * (ρ * (lipS J L h Cc |θ| T + 1) *
            (t.factorial * (n * K * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
              n * K * (n ^ t * h ^ (h * T))) + ρ + ρ * lipS J L h Cc |θ| t) := by ring
      _ ≤ 1 / 4 + 1 / 2 := add_le_add hA hB
      _ < 1 := by norm_num
  -- the Liouville inequality over `ℤ[i][ϑ]`
  have hdec := eval_angS_eq_sum hf hmf hϑa hϑ c t s₀ β₀
  have hsmall : ‖∑ e : Fin m, ϑ ^ (e : ℕ) * ((angQ a f c t s₀ e).map toComplex).eval β₀‖ *
      angleLiouville G m F (J * h) (heightQA a F J L h Cc t) < 1 := by
    rw [← hdec, norm_mul, norm_pow, Complex.norm_natCast]
    unfold deltaInvA at hfinal
    calc (a : ℝ) ^ t * ‖(angS ω c t s₀).eval β₀‖ *
          angleLiouville G m F (J * h) (heightQA a F J L h Cc t)
        = ‖(angS ω c t s₀).eval β₀‖ *
            ((a : ℝ) ^ t * angleLiouville G m F (J * h) (heightQA a F J L h Cc t)) := by ring
      _ < 1 := hfinal
  have hzero := eq_zero_of_norm_small_angle hG hdeg hβ hβ2 hf hmf hm hϑ hF0 hF
    (fun e => angQ a f c t s₀ e) (one_le_heightQA ha1 hF0 (J := J) hL hh hCc t)
    (fun e => (natDegree_angQ_le a f c t s₀ e).trans (Nat.mul_le_mul_left J hs₀.le))
    (fun e k => norm_coeff_angQ_le hf (hmf ▸ hm) hF0 hF c hc hs₀.le hh e k) hsmall
  rw [← hdec] at hzero
  have ha0 : (a : ℂ) ^ t ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : a ≠ 0))
  exact (mul_eq_zero.mp hzero).resolve_left ha0

theorem one_le_angSiegelBound {G : GaussianInt[X]} {aG : ℝ} (ha : 1 ≤ aG) {a : ℕ} (ha1 : 1 ≤ a)
    {F : ℝ} (hF0 : 0 ≤ F) {J L h T₀ : ℕ} (hh : 1 ≤ h) (hL : 1 ≤ L) :
    1 ≤ angSiegelBound G aG a F J L h T₀ := by
  unfold angSiegelBound
  have h0 : (1 : ℝ) ≤ (((J + 1) * L : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : (1 : ℝ) ≤ (h : ℝ) ^ L := one_le_pow₀ (by exact_mod_cast hh)
  have h2 : (1 : ℝ) ≤ ((a : ℝ) * L + J * (1 + F)) ^ T₀ := by
    refine one_le_pow₀ ?_
    have : (1 : ℝ) ≤ (a : ℝ) * L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast ha1)
      (by exact_mod_cast hL)
    have : (0 : ℝ) ≤ J * (1 + F) := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ aG ^ (J * h) := one_le_pow₀ ha
  have h4 : (1 : ℝ) ≤ (1 + aG ^ G.natDegree) ^ (J * h) :=
    one_le_pow₀ (by linarith [one_le_pow₀ (n := G.natDegree) ha])
  exact one_le_mul_of_one_le_of_one_le h0 (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4)

/-- **Abstract lower bound.** Under the numeric conditions of the doubling step along the
whole chain `T₀ ≤ T < (J+1)L`, `|G(e^{iθ})| ≥ ρ^g`. -/
theorem lower_bound_of_conditions_angle {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {aG : ℝ} (ha : 1 ≤ aG) (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ aG)
    {a : ℕ} (ha1 : 1 ≤ a) {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m)
    (hm : 1 ≤ m) {θ : ℝ} (hθ0 : θ ≠ 0) {ϑ : ℂ} (hϑa : ϑ = a * θ)
    (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F)
    {J L h T₀ : ℕ} (hh : 1 ≤ h) (hT₀ : 1 ≤ T₀) (hL : 1 ≤ L)
    (hcount : 2 * (T₀ * h * G.natDegree * m * 2) ≤ (J + 1) * L)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hH1 : ∀ T, T₀ ≤ T → T < (J + 1) * L → ∀ t < 2 * T,
      t.factorial * growthA J L h (angSiegelBound G aG a F J L h T₀) |θ| / 7 ^ (h * T) *
        deltaInvA G a m F J L h (angSiegelBound G aG a F J L h T₀) t ≤ 1 / 4)
    (hH2 : ∀ T, T₀ ≤ T → T < (J + 1) * L → ∀ t < 2 * T,
      deltaInvA G a m F J L h (angSiegelBound G aG a F J L h T₀) t *
      (ρ * (lipS J L h (angSiegelBound G aG a F J L h T₀) |θ| T + 1) *
        (t.factorial * ((((h * T : ℕ) : ℝ)) * interpConst h T * (8 * h) ^ (h * T)) / 7 ^ (h * T) +
          (((h * T : ℕ) : ℝ)) * interpConst h T * ((((h * T : ℕ) : ℝ)) ^ t * h ^ (h * T))) + ρ +
        ρ * lipS J L h (angSiegelBound G aG a F J L h T₀) |θ| t) ≤ 1 / 2) :
    ρ ^ G.natDegree ≤ ‖(G.map toComplex).eval (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  classical
  by_contra hlt
  replace hlt := not_le.mp hlt
  set ω : ℂ := (θ : ℂ) * Complex.I with hωdef
  obtain ⟨c, hc0, hcbound, hC₀⟩ := exists_siegel_coefficients_angle hG hdeg ha hcoeff ha1 hf hmf
    hm hF0 hF hh hT₀ hcount
  set Cc := angSiegelBound G aG a F J L h T₀ with hCc
  have hCc1 : 1 ≤ Cc := one_le_angSiegelBound ha ha1 hF0 hh hL
  obtain ⟨β₀, hβ₀, hnear⟩ := exists_root_near hG.ne_zero hdeg (Complex.exp ω)
  have hη : ‖Complex.exp ω - β₀‖ < ρ := by
    by_contra hge
    have := pow_le_pow_left₀ hρ0.le (not_lt.mp hge) G.natDegree
    linarith
  set U := (J + 1) * L with hU
  let P : ℕ → Prop := fun T => ∀ s < h, ∀ t < T, (angS ω c t s).eval β₀ = 0
  have hmono : ∀ {T T'}, T' ≤ T → P T → P T' := fun hTT hP s hs t ht => hP s hs t (by omega)
  have hP₀ : P T₀ := by
    intro s hs t ht
    have hdec := eval_angS_eq_sum hf hmf hϑa hϑ c t s β₀
    have hsum : ∑ e : Fin m, ϑ ^ (e : ℕ) * ((angQ a f c t s e).map toComplex).eval β₀ = 0 :=
      Finset.sum_eq_zero fun e _ => by
        obtain ⟨W, hW⟩ := hC₀ t ht s hs e e.isLt
        rw [hW, Polynomial.map_mul, eval_mul, hβ₀, zero_mul, mul_zero]
    rw [← hdec] at hsum
    have ha0 : (a : ℂ) ^ t ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : a ≠ 0))
    exact (mul_eq_zero.mp hsum).resolve_left ha0
  have hstep : ∀ T, T₀ ≤ T → T < U → P T → P (2 * T) := fun T hT₀T hTU hP =>
    doubling_angle hG hdeg ha1 hf hmf hm hϑa hϑ hF0 hF hh (by omega) hL c hCc1 hcbound hρ0 hρ1
      hβ₀ hη (hH1 T hT₀T hTU) (hH2 T hT₀T hTU) hP
  have hchain : ∀ k, P (min (T₀ * 2 ^ k) U) := by
    intro k
    induction k with
    | zero => simpa using hmono (min_le_left _ _) hP₀
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
  have hφ : ∀ t < U, ∑ j : Fin (J + 1), ∑ l : Fin L, (c j l : ℂ) * angKappa ω t 0 j l = 0 := by
    intro t ht
    have h0 := hPU 0 (by omega) t ht
    rwa [angS_zero, eval_C] at h0
  apply hc0
  have hz := coeff_eq_zero_of_taylor_vanish (K := ℂ) (J := J) (L := L)
    (fun j => ((j : ℕ) : ℂ) * ω) (fun j₁ j₂ hj => by
      have hω0 : ω ≠ 0 := mul_ne_zero (by exact_mod_cast hθ0) Complex.I_ne_zero
      have := mul_right_cancel₀ hω0 hj
      exact Fin.ext (by exact_mod_cast this))
    (fun j l => (c j l : ℂ)) (fun t ht => by
      have := hφ t ht
      simp only [angKappa_zero] at this
      rw [← this])
  funext j l
  have := congrFun (congrFun hz j) l
  simpa using this

end NLQCLean.Gelfond
