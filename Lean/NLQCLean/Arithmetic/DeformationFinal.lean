import NLQCLean.Arithmetic.DeformationEliminant
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The optimization eliminant without external input

Let `Cst ∈ ℤ[x]` and `Sc ∈ ℤ[cos, sin, x]` have degree at most `12` and coefficient mass at
most `H`, with `k` coordinates. Suppose the maximum of `Sc(cos θ, sin θ, ·)` over
`{Cst = 0}` equals `16(1 − g)` with `0 < g ≤ 1`, attained at a point with coordinates in
`[−1, 1]`. Then some nonzero `A ∈ ℤ[g, c]` vanishes at `(g, cos θ)`. Its degree is at most
`dNrm k = 4 · 26 · 25^k · (26 + 24k) + 2` and its mass at most `MNrm k H · 32^{dNrm k}`.

The proof deforms the problem to `Q_λ = Σ z²⁶ − R₀ + λ (Cst² + (y − Sc)²)` and takes the
determinant eliminant of its critical system. It then takes the norm in `s` and the leading
coefficient in `λ`, and passes to the limit `λ → ∞` along maximizers.
-/

namespace NLQCLean.Deformation

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination NLQCLean.PurePower
open Filter Topology

local notation "pe" => PhysicalPolynomial.eval

/-! ### Size functions -/

/-- Number of reduced monomials, `26 · 25^k`. -/
def NB (k : ℕ) : ℕ := 26 * 25 ^ k

/-- Level of the multiplication matrix, `26 + 24k`. -/
def DB (k : ℕ) : ℕ := 26 + 24 * k

/-- The deformation constant `R₀ = k + 16²⁶ + 1`. -/
def R0 (k : ℕ) : ℕ := k + 16 ^ 26 + 1

/-- The reduction constant. -/
def KB (k H : ℕ) : ℕ := 26 * R0 k + (26 + 24 * k) * (H ^ 2 + (1 + H) ^ 2)

/-- Degree of the determinant. -/
def dPhi (k : ℕ) : ℕ := NB k * DB k

/-- Mass of the determinant. -/
def MPhi (k H : ℕ) : ℕ := (NB k).factorial * (KB k H ^ DB k + KB k H ^ DB k) ^ NB k

/-- Degree of the norm and of the final eliminant. -/
def dNrm (k : ℕ) : ℕ := 4 * dPhi k + 2

/-- Mass of the norm. -/
def MNrm (k H : ℕ) : ℕ := 3 * ((dPhi k + 1) * (MPhi k H * 2 ^ dPhi k)) ^ 2

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem card_bas_ePow : Fintype.card (Bas (ePow : Option κ → ℕ)) = NB (Fintype.card κ) := by
  rw [Fintype.card_pi, Fintype.prod_option]
  simp only [Fintype.card_eq_nat_card]
  simp [NB, ePow, Nat.card_eq_fintype_card]

theorem dExp_sys (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) :
    dExp (sys Cst Sc R₀ hC hS) = DB (Fintype.card κ) := by
  change 1 + ∑ u, (ePow u - 1) = _
  rw [Fintype.sum_option]
  simp [ePow, DB, Finset.sum_const, Finset.card_univ]
  ring

/-! ### Affine substitution -/

theorem totalDegree_bind₁_le_of {σ τ : Type*} (p : MvPolynomial σ ℤ)
    (f : σ → MvPolynomial τ ℤ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hf i))).trans (le_of_eq ?_)
  simp [Finsupp.sum]

/-- The substitution `g ↦ 16 − 16 g`, `c ↦ c`. -/
noncomputable def subst16 : Fin 2 → MvPolynomial (Fin 2) ℤ := ![C 16 - C 16 * X 0, X 1]

theorem pe_bind₁_subst16 (A0 : MvPolynomial (Fin 2) ℤ) (g c : ℝ) :
    pe ![g, c] (bind₁ subst16 A0) = pe ![16 - 16 * g, c] A0 := by
  simp only [PhysicalPolynomial.eval, eval₂Hom_bind₁]
  have h : (fun i => eval₂Hom (Int.castRingHom ℝ) ![g, c] (subst16 i)) = ![16 - 16 * g, c] := by
    funext i
    fin_cases i <;> simp [subst16]
  rw [h]

theorem bind₁_subst16_ne_zero {A0 : MvPolynomial (Fin 2) ℤ} (h : A0 ≠ 0) :
    bind₁ subst16 A0 ≠ 0 := by
  intro hz
  apply h
  have hall : ∀ x : Fin 2 → ℝ, pe x A0 = 0 := by
    intro x
    have := congrArg (pe ![(16 - x 0) / 16, x 1]) hz
    rw [map_zero, pe_bind₁_subst16] at this
    have hx : ![16 - 16 * ((16 - x 0) / 16), x 1] = x := by
      funext i
      fin_cases i
      · show 16 - 16 * ((16 - x 0) / 16) = x 0
        ring
      · rfl
    rwa [hx] at this
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) A0 = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_zero]
    have := hall x
    rwa [PhysicalPolynomial.eval, coe_eval₂Hom, eval₂_eq_eval_map] at this
  exact MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℝ)) (by
    rw [hmap, map_zero])

theorem SizeLE.bind₁_subst16 {A0 : MvPolynomial (Fin 2) ℤ} {d M : ℕ} (h : SizeLE A0 d M) :
    SizeLE (bind₁ subst16 A0) d (M * 32 ^ d) := by
  refine ⟨(totalDegree_bind₁_le_of _ _ fun i => ?_).trans h.1, ?_⟩
  · fin_cases i
    · show (C 16 - C 16 * X 0 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1
      refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
    · show (X 1 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1
      simp
  · refine CoefficientMassLE.bind₁_le h.2 h.1 _ (by norm_num) fun i => ?_
    fin_cases i
    · have := (CoefficientMassLE.constant (σ := Fin 2) (16 : ℤ)).sub
        ((CoefficientMassLE.constant (σ := Fin 2) (16 : ℤ)).mul (CoefficientMassLE.variablePolynomial 0))
      exact this.mono (by norm_num)
    · exact (CoefficientMassLE.variablePolynomial (σ := Fin 2) 1).mono (by norm_num)

/-! ### The eliminant -/

/-- **Optimization eliminant, without external input.** -/
theorem exists_deformation_eliminant (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ)
    {H : ℕ} (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12)
    (hCm : CoefficientMassLE Cst H) (hSm : CoefficientMassLE Sc H) (θ g : ℝ) (hg0 : 0 < g)
    (hg1 : g ≤ 1)
    (hupper : ∀ w : κ → ℝ, pe w Cst = 0 →
      pe (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc ≤ 16 * (1 - g))
    (hattain : ∃ w : κ → ℝ, pe w Cst = 0 ∧
      pe (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc = 16 * (1 - g) ∧ ∀ i, |w i| ≤ 1) :
    ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧
      SizeLE A (dNrm (Fintype.card κ)) (MNrm (Fintype.card κ) H * 32 ^ dNrm (Fintype.card κ)) ∧
      pe ![g, Real.cos θ] A = 0 := by
  classical
  obtain ⟨w, hw, hwy, hwb⟩ := hattain
  set k := Fintype.card κ with hk
  set ystar : ℝ := 16 * (1 - g) with hystar
  set c0 := Real.cos θ
  set s0 := Real.sin θ
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = R0 k := ⟨_, rfl⟩
  have hR1n : 1 ≤ R₀ := by rw [hR₀]; exact Nat.le_add_left 1 _
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR1n
  have hGw : ∑ i, w i ^ 26 + ystar ^ 26 < R₀ := by
    have h1 : ∑ i, w i ^ 26 ≤ k := by
      calc ∑ i, w i ^ 26 ≤ ∑ _i : κ, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            have : w i ^ 26 = |w i| ^ 26 := by
              rw [show (26 : ℕ) = 2 * 13 by norm_num, pow_mul, pow_mul, sq_abs]
            rw [this]
            exact pow_le_one₀ (abs_nonneg _) (hwb i)
        _ = k := by simp [hk]
    have hy0 : 0 ≤ ystar := by rw [hystar]; exact mul_nonneg (by norm_num) (by linarith)
    have hy16 : ystar ≤ 16 := by rw [hystar]; linarith
    have h2 : ystar ^ 26 ≤ 16 ^ 26 := pow_le_pow_left₀ hy0 hy16 26
    have h3 : (R₀ : ℝ) = k + 16 ^ 26 + 1 := by rw [hR₀, R0]; push_cast; ring
    linarith
  set S := sys Cst Sc R₀ hC hS with hSdef
  have hMr : ∀ u, l1 (S.r u) ≤ KB k H := fun u => by
    rw [KB, ← hR₀]; exact l1_rPoly_le hC hS hCm hSm R₀ u
  have haK : S.a.natAbs ≤ KB k H := by
    have : (S.a).natAbs = 26 := rfl
    rw [this, KB, ← hR₀]
    calc 26 = 26 * 1 := rfl
      _ ≤ 26 * R₀ := Nat.mul_le_mul_left _ hR1n
      _ ≤ _ := Nat.le_add_right _ _
  obtain ⟨Φ, hΦsz, hΦmem, hΦfin⟩ := exists_det_eliminant S hMr le_rfl haK none
  have hcard : Fintype.card (Bas S.e) = NB k := card_bas_ePow
  have hdexp : dExp S = DB k := dExp_sys Cst Sc R₀ hC hS
  rw [hcard, hdexp] at hΦsz
  obtain ⟨Nrm, hNne, hNsz, hNvan⟩ := exists_norm_eliminant Φ (d := dPhi k) (M := MPhi k H)
    hΦsz (fun v => hΦfin v)
  obtain ⟨A0, hA0ne, hA0sz, hA0lim⟩ := exists_limit_eliminant Nrm hNne hNsz
  -- maximizers along `λₙ = R₀ + 1 + n`
  set lam : ℕ → ℝ := fun n => (R₀ : ℝ) + 1 + n with hlam
  have hcrit := fun n : ℕ => exists_critical_point Cst Sc hC hS R₀ c0 s0 (lam n)
    (by simp only [hlam]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) w ystar hw hwy hGw
    hupper
  choose p hpf hpy hpQ hpb using hcrit
  have hΦvan : ∀ n, pe (fun o => Option.elim o (p n none) ![lam n, c0, s0]) Φ = 0 := by
    intro n
    have hle : Ideal.span (Set.range S.f) ≤ RingHom.ker (pe (Sum.elim (p n) ![lam n, c0, s0])) :=
      Ideal.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact hpf n u)
    have h0 := hle hΦmem
    rw [RingHom.mem_ker, ev_rename] at h0
    have hfun : (Sum.elim (p n) ![lam n, c0, s0] ∘ fun o : Option (Fin 3) =>
        Option.elim o (Sum.inl none) Sum.inr) = fun o => Option.elim o (p n none) ![lam n, c0, s0] := by
      funext o; rcases o with _ | i <;> rfl
    rwa [hfun] at h0
  -- compactness
  have hpB : ∀ n, p n ∈ Set.pi Set.univ fun _ : Option κ => Set.Icc (-(R₀ : ℝ)) R₀ :=
    fun n u _ => abs_le.mp (hpb n u)
  obtain ⟨pinf, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hpB
  set Qr : (Option κ → ℝ) → ℝ := fun x => pe (Sum.elim x ![0, c0, s0]) (Qpoly Cst Sc) with hQr
  have hQrcont : Continuous Qr := continuous_eval_elim _ _
  have hQeq : ∀ n, pe (Sum.elim (p n) ![lam n, c0, s0]) (Qpoly Cst Sc) = Qr (p n) := by
    intro n
    simp only [hQr, eval_Qpoly]
    rfl
  have hQnn : ∀ x, 0 ≤ Qr x := fun x => by simp only [hQr, eval_Qpoly]; positivity
  have hlampos : ∀ n, 0 < lam n := fun n => by
    simp only [hlam]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hQle : ∀ n, Qr (p n) ≤ R₀ / lam n := by
    intro n
    rw [le_div_iff₀ (hlampos n), mul_comm, ← hQeq]
    exact hpQ n
  have hlamφ : Tendsto (fun n => lam (φ n)) atTop atTop := by
    simp only [hlam]
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hQlim : Qr pinf = 0 := by
    have h1 : Tendsto (fun n => Qr (p (φ n))) atTop (𝓝 (Qr pinf)) :=
      (hQrcont.tendsto _).comp hlim
    have h2 : Tendsto (fun n => (R₀ : ℝ) / lam (φ n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlamφ
    have := le_of_tendsto_of_tendsto' h1 h2 fun n => hQle (φ n)
    exact le_antisymm this (hQnn _)
  have hQlim' : pe (fun i => pinf (some i)) Cst ^ 2 +
      (pinf none - pe (Sum.elim ![c0, s0] fun i => pinf (some i)) Sc) ^ 2 = 0 := by
    have := hQlim
    simp only [hQr] at this
    rw [eval_Qpoly] at this
    exact this
  have hCinf : pe (fun i => pinf (some i)) Cst = 0 := by
    have h1 := sq_nonneg (pinf none - pe (Sum.elim ![c0, s0] fun i => pinf (some i)) Sc)
    have h2 : pe (fun i => pinf (some i)) Cst ^ 2 = 0 := by
      nlinarith [sq_nonneg (pe (fun i => pinf (some i)) Cst)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hYinf : pinf none = pe (Sum.elim ![c0, s0] fun i => pinf (some i)) Sc := by
    have h2 : (pinf none - pe (Sum.elim ![c0, s0] fun i => pinf (some i)) Sc) ^ 2 = 0 := by
      nlinarith [sq_nonneg (pe (fun i => pinf (some i)) Cst),
        sq_nonneg (pinf none - pe (Sum.elim ![c0, s0] fun i => pinf (some i)) Sc)]
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  have hyle : pinf none ≤ ystar := by
    rw [hYinf]
    exact hupper _ hCinf
  have hyge : ystar ≤ pinf none := by
    have h1 : Tendsto (fun n => p (φ n) none) atTop (𝓝 (pinf none)) :=
      ((continuous_apply none).tendsto _).comp hlim
    exact ge_of_tendsto h1 (Eventually.of_forall fun n => hpy (φ n))
  have hyinf : pinf none = ystar := le_antisymm hyle hyge
  have htS : Tendsto (fun n => p (φ n) none) atTop (𝓝 ystar) := by
    rw [← hyinf]
    exact ((continuous_apply none).tendsto _).comp hlim
  have hzeroN : ∀ n, pe ![p (φ n) none, lam (φ n), c0] Nrm = 0 := fun n =>
    hNvan _ _ _ _ (Real.cos_sq_add_sin_sq θ) (hΦvan (φ n))
  have hA0zero := hA0lim c0 ystar (fun n => lam (φ n)) (fun n => p (φ n) none) hlamφ htS hzeroN
  refine ⟨bind₁ subst16 A0, bind₁_subst16_ne_zero hA0ne, SizeLE.bind₁_subst16 hA0sz, ?_⟩
  rw [pe_bind₁_subst16, show (16 : ℝ) - 16 * g = ystar by rw [hystar]; ring]
  exact hA0zero

end NLQCLean.Deformation
