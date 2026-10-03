import NLQCLean.Arithmetic.DeformationAnalysis
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The deformation eliminant

From the determinant `Φ(T, λ, c, s)` of the deformed critical system:

* **Norm.** Write `Φ = Σ_k Φ_k s^k` and put `U = Σ_{k even} Φ_k (1 − c²)^{k/2}`,
  `V = Σ_{k odd} Φ_k (1 − c²)^{k/2}`. When `c² + s² = 1`,
  `U² − (1 − c²)V² = Φ(…, s) Φ(…, −s)`. It is nonzero because `Φ` has only finitely many
  zeros in `T` at `(λ, c, s) = (0, 0, ±1)`.
* **Limit.** The leading coefficient `A₀(T, c)` of this norm in `λ` vanishes at `(y*, c₀)`
  whenever the norm vanishes along `λₙ → ∞`, `Tₙ → y*`.
* **Eliminant.** `A(g, c) = A₀(16 − 16 g, c)`.
-/

namespace NLQCLean.Deformation

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination NLQCLean.PurePower
open Filter Topology

/-- Real evaluation of integer polynomials. -/
local notation "pe" => PhysicalPolynomial.eval

/-! ### Expansion in one variable -/

theorem ev_option {σ : Type*} (x : σ → ℝ) (y : ℝ) (f : MvPolynomial (Option σ) ℤ) :
    pe (fun o => Option.elim o y x) f =
      Polynomial.eval₂ (pe x) y (optionEquivLeft ℤ σ f) := by
  have h : (pe (fun o => Option.elim o y x) : MvPolynomial (Option σ) ℤ →+* ℝ) =
      (Polynomial.eval₂RingHom (pe x) y).comp
        (optionEquivLeft ℤ σ).toAlgHom.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [ev_C, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgEquiv.coe_toAlgHom, optionEquivLeft_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
    · rcases i with _ | i
      · simp only [ev_X, Option.elim_none, RingHom.coe_comp, Function.comp_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom, optionEquivLeft_X_none,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      · simp only [ev_X, Option.elim_some, RingHom.coe_comp, Function.comp_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom, optionEquivLeft_X_some,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  exact congrArg (fun φ : MvPolynomial (Option σ) ℤ →+* ℝ => φ f) h

theorem natDegree_optionEquivLeft_le {σ : Type*} (f : MvPolynomial (Option σ) ℤ) :
    (optionEquivLeft ℤ σ f).natDegree ≤ f.totalDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨m, hm⟩ : ((optionEquivLeft ℤ σ f).coeff k).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  have hmem := (mem_support_coeff_optionEquivLeft (R := ℤ)).mp hm
  have h1 := le_totalDegree hmem
  have h2 : k ≤ (m.optionElim k).sum fun _ e => e := by
    have := Finsupp.le_degree none (m.optionElim k)
    simpa [Finsupp.degree_apply, Finsupp.sum] using this
  have : (k : WithBot ℕ) ≤ f.totalDegree := by exact_mod_cast h2.trans h1
  exact absurd (WithBot.coe_le_coe.mp this) (not_le.mpr hk)

/-- The even part `Σ_{k even} P_k q^{k/2}`. -/
noncomputable def evenPart {τ : Type*} (P : Polynomial (MvPolynomial τ ℤ)) (q : MvPolynomial τ ℤ)
    (n : ℕ) : MvPolynomial τ ℤ :=
  ∑ k ∈ Finset.range n, if Even k then P.coeff k * q ^ (k / 2) else 0

/-- The odd part `Σ_{k odd} P_k q^{k/2}`. -/
noncomputable def oddPart {τ : Type*} (P : Polynomial (MvPolynomial τ ℤ)) (q : MvPolynomial τ ℤ)
    (n : ℕ) : MvPolynomial τ ℤ :=
  ∑ k ∈ Finset.range n, if Even k then 0 else P.coeff k * q ^ (k / 2)

theorem eval₂_eq_parts {τ : Type*} (P : Polynomial (MvPolynomial τ ℤ)) (q : MvPolynomial τ ℤ)
    {n : ℕ} (hn : P.natDegree < n) (x : τ → ℝ) (s0 : ℝ) (hs : s0 ^ 2 = pe x q) :
    Polynomial.eval₂ (pe x) s0 P = pe x (evenPart P q n) + s0 * pe x (oddPart P q n) := by
  rw [Polynomial.eval₂_eq_sum_range' _ hn, evenPart, oddPart, map_sum, map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with he | ho
  · have hk : 2 * (k / 2) = k := Nat.two_mul_div_two_of_even he
    rw [ite_eq_left he, ite_eq_left he, map_zero, mul_zero, add_zero, map_mul, map_pow, ← hs, ← pow_mul, hk]
  · have hk : 2 * (k / 2) + 1 = k := Nat.two_mul_div_two_add_one_of_odd ho
    have hne : ¬ Even k := Nat.not_even_iff_odd.mpr ho
    rw [ite_eq_right hne, ite_eq_right hne, map_zero, zero_add, map_mul, map_pow]
    have hpow : s0 ^ k = s0 * (s0 ^ 2) ^ (k / 2) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    rw [hpow, hs]
    ring

theorem SizeLE.evenPart {τ : Type*} {P : Polynomial (MvPolynomial τ ℤ)} {d M : ℕ}
    (hP : ∀ k, SizeLE (P.coeff k) d M) (q : MvPolynomial τ ℤ) (hq : SizeLE q 2 2) :
    SizeLE (evenPart P q (d + 1)) (2 * d) ((d + 1) * (M * 2 ^ d)) := by
  have h := SizeLE.finsetSum (Finset.range (d + 1))
    (fun k => if Even k then P.coeff k * q ^ (k / 2) else 0) (d := 2 * d) (M := M * 2 ^ d)
    (fun k hk => by
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      split_ifs
      · refine ((hP k).mul (hq.pow (k / 2))).mono ?_ ?_
        · have : k / 2 * 2 ≤ d := (Nat.div_mul_le_self k 2).trans hkd
          omega
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
            ((Nat.div_le_self k 2).trans hkd))
      · exact SizeLE.zero _ _)
  simpa [Deformation.evenPart] using h

theorem SizeLE.oddPart {τ : Type*} {P : Polynomial (MvPolynomial τ ℤ)} {d M : ℕ}
    (hP : ∀ k, SizeLE (P.coeff k) d M) (q : MvPolynomial τ ℤ) (hq : SizeLE q 2 2) :
    SizeLE (oddPart P q (d + 1)) (2 * d) ((d + 1) * (M * 2 ^ d)) := by
  have h := SizeLE.finsetSum (Finset.range (d + 1))
    (fun k => if Even k then 0 else P.coeff k * q ^ (k / 2)) (d := 2 * d) (M := M * 2 ^ d)
    (fun k hk => by
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      split_ifs
      · exact SizeLE.zero _ _
      · refine ((hP k).mul (hq.pow (k / 2))).mono ?_ ?_
        · have : k / 2 * 2 ≤ d := (Nat.div_mul_le_self k 2).trans hkd
          omega
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
            ((Nat.div_le_self k 2).trans hkd)))
  simpa [Deformation.oddPart] using h

/-! ### The norm in `s` -/

/-- **Norm eliminant.** -/
theorem exists_norm_eliminant (Φ : MvPolynomial (Option (Fin 3)) ℤ) {d M : ℕ}
    (hΦ : SizeLE Φ d M)
    (hfin : ∀ v : Fin 3 → ℝ, {t : ℝ | pe (fun o => Option.elim o t v) Φ = 0}.Finite) :
    ∃ Nrm : MvPolynomial (Fin 3) ℤ, Nrm ≠ 0 ∧
      SizeLE Nrm (4 * d + 2) (3 * ((d + 1) * (M * 2 ^ d)) ^ 2) ∧
      ∀ t lam c0 s0 : ℝ, c0 ^ 2 + s0 ^ 2 = 1 →
        pe (fun o => Option.elim o t ![lam, c0, s0]) Φ = 0 → pe ![t, lam, c0] Nrm = 0 := by
  classical
  -- move `s` to the distinguished variable
  let e : Option (Fin 3) → Option (Fin 3) := fun o => Option.elim o (some 0) ![some 1, some 2, none]
  set Ψ := rename e Φ with hΨ
  have hΨev : ∀ t lam c0 s0 : ℝ, pe (fun o => Option.elim o s0 ![t, lam, c0]) Ψ =
      pe (fun o => Option.elim o t ![lam, c0, s0]) Φ := by
    intro t lam c0 s0
    rw [hΨ, ev_rename]
    have hfun : ((fun o : Option (Fin 3) => Option.elim o s0 ![t, lam, c0]) ∘ e) =
        fun o => Option.elim o t ![lam, c0, s0] := by
      funext o
      rcases o with _ | i
      · rfl
      · fin_cases i <;> rfl
    rw [hfun]
  have hΨsz : SizeLE Ψ d M := hΦ.rename e
  set P := optionEquivLeft ℤ (Fin 3) Ψ with hP
  have hPdeg : P.natDegree < d + 1 :=
    Nat.lt_succ_of_le ((natDegree_optionEquivLeft_le Ψ).trans hΨsz.1)
  have hPc : ∀ k, SizeLE (P.coeff k) d M := fun k => hΨsz.coeff_optionEquivLeft k
  set q : MvPolynomial (Fin 3) ℤ := 1 - X 2 ^ 2 with hq
  have hqsz : SizeLE q 2 2 := by
    have := (SizeLE.one (σ := Fin 3)).mono (Nat.zero_le 2) le_rfl |>.add
      ((SizeLE.X (σ := Fin 3) 2).pow 2).neg
    simpa [hq, sub_eq_add_neg] using this
  set U := evenPart P q (d + 1)
  set V := oddPart P q (d + 1)
  have hUsz := SizeLE.evenPart hPc q hqsz
  have hVsz := SizeLE.oddPart hPc q hqsz
  refine ⟨U ^ 2 - q * V ^ 2, ?_, ?_, ?_⟩
  · -- nonvanishing at `λ = c = 0`, `s = ±1`
    have hfin2 := (hfin ![0, 0, 1]).union (hfin ![0, 0, -1])
    obtain ⟨t, ht⟩ := hfin2.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    intro hzero
    have hev := congrArg (pe ![t, 0, 0]) hzero
    rw [map_zero] at hev
    have hqv : pe ![t, (0 : ℝ), 0] q = 1 := by simp [hq, ev_X]
    have h1 : pe (fun o => Option.elim o t ![0, 0, 1]) Φ =
        pe ![t, 0, 0] U + 1 * pe ![t, 0, 0] V := by
      rw [← hΨev, ev_option]
      exact eval₂_eq_parts P q hPdeg _ _ (by rw [hqv]; norm_num)
    have h2 : pe (fun o => Option.elim o t ![0, 0, -1]) Φ =
        pe ![t, 0, 0] U + -1 * pe ![t, 0, 0] V := by
      rw [← hΨev, ev_option]
      exact eval₂_eq_parts P q hPdeg _ _ (by rw [hqv]; norm_num)
    have hprod : pe ![t, (0 : ℝ), 0] (U ^ 2 - q * V ^ 2) =
        pe (fun o => Option.elim o t ![0, 0, 1]) Φ *
          pe (fun o => Option.elim o t ![0, 0, -1]) Φ := by
      rw [h1, h2, map_sub, map_mul, map_pow, map_pow, hqv]
      ring
    rw [hprod] at hev
    exact (mul_ne_zero ht.1 ht.2) hev
  · have h1 := hUsz.pow 2
    have h2 := hqsz.mul (hVsz.pow 2)
    have := (h1.mono (by omega : 2 * (2 * d) ≤ 4 * d + 2) le_rfl).add
      (h2.neg.mono (by omega : 2 + 2 * (2 * d) ≤ 4 * d + 2) le_rfl)
    rw [← sub_eq_add_neg] at this
    refine this.mono le_rfl (le_of_eq ?_)
    ring
  · intro t lam c0 s0 hcs hΦ0
    have hqv : pe ![t, lam, c0] q = 1 - c0 ^ 2 := by simp [hq, ev_X]
    have hs : s0 ^ 2 = pe ![t, lam, c0] q := by rw [hqv]; linarith
    have hs' : (-s0) ^ 2 = pe ![t, lam, c0] q := by rw [neg_sq]; exact hs
    have hpos := eval₂_eq_parts P q hPdeg ![t, lam, c0] s0 hs
    rw [← ev_option, hΨev, hΦ0] at hpos
    have hneg := eval₂_eq_parts P q hPdeg ![t, lam, c0] (-s0) hs'
    rw [map_sub, map_mul, map_pow, map_pow, ← hs]
    have : pe ![t, lam, c0] U = -(s0 * pe ![t, lam, c0] V) := by linarith
    rw [this]
    ring

/-! ### The leading coefficient in `λ` -/

theorem continuous_ev {σ : Type*} (p : MvPolynomial σ ℤ) :
    Continuous fun x : σ → ℝ => pe x p := by
  have h : (fun x : σ → ℝ => pe x p) =
      fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℝ) p) := by
    funext x
    simp only [PhysicalPolynomial.eval, coe_eval₂Hom]
    rw [eval₂_eq_eval_map]
  rw [h]
  exact MvPolynomial.continuous_eval _

/-- **Leading coefficient and limit.** -/
theorem exists_limit_eliminant (Nrm : MvPolynomial (Fin 3) ℤ) (hN : Nrm ≠ 0) {dN MN : ℕ}
    (hsz : SizeLE Nrm dN MN) :
    ∃ A0 : MvPolynomial (Fin 2) ℤ, A0 ≠ 0 ∧ SizeLE A0 dN MN ∧
      ∀ (c0 tstar : ℝ) (lamS tS : ℕ → ℝ), Tendsto lamS atTop atTop →
        Tendsto tS atTop (𝓝 tstar) → (∀ n, pe ![tS n, lamS n, c0] Nrm = 0) →
          pe ![tstar, c0] A0 = 0 := by
  classical
  let e2 : Fin 3 → Option (Fin 2) := ![some 0, none, some 1]
  have he2 : Function.Injective e2 := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [e2]
  set N2 := rename e2 Nrm with hN2
  have hN2ne : N2 ≠ 0 := fun h => hN ((rename_injective e2 he2) (by rw [← hN2, h, map_zero]))
  set PN := optionEquivLeft ℤ (Fin 2) N2 with hPN
  have hPNne : PN ≠ 0 := fun h => hN2ne ((optionEquivLeft ℤ (Fin 2)).injective (by rw [← hPN, h,
    map_zero]))
  refine ⟨PN.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hPNne,
    (hsz.rename e2).coeff_optionEquivLeft _, ?_⟩
  intro c0 tstar lamS tS hlam ht hzero
  set J := PN.natDegree
  let a : ℕ → ℝ → ℝ := fun j t => pe ![t, c0] (PN.coeff j)
  have hNev : ∀ t lam : ℝ, pe ![t, lam, c0] Nrm = ∑ j ∈ Finset.range (J + 1), a j t * lam ^ j := by
    intro t lam
    have h1 : pe ![t, lam, c0] Nrm = pe (fun o => Option.elim o lam ![t, c0]) N2 := by
      rw [hN2, ev_rename]
      have hfun : ((fun o : Option (Fin 2) => Option.elim o lam ![t, c0]) ∘ e2) = ![t, lam, c0] := by
        funext i
        fin_cases i <;> rfl
      rw [hfun]
    rw [h1, ev_option, Polynomial.eval₂_eq_sum_range]
  let f : ℝ × ℝ → ℝ := fun z => ∑ j ∈ Finset.range (J + 1), a j z.2 * z.1 ^ (J - j)
  have hfcont : Continuous f := by
    refine continuous_finsetSum _ fun j _ => ?_
    refine Continuous.mul ?_ (continuous_fst.pow _)
    exact (continuous_ev _).comp (continuous_pi fun i => by
      fin_cases i
      · exact continuous_snd
      · exact continuous_const)
  have hf0 : f (0, tstar) = a J tstar := by
    simp only [f]
    rw [Finset.sum_eq_single J]
    · simp
    · intro j hj hjJ
      have : 0 < J - j := by
        have := Finset.mem_range.mp hj
        omega
      rw [zero_pow this.ne', mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self J)) h
  have hfseq : ∀ᶠ n in atTop, f ((lamS n)⁻¹, tS n) = 0 := by
    filter_upwards [hlam.eventually_gt_atTop 0] with n hn
    have hz := hzero n
    rw [hNev] at hz
    simp only [f]
    have : ∑ j ∈ Finset.range (J + 1), a j (tS n) * (lamS n)⁻¹ ^ (J - j) =
        ((lamS n) ^ J)⁻¹ * ∑ j ∈ Finset.range (J + 1), a j (tS n) * lamS n ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [inv_pow, pow_sub₀ _ hn.ne' hjJ, mul_inv, inv_inv]
      ring
    rw [this, hz, mul_zero]
  have hlim : Tendsto (fun n => f ((lamS n)⁻¹, tS n)) atTop (𝓝 (f (0, tstar))) :=
    (hfcont.tendsto _).comp ((tendsto_inv_atTop_zero.comp hlam).prodMk_nhds ht)
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hfseq.mono fun n hn => hn.symm))
  rw [hf0] at this
  exact this

end NLQCLean.Deformation
