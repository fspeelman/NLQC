import NLQCLean.Arithmetic.DeformationSystem
import NLQCLean.Arithmetic.EliminationKKT
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Critical points of the deformed problem

Fix real parameters `(λ, c₀, s₀)` with `λ > R₀`, and a feasible point `w` with value
`y* = Sc(c₀, s₀, w)` and `Σ wᵢ²⁶ + y*²⁶ < R₀`. The zero set of `Q_λ` is compact and
contains a point with `y ≥ y*` (intermediate value theorem in the `y` direction). At a
maximizer of `y` on it, the one-dimensional Lagrange rule gives `∂_{xᵢ} Q_λ = 0`, so every
polynomial of the deformed critical system vanishes there. Moreover `Q ≤ R₀/λ` and all
coordinates lie in `[−R₀, R₀]`.
-/

namespace NLQCLean.Deformation

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination NLQCLean.PurePower

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-! ### Mass of the lower-order parts -/

omit [Fintype κ] [DecidableEq κ] in
theorem massLE_Qpoly {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ} {HC HS : ℕ}
    (hCm : CoefficientMassLE Cst HC) (hSm : CoefficientMassLE Sc HS) :
    CoefficientMassLE (Qpoly Cst Sc) (HC ^ 2 + (1 + HS) ^ 2) := by
  have h1 : CoefficientMassLE (liftCst Cst) HC := (SizeLE.rename ⟨le_rfl, hCm⟩ _).2
  have h2 : CoefficientMassLE (liftSc Sc) HS := (SizeLE.rename ⟨le_rfl, hSm⟩ _).2
  exact (h1.pow 2).add (((CoefficientMassLE.variablePolynomial _).sub h2).pow 2)

theorem l1_rPoly_le {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ} {HC HS : ℕ}
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12)
    (hCm : CoefficientMassLE Cst HC) (hSm : CoefficientMassLE Sc HS) (R₀ : ℕ) (u : Option κ) :
    l1 (rPoly Cst Sc R₀ u) ≤
      26 * R₀ + (26 + 24 * Fintype.card κ) * (HC ^ 2 + (1 + HS) ^ 2) := by
  set MQ := HC ^ 2 + (1 + HS) ^ 2
  have hQ : SizeLE (Qpoly Cst Sc) 24 MQ := ⟨totalDegree_Qpoly hC hS, massLE_Qpoly hCm hSm⟩
  have hd : ∀ i : κ, CoefficientMassLE (pderiv (Sum.inl (some i)) (Qpoly Cst Sc)) (24 * MQ) :=
    fun i => (hQ.pderiv _).2
  rcases u with _ | i
  · refine l1_le ?_
    simp only [rPoly]
    have hsum : CoefficientMassLE (∑ i, X (Sum.inl (some i)) *
        pderiv (Sum.inl (some i)) (Qpoly Cst Sc) : Amb κ) (Fintype.card κ * (24 * MQ)) := by
      have := CoefficientMassLE.sum_uniform (fun i : κ => (X (Sum.inl (some i)) *
        pderiv (Sum.inl (some i)) (Qpoly Cst Sc) : Amb κ)) (H := 24 * MQ)
        (fun i => by simpa using (CoefficientMassLE.variablePolynomial _).mul (hd i))
      simpa using this
    have h := (CoefficientMassLE.constant (σ := Option κ ⊕ Fin 3) (26 * (R₀ : ℤ))).neg.add
      ((CoefficientMassLE.variablePolynomial (Sum.inr 0)).mul
        (((CoefficientMassLE.constant (26 : ℤ)).mul (massLE_Qpoly hCm hSm)).sub hsum))
    refine h.mono (le_of_eq ?_)
    simp only [Int.natAbs_mul, Int.natAbs_natCast, one_mul]
    norm_num
    ring
  · refine l1_le (((CoefficientMassLE.variablePolynomial _).mul (hd i)).mono ?_)
    nlinarith [Nat.zero_le MQ]

/-! ### Evaluation -/

theorem ev_rename {σ τ : Type*} (x : τ → ℝ) (f : σ → τ) (p : MvPolynomial σ ℤ) :
    PhysicalPolynomial.eval x (rename f p) = PhysicalPolynomial.eval (x ∘ f) p := by
  simp only [PhysicalPolynomial.eval, coe_eval₂Hom, eval₂_rename]

theorem ev_X {σ : Type*} (x : σ → ℝ) (i : σ) :
    PhysicalPolynomial.eval x (X i : MvPolynomial σ ℤ) = x i := by
  simp only [PhysicalPolynomial.eval, coe_eval₂Hom, eval₂_X]

theorem ev_C {σ : Type*} (x : σ → ℝ) (z : ℤ) :
    PhysicalPolynomial.eval x (C z : MvPolynomial σ ℤ) = z := by
  show eval₂ (Int.castRingHom ℝ) x (C z) = z
  rw [eval₂_C]
  rfl

omit [Fintype κ] [DecidableEq κ] in
theorem eval_liftCst (Cst : MvPolynomial κ ℤ) (x : Option κ → ℝ) (par : Fin 3 → ℝ) :
    eval (Sum.elim x par) (liftCst Cst) = eval (fun i => x (some i)) Cst := by
  rw [liftCst, ev_rename]
  rfl

omit [Fintype κ] [DecidableEq κ] in
theorem eval_liftSc (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (x : Option κ → ℝ) (par : Fin 3 → ℝ) :
    eval (Sum.elim x par) (liftSc Sc) = eval (Sum.elim ![par 1, par 2] fun i => x (some i)) Sc := by
  rw [liftSc, ev_rename]
  have h : (Sum.elim x par ∘ Sum.elim (fun j : Fin 2 => Sum.inr j.succ) fun i => Sum.inl (some i)) =
      Sum.elim ![par 1, par 2] fun i => x (some i) := by
    funext v
    rcases v with j | i
    · fin_cases j <;> rfl
    · rfl
  rw [h]

omit [Fintype κ] [DecidableEq κ] in
theorem eval_Qpoly (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ)
    (x : Option κ → ℝ) (par : Fin 3 → ℝ) :
    eval (Sum.elim x par) (Qpoly Cst Sc) = eval (fun i => x (some i)) Cst ^ 2 +
      (x none - eval (Sum.elim ![par 1, par 2] fun i => x (some i)) Sc) ^ 2 := by
  simp only [Qpoly, map_add, map_pow, map_sub, eval_liftCst, eval_liftSc, ev_X, Sum.elim_inl]

omit [DecidableEq κ] in
theorem eval_Gpoly (x : Option κ → ℝ) (par : Fin 3 → ℝ) :
    eval (Sum.elim x par) (Gpoly : Amb κ) = ∑ u, x u ^ 26 := by
  simp only [Gpoly, map_sum, map_pow, ev_X, Sum.elim_inl]

omit [DecidableEq κ] in
theorem eval_Qlam (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ)
    (x : Option κ → ℝ) (par : Fin 3 → ℝ) :
    eval (Sum.elim x par) (Qlam Cst Sc R₀) =
      ∑ u, x u ^ 26 - R₀ + par 0 * eval (Sum.elim x par) (Qpoly Cst Sc) := by
  simp only [Qlam, map_add, map_sub, map_mul, eval_Gpoly, ev_X, ev_C, Sum.elim_inr]
  push_cast
  ring

theorem continuous_eval_elim {σ : Type*} (p : MvPolynomial (σ ⊕ Fin 3) ℤ) (par : Fin 3 → ℝ) :
    Continuous fun x : σ → ℝ => eval (Sum.elim x par) p := by
  have h : (fun x : σ → ℝ => eval (Sum.elim x par) p) =
      (fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℝ) p)) ∘
        (fun x : σ → ℝ => Sum.elim x par) := by
    funext x
    simp only [PhysicalPolynomial.eval, coe_eval₂Hom, Function.comp_apply]
    rw [eval₂_eq_eval_map]
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp (continuous_pi fun v => ?_)
  rcases v with i | j
  · exact continuous_apply i
  · exact continuous_const

/-! ### Existence of a critical point -/

theorem abs_le_of_pow_le {t R : ℝ} (hR : 1 ≤ R) (h : t ^ 26 ≤ R) : |t| ≤ R := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 ≤ |t| := hR.trans hlt.le
  have : |t| ≤ |t| ^ 26 := le_self_pow₀ h1 (by norm_num)
  have h26 : |t| ^ 26 = t ^ 26 := by
    rw [show (26 : ℕ) = 2 * 13 by norm_num, pow_mul, pow_mul, sq_abs]
  linarith

/-- **Critical point of the deformed problem.** -/
theorem exists_critical_point (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) (R₀ : ℕ) (c₀ s₀ lam : ℝ)
    (hlam : (R₀ : ℝ) < lam) (w : κ → ℝ) (ystar : ℝ) (hw : eval w Cst = 0)
    (hwy : eval (Sum.elim ![c₀, s₀] w) Sc = ystar)
    (hGw : ∑ i, w i ^ 26 + ystar ^ 26 < R₀)
    (_hupper : ∀ v : κ → ℝ, eval v Cst = 0 → eval (Sum.elim ![c₀, s₀] v) Sc ≤ ystar) :
    ∃ p : Option κ → ℝ,
      (∀ u, eval (Sum.elim p ![lam, c₀, s₀]) ((sys Cst Sc R₀ hC hS).f u) = 0) ∧
      ystar ≤ p none ∧
      lam * eval (Sum.elim p ![lam, c₀, s₀]) (Qpoly Cst Sc) ≤ R₀ ∧
      ∀ u, |p u| ≤ R₀ := by
  classical
  set par : Fin 3 → ℝ := ![lam, c₀, s₀] with hpar
  set F : (Option κ → ℝ) → ℝ := fun x => eval (Sum.elim x par) (Qlam Cst Sc R₀) with hF
  have hFcont : Continuous F := continuous_eval_elim _ par
  have hQnn : ∀ x : Option κ → ℝ, 0 ≤ eval (Sum.elim x par) (Qpoly Cst Sc) := fun x => by
    rw [eval_Qpoly]; positivity
  have hR0 : (0 : ℝ) < R₀ := lt_of_le_of_lt (by positivity) hGw
  have hR1 : (1 : ℝ) ≤ R₀ := by
    have : 0 < R₀ := by exact_mod_cast hR0
    exact_mod_cast this
  have hlam0 : 0 < lam := hR0.trans hlam
  -- the zero set
  set Z : Set (Option κ → ℝ) := {x | F x = 0} with hZ
  have hZbound : ∀ x ∈ Z, (∑ u, x u ^ 26 ≤ R₀) ∧
      lam * eval (Sum.elim x par) (Qpoly Cst Sc) ≤ R₀ := by
    intro x hx
    simp only [hZ, Set.mem_ofPred_eq, hF, eval_Qlam] at hx
    have h0 : par 0 = lam := rfl
    rw [h0] at hx
    have hq := mul_nonneg hlam0.le (hQnn x)
    have hg : 0 ≤ ∑ u, x u ^ 26 := Finset.sum_nonneg fun u _ => by positivity
    constructor <;> linarith
  have hZbox : Z ⊆ Set.pi Set.univ fun _ => Set.Icc (-(R₀ : ℝ)) R₀ := by
    intro x hx u _
    have h26 : x u ^ 26 ≤ R₀ := by
      have := (hZbound x hx).1
      have hle : x u ^ 26 ≤ ∑ v, x v ^ 26 :=
        Finset.single_le_sum (f := fun v => x v ^ 26) (fun v _ => by positivity)
          (Finset.mem_univ u)
      linarith
    exact abs_le.mp (abs_le_of_pow_le hR1 h26)
  have hZcpt : IsCompact Z :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      (isClosed_eq hFcont continuous_const) hZbox
  -- a point with `y ≥ y*`
  set pstar : Option κ → ℝ := fun u => Option.elim u ystar w with hpstar
  set φ : ℝ → ℝ := fun t => F (Function.update pstar none (ystar + t)) with hφ
  have hφcont : Continuous φ :=
    hFcont.comp (continuous_const.update none (continuous_const.add continuous_id))
  have hQline : ∀ t, eval (Sum.elim (Function.update pstar none (ystar + t)) par) (Qpoly Cst Sc) =
      t ^ 2 := by
    intro t
    rw [eval_Qpoly]
    have h1 : (fun i => Function.update pstar none (ystar + t) (some i)) = w := by
      funext i; simp [pstar]
    simp only [h1, hw, Function.update_self]
    have h2 : eval (Sum.elim ![par 1, par 2] w) Sc = ystar := by
      rw [← hwy]; congr 2
    rw [h2]
    ring
  have hGline : ∀ t, ∑ u, Function.update pstar none (ystar + t) u ^ 26 =
      (ystar + t) ^ 26 + ∑ i, w i ^ 26 := by
    intro t
    rw [Fintype.sum_option]
    simp [pstar]
  have hφ0 : φ 0 < 0 := by
    simp only [hφ, hF, eval_Qlam, hQline, hGline]
    have h0 : par 0 = lam := rfl
    rw [h0]
    simp only [add_zero]
    nlinarith
  have hφ1 : 0 < φ 1 := by
    simp only [hφ, hF, eval_Qlam, hQline, hGline]
    have h0 : par 0 = lam := rfl
    rw [h0]
    have : 0 ≤ (ystar + 1) ^ 26 + ∑ i, w i ^ 26 :=
      add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)
    nlinarith
  obtain ⟨t0, ht0, hφt0⟩ := intermediate_value_Icc (zero_le_one' ℝ) hφcont.continuousOn
    ⟨hφ0.le, hφ1.le⟩
  have hZne : (Function.update pstar none (ystar + t0)) ∈ Z := hφt0
  -- the maximizer of `y`
  obtain ⟨p, hpZ, hpmax⟩ := hZcpt.exists_isMaxOn ⟨_, hZne⟩
    (continuous_apply (none : Option κ)).continuousOn
  have hpy : ystar ≤ p none := by
    have := hpmax hZne
    simp only [Set.mem_ofPred_eq, Function.update_self] at this
    linarith [ht0.1]
  -- Lagrange
  have hswap : ∀ x : Option κ → ℝ, F x = ev (Sum.elim par x) (rename Sum.swap (Qlam Cst Sc R₀)) := by
    intro x
    show PhysicalPolynomial.eval _ _ = PhysicalPolynomial.eval _ _
    rw [ev_rename]
    have : (Sum.elim par x ∘ Sum.swap : Option κ ⊕ Fin 3 → ℝ) = Sum.elim x par := by
      funext v; rcases v with u | j <;> rfl
    rw [this]
  have hstrict : HasStrictFDerivAt F (polyDeriv (rename Sum.swap (Qlam Cst Sc R₀)) par p) p := by
    have := hasStrictFDerivAt_ev (rename Sum.swap (Qlam Cst Sc R₀)) par p
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (hswap x).symm)
  have hextr : IsLocalExtrOn (fun x : Option κ → ℝ => x none) {x | F x = F p} p := by
    refine Or.inr (IsMaxOn.isLocalMaxOn fun x hx => ?_)
    have hxZ : x ∈ Z := by
      show F x = 0
      rw [show F x = F p from hx]
      exact hpZ
    exact hpmax hxZ
  obtain ⟨a, b, hab, hsum⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d hstrict
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option κ => ℝ) none).hasStrictFDerivAt
  have hpd : ∀ j : Option κ, polyDeriv (rename Sum.swap (Qlam Cst Sc R₀)) par p (Pi.single j 1) =
      eval (Sum.elim p par) (pderiv (Sum.inl j) (Qlam Cst Sc R₀)) := by
    intro j
    rw [polyDeriv_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    have : (Sum.inr j : Fin 3 ⊕ Option κ) = Sum.swap (Sum.inl j) := rfl
    rw [this, pderiv_rename Sum.swap_leftInverse.injective]
    show PhysicalPolynomial.eval _ _ = PhysicalPolynomial.eval _ _
    rw [ev_rename]
    have : (Sum.elim par p ∘ Sum.swap : Option κ ⊕ Fin 3 → ℝ) = Sum.elim p par := by
      funext v; rcases v with u | k <;> rfl
    rw [this]
  have hcrit : ∀ i : κ, eval (Sum.elim p par) (pderiv (Sum.inl (some i)) (Qlam Cst Sc R₀)) = 0 := by
    intro i
    have h1 := congrArg (fun L : (Option κ → ℝ) →L[ℝ] ℝ => L (Pi.single (some i) 1)) hsum
    have h2 := congrArg (fun L : (Option κ → ℝ) →L[ℝ] ℝ => L (Pi.single none 1)) hsum
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, zero_apply,
      hpd] at h1 h2
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero, ite_true, mul_one] at h1 h2
    have ha : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul, zero_add] at h2
      exact hab (by simp [ha0, h2])
    exact (mul_eq_zero.mp h1).resolve_left ha
  have hFp : F p = 0 := hpZ
  refine ⟨p, fun u => ?_, hpy, (hZbound p hpZ).2, fun u => ?_⟩
  · rcases u with _ | i
    · rw [sys_f_none, map_sub, map_mul, map_sum]
      have : eval (Sum.elim p par) (Qlam Cst Sc R₀) = 0 := hFp
      rw [this, mul_zero, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hcrit i, mul_zero]
    · rw [sys_f_some]
      exact hcrit i
  · exact abs_le.mpr (hZbox hpZ u (Set.mem_univ _))

end NLQCLean.Deformation
