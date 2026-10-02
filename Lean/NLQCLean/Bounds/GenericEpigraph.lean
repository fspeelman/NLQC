import NLQCLean.Bounds.ExplicitGateEpigraph

/-!
# Boundary eliminants of polynomial optimization problems

The epigraph argument of `thm:explicit`, for an arbitrary finite coordinate set `κ`, an integer
constraint polynomial `Cst` of degree at most four (the physical points are its zero set) and an
integer score numerator `Sc(c, s, w)` of degree at most twelve with denominator `16`. If the
largest score at `(cos θ, sin θ)` is `16 (1 - g)` with `g > 0`, then one-block quantifier
elimination (E-QE) produces a nonzero integer polynomial `A(y, c)` vanishing at `(g, cos θ)`,
of degree at most `12^{a(|κ| + 2)}` and coefficients below `2^{τ 12^{a(|κ| + 2)}}`, where every
coefficient of `Cst` and `Sc` is below `2^τ - 32`.
-/

namespace NLQCLean.GenericEpigraph

open MvPolynomial PhysicalPolynomial ExplicitGate

variable {κ : Type}

/-- The quantified variables: the sine coordinate and the raw coordinates. -/
abbrev GBound (κ : Type) := Unit ⊕ κ

/-- Free variable `0` is the deficit level, free variable `1` the cosine. -/
def gScoreRename : Fin 2 ⊕ κ → Fin 2 ⊕ GBound κ :=
  Sum.elim ![Sum.inl 1, Sum.inr (Sum.inl ())] fun i => Sum.inr (Sum.inr i)

def gConstraintRename : κ → Fin 2 ⊕ GBound κ := fun i => Sum.inr (Sum.inr i)

theorem gScoreRename_injective : Function.Injective (gScoreRename (κ := κ)) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v
  · fin_cases u <;> fin_cases v <;> simp_all [gScoreRename]
  · fin_cases u <;> simp [gScoreRename] at h
  · fin_cases v <;> simp [gScoreRename] at h
  · simpa [gScoreRename] using h

theorem gConstraintRename_injective : Function.Injective (gConstraintRename (κ := κ)) := by
  intro u v h
  simpa [gConstraintRename] using h

/-- `σ s ≥ 0`, `c² + s² = 1`, constraint `= 0`, `16 - 16 y - score ≤ 0`. -/
noncomputable def gEpigraphPolynomials (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ)
    (σ : ℤ) : Fin 4 → MvPolynomial (Fin 2 ⊕ GBound κ) ℤ :=
  ![C σ * X (Sum.inr (Sum.inl ())),
    X (Sum.inl 1) ^ 2 + X (Sum.inr (Sum.inl ())) ^ 2 - 1,
    rename gConstraintRename Cst,
    C 16 - C 16 * X (Sum.inl 0) - rename gScoreRename Sc]

theorem gEpigraphPolynomials_totalDegree_le {Cst : MvPolynomial κ ℤ}
    {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ} (hCst : Cst.totalDegree ≤ 12) (hSc : Sc.totalDegree ≤ 12)
    (σ : ℤ) (i : Fin 4) : (gEpigraphPolynomials Cst Sc σ i).totalDegree ≤ 12 := by
  have hX : ∀ j : Fin 2 ⊕ GBound κ, (X j : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).totalDegree ≤ 1 :=
    fun j => (totalDegree_X j).le
  fin_cases i
  · calc (C σ * X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).totalDegree
        ≤ (C σ : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).totalDegree +
            (X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).totalDegree :=
          totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add (le_of_eq (totalDegree_C σ)) (hX _)
      _ ≤ 12 := by norm_num
  · have h1 := (totalDegree_pow (X (Sum.inl 1) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ) 2).trans
      (Nat.mul_le_mul_left 2 (hX _))
    have h2 := (totalDegree_pow (X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ)
      2).trans (Nat.mul_le_mul_left 2 (hX _))
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
    · exact h1.trans (by norm_num)
    · exact h2.trans (by norm_num)
    · exact totalDegree_one.le.trans (Nat.zero_le _)
  · exact (totalDegree_rename_le _ _).trans hCst
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
    · exact (totalDegree_C _).le.trans (Nat.zero_le _)
    · exact (totalDegree_mul _ _).trans (by
        rw [totalDegree_C]
        exact (Nat.zero_add _).le.trans ((hX _).trans (by norm_num)))
    · exact (totalDegree_rename_le _ _).trans hSc

theorem gEpigraphPolynomials_bitsize {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ}
    {H τ : ℕ} (hCst : ∀ m, (Cst.coeff m).natAbs ≤ H) (hSc : ∀ m, (Sc.coeff m).natAbs ≤ H)
    (hH : 32 + H < 2 ^ τ) {σ : ℤ} (hσ : σ.natAbs = 1) (i : Fin 4) :
    IntPolynomialBitsizeLE (gEpigraphPolynomials Cst Sc σ i) τ := by
  intro m
  fin_cases i
  · change ((C σ * X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m).natAbs < _
    rw [coeff_C_mul, Int.natAbs_mul, hσ, one_mul]
    exact (natAbs_coeff_X_le _ m).trans_lt (by omega)
  · change ((X (Sum.inl 1) ^ 2 + X (Sum.inr (Sum.inl ())) ^ 2 - 1 :
      MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m).natAbs < _
    simp only [coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    have h1 := natAbs_coeff_X_sq_le (Sum.inl 1 : Fin 2 ⊕ GBound κ) m
    have h2 := natAbs_coeff_X_sq_le (Sum.inr (Sum.inl ()) : Fin 2 ⊕ GBound κ) m
    have h3 : ((1 : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m).natAbs ≤ 1 := by
      simpa using natAbs_coeff_C_le (σ := Fin 2 ⊕ GBound κ) 1 m
    have := Int.natAbs_sub_le ((X (Sum.inl 1) ^ 2).coeff m + (X (Sum.inr (Sum.inl ())) ^ 2).coeff m)
      ((1 : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m)
    have := Int.natAbs_add_le ((X (Sum.inl 1) ^ 2 : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m)
      ((X (Sum.inr (Sum.inl ())) ^ 2).coeff m)
    omega
  · change ((rename gConstraintRename Cst).coeff m).natAbs < _
    have h := natAbs_coeff_rename_le gConstraintRename_injective _ hCst m
    omega
  · change ((C 16 - C 16 * X (Sum.inl 0) - rename gScoreRename Sc :
      MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m).natAbs < _
    rw [coeff_sub, coeff_sub, coeff_C_mul]
    have h1 := natAbs_coeff_C_le (σ := Fin 2 ⊕ GBound κ) 16 m
    have h2 := natAbs_coeff_X_le (Sum.inl 0 : Fin 2 ⊕ GBound κ) m
    have h3 := natAbs_coeff_rename_le gScoreRename_injective _ hSc m
    have := Int.natAbs_sub_le ((C 16 : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m -
      16 * (X (Sum.inl 0)).coeff m) ((rename gScoreRename Sc).coeff m)
    have := Int.natAbs_sub_le ((C 16 : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m)
      (16 * (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m)
    have h4 : (16 * (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ GBound κ) ℤ).coeff m).natAbs ≤ 16 := by
      rw [Int.natAbs_mul]
      simpa using Nat.mul_le_mul_left 16 h2
    change _ ≤ 16 at h1
    omega

section Evaluation

variable (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (y : Fin 2 → ℝ)
  (x : GBound κ → ℝ)

theorem eval_gEpigraph_zero (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (gEpigraphPolynomials Cst Sc σ 0) =
      σ * x (Sum.inl ()) := by
  simp only [gEpigraphPolynomials, Matrix.cons_val_zero, eval₂_mul, eval₂_C, eval₂_X,
    Sum.elim_inr]
  simp

theorem eval_gEpigraph_one (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (gEpigraphPolynomials Cst Sc σ 1) =
      y 1 ^ 2 + x (Sum.inl ()) ^ 2 - 1 := by
  simp [gEpigraphPolynomials]

theorem eval_gEpigraph_two (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (gEpigraphPolynomials Cst Sc σ 2) =
      eval (fun i => x (Sum.inr i)) Cst := by
  simp only [gEpigraphPolynomials, Matrix.cons_val, eval₂_rename]
  rfl

theorem eval_gEpigraph_three (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (gEpigraphPolynomials Cst Sc σ 3) =
      16 - 16 * y 0 - eval (Sum.elim ![y 1, x (Sum.inl ())] fun i => x (Sum.inr i)) Sc := by
  have hcomp : (Sum.elim y x ∘ gScoreRename) =
      Sum.elim ![y 1, x (Sum.inl ())] fun i => x (Sum.inr i) := by
    funext u
    rcases u with u | u
    · fin_cases u <;> rfl
    · rfl
  simp only [gEpigraphPolynomials, Matrix.cons_val, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
    eval₂_rename, hcomp]
  simp
  rfl

end Evaluation

/-- **Epigraph boundary point.** -/
theorem gEpigraph_boundary {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ}
    {θ g : ℝ} (hsin : Real.sin θ ≠ 0)
    (hupper : ∀ w : κ → ℝ, eval w Cst = 0 →
      eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc ≤ 16 * (1 - g))
    (hattain : ∃ w : κ → ℝ, eval w Cst = 0 ∧
      eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc = 16 * (1 - g)) :
    let σ : ℤ := if 0 < Real.sin θ then 1 else -1
    let E : (Fin 2 → ℝ) → Prop := fun y => ∃ x : GBound κ → ℝ,
      epigraphFormula (fun i => SignType.sign
        (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (gEpigraphPolynomials Cst Sc σ i)))
    E ![g, Real.cos θ] ∧ ∀ y₀ < g, ¬ E ![y₀, Real.cos θ] := by
  intro σ E
  have hσsin : 0 < (σ : ℝ) * Real.sin θ := by
    by_cases h : 0 < Real.sin θ
    · simp [σ, h]
    · have hneg : Real.sin θ < 0 := lt_of_le_of_ne (not_lt.mp h) hsin
      simp [σ, h]
      linarith
  constructor
  · obtain ⟨w, hw0, hws⟩ := hattain
    refine ⟨Sum.elim (fun _ => Real.sin θ) w, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [eval_gEpigraph_zero]
      simp only [Sum.elim_inl]
      rw [sign_pos hσsin]
      decide
    · rw [eval_gEpigraph_one]
      simp [Real.cos_sq_add_sin_sq]
    · rw [eval_gEpigraph_two]
      simp only [Sum.elim_inr]
      rw [hw0]
      simp
    · rw [eval_gEpigraph_three]
      have hcoord : (Sum.elim ![(![g, Real.cos θ] : Fin 2 → ℝ) 1,
          Sum.elim (fun _ => Real.sin θ) w (Sum.inl ())]
          fun i => Sum.elim (fun _ : Unit => Real.sin θ) w (Sum.inr i)) =
            Sum.elim ![Real.cos θ, Real.sin θ] w := by
        funext u
        rcases u with u | u
        · fin_cases u <;> rfl
        · rfl
      rw [hcoord, hws]
      have : (16 : ℝ) - 16 * (![g, Real.cos θ] : Fin 2 → ℝ) 0 - 16 * (1 - g) = 0 := by
        simp
        ring
      rw [this, sign_zero]
      decide
  · intro y₀ hy₀ ⟨x, h0, h1, h2, h3⟩
    dsimp only at h0 h1 h2 h3
    rw [eval_gEpigraph_zero] at h0
    rw [eval_gEpigraph_one] at h1
    rw [eval_gEpigraph_two] at h2
    rw [eval_gEpigraph_three] at h3
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1 h3
    have hs0 : 0 ≤ (σ : ℝ) * x (Sum.inl ()) := by
      by_contra hn
      exact h0 (sign_neg (lt_of_not_ge hn))
    have hcirc : x (Sum.inl ()) ^ 2 = Real.sin θ ^ 2 := by
      have := sign_eq_zero_iff.mp h1
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have hxs : x (Sum.inl ()) = Real.sin θ := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcirc with h | h
      · exact h
      · exfalso
        rw [h, mul_neg] at hs0
        linarith
    have hcst : eval (fun i => x (Sum.inr i)) Cst = 0 := sign_eq_zero_iff.mp h2
    have hle := hupper _ hcst
    rw [← hxs] at hle
    have hpos : 0 < 16 - 16 * y₀ - eval (Sum.elim ![Real.cos θ, x (Sum.inl ())]
        fun i => x (Sum.inr i)) Sc := by
      linarith
    exact h3 (sign_pos hpos)

/-- **Boundary eliminant.** Under E-QE (with its exponent `a`), a positive least deficit `g` of a
polynomial optimization problem with `|κ|` coordinates is a root, with `cos θ`, of a nonzero
integer polynomial of degree at most `M = 12^{a(|κ| + 2)}` and coefficients below `2^{τ M}`. -/
theorem exists_eliminant_of_family (hQE : BasuPollackRoyExistentialElimination) :
    ∃ a : ℕ, ∀ (κ : Type) [Fintype κ] (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ)
      (H τ : ℕ) (θ g : ℝ), 1 ≤ τ → Cst.totalDegree ≤ 12 → Sc.totalDegree ≤ 12 →
      (∀ m, (Cst.coeff m).natAbs ≤ H) → (∀ m, (Sc.coeff m).natAbs ≤ H) → 32 + H < 2 ^ τ →
      Real.sin θ ≠ 0 → 0 < g →
      (∀ w : κ → ℝ, eval w Cst = 0 →
        eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc ≤ 16 * (1 - g)) →
      (∃ w : κ → ℝ, eval w Cst = 0 ∧
        eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc = 16 * (1 - g)) →
      ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧
        A.totalDegree ≤ 12 ^ (a * (Fintype.card κ + 2)) ∧
        (∀ m, (A.coeff m).natAbs < 2 ^ (τ * 12 ^ (a * (Fintype.card κ + 2)))) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℝ) ![g, Real.cos θ] A = 0 := by
  obtain ⟨a, hqe⟩ := hQE
  refine ⟨a, fun κ _ Cst Sc H τ θ g hτ hCdeg hSdeg hCH hSH hH hsin hg hupper hattain => ?_⟩
  set σ : ℤ := if 0 < Real.sin θ then 1 else -1 with hσdef
  have hσ : σ.natAbs = 1 := by by_cases h : 0 < Real.sin θ <;> simp [σ, h]
  obtain ⟨Ψ, hΨbd, hΨ⟩ := hqe (GBound κ) 4 12 τ (by norm_num) hτ
    (gEpigraphPolynomials Cst Sc σ) (gEpigraphPolynomials_totalDegree_le hCdeg hSdeg σ)
    (gEpigraphPolynomials_bitsize hCH hSH hH hσ) epigraphFormula
  obtain ⟨hin, hout⟩ := gEpigraph_boundary (Cst := Cst) (Sc := Sc) hsin hupper hattain
  have hp : Ψ.Holds ![g, Real.cos θ] := (hΨ _).mpr hin
  have hnear : ∀ δ > 0, ∃ q, dist q ![g, Real.cos θ] < δ ∧ ¬ Ψ.Holds q := by
    intro δ hδ
    have hm : 0 < min (δ / 2) (g / 2) := lt_min (by linarith) (by linarith)
    refine ⟨![g - min (δ / 2) (g / 2), Real.cos θ], ?_, fun h => hout _ ?_ ((hΨ _).mp h)⟩
    · rw [dist_pi_lt_iff hδ]
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.dist_eq]
        rw [show g - min (δ / 2) (g / 2) - g = -min (δ / 2) (g / 2) by ring, abs_neg,
          abs_of_pos hm]
        exact (min_le_left _ _).trans_lt (by linarith)
      · simpa using hδ
    · linarith
  obtain ⟨L, hL, A, hA, hQ0, hQzero⟩ := Ψ.exists_atom_zero_of_boundary hp hnear
  obtain ⟨hdeg, hbits⟩ := hΨbd L hL A hA
  have hcard : Fintype.card (GBound κ) + 1 = Fintype.card κ + 2 := by
    simp only [GBound, Fintype.card_sum, Fintype.card_unit]
    ring
  rw [hcard] at hdeg hbits
  exact ⟨A.polynomial, hQ0, hdeg, hbits, hQzero⟩

end NLQCLean.GenericEpigraph
