import NLQCLean.Arithmetic.ControlledPhaseLeastDeficit
import NLQCLean.External.EffectiveArithmetic

/-!
# The epigraph formula of the least controlled-phase deficit

Step 3 of the proof of `thm:explicit`. For an attaining architecture `t` of
the polynomial model, the existential formula in the free variables `(y, c)`

`∃ s, x : σ s ≥ 0 ∧ c² + s² = 1 ∧ constraints(x) = 0 ∧ 16 - 16 y - score(c, s, x) ≤ 0`,

with `σ = sign sin θ`, uses four integer polynomials of total degree at most
`12` and coefficient bit size at most `56 + 14 K`. At `c = cos θ` the point
`y = g_K(θ)` satisfies it, while no `y < g_K(θ)` does. Any quantifier-free sign
formula equivalent to it therefore has an atom whose nonzero polynomial
vanishes at `(g_K(θ), cos θ)`.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial

section BoundaryAtom

/-- Every atom of a finite integer sign formula is locally constant at a point
where its polynomial is either zero or does not vanish. -/
theorem IntSignAtom.eventually_holds_iff {n : ℕ} (A : IntSignAtom n) (p : Fin n → ℝ)
    (h : A.polynomial = 0 ∨ MvPolynomial.eval₂ (Int.castRingHom ℝ) p A.polynomial ≠ 0) :
    ∀ᶠ q in nhds p, (A.Holds q ↔ A.Holds p) := by
  rcases h with h0 | hne
  · exact Filter.Eventually.of_forall fun q => by simp [IntSignAtom.Holds, h0]
  · have hcont : Continuous fun q : Fin n → ℝ =>
        MvPolynomial.eval₂ (Int.castRingHom ℝ) q A.polynomial := by
      have := MvPolynomial.continuous_eval (A.polynomial.map (Int.castRingHom ℝ))
      simpa [MvPolynomial.eval_map] using this
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hneg)] with q hq
      simp only [IntSignAtom.Holds, sign_neg hq, sign_neg hneg]
    · filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
      simp only [IntSignAtom.Holds, sign_pos hq, sign_pos hpos]

/-- **Boundary atom.** If a quantifier-free integer sign formula holds at `p`
but fails at points arbitrarily close to `p`, then one of its atoms has a
nonzero polynomial vanishing at `p`. -/
theorem IntSignDNF.exists_atom_zero_of_boundary {n : ℕ} (Ψ : IntSignDNF n) {p : Fin n → ℝ}
    (hp : Ψ.Holds p) (hnear : ∀ δ > 0, ∃ q, dist q p < δ ∧ ¬ Ψ.Holds q) :
    ∃ L ∈ Ψ, ∃ A ∈ L, A.polynomial ≠ 0 ∧
      MvPolynomial.eval₂ (Int.castRingHom ℝ) p A.polynomial = 0 := by
  classical
  by_contra hno
  push Not at hno
  let S : Set (IntSignAtom n) := ⋃ L ∈ {L | L ∈ Ψ}, {A | A ∈ L}
  have hS : S.Finite := (List.finite_toSet Ψ).biUnion fun L _ => List.finite_toSet L
  have hev : ∀ᶠ q in nhds p, ∀ A ∈ S, (A.Holds q ↔ A.Holds p) := by
    apply (Filter.eventually_all_finite hS).mpr
    intro A hA
    simp only [S, Set.mem_iUnion, Set.mem_ofPred_eq] at hA
    obtain ⟨L, hL, hAL⟩ := hA
    apply A.eventually_holds_iff p
    by_cases h0 : A.polynomial = 0
    · exact Or.inl h0
    · exact Or.inr (hno L hL A hAL h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨q, hq, hnot⟩ := hnear δ hδ
  apply hnot
  obtain ⟨L, hL, hall⟩ := hp
  refine ⟨L, hL, fun A hA => ?_⟩
  have hAS : A ∈ S := by
    simp only [S, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨L, hL, hA⟩
  exact (hball hq A hAS).mpr (hall A hA)

end BoundaryAtom

namespace ExplicitGate

variable (t : Fin 8 → ℕ)

/-- The bound variables: the sine coordinate and the raw physical coordinates. -/
abbrev BoundIndex := Unit ⊕ PhysicalCoordinateIndex 2 t

/-- Free variable `0` is the deficit level `y`, free variable `1` the cosine `c`. -/
def scoreRename : PhaseScoreCoordinateIndex t → Fin 2 ⊕ BoundIndex t :=
  Sum.elim ![Sum.inl 1, Sum.inr (Sum.inl ())] fun i => Sum.inr (Sum.inr i)

def constraintRename : PhysicalCoordinateIndex 2 t → Fin 2 ⊕ BoundIndex t :=
  fun i => Sum.inr (Sum.inr i)

theorem scoreRename_injective : Function.Injective (scoreRename t) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v
  · fin_cases u <;> fin_cases v <;> simp_all [scoreRename]
  · fin_cases u <;> simp_all [scoreRename]
  · fin_cases v <;> simp_all [scoreRename]
  · simp_all [scoreRename]

theorem constraintRename_injective : Function.Injective (constraintRename t) := by
  intro u v h
  simpa [constraintRename] using h

/-- The four epigraph polynomials, with sine-sign `σ`. -/
noncomputable def epigraphPolynomials (σ : ℤ) : Fin 4 → MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ :=
  ![C σ * X (Sum.inr (Sum.inl ())),
    X (Sum.inl 1) ^ 2 + X (Sum.inr (Sum.inl ())) ^ 2 - 1,
    rename (constraintRename t) (physicalConstraintSumSquares 2 t),
    C 16 - C 16 * X (Sum.inl 0) - rename (scoreRename t) (controlledPhaseScoreNumeratorPolynomial t)]

/-- `σ s ≥ 0`, `c² + s² = 1`, constraints vanish and `16 - 16 y - score ≤ 0`. -/
def epigraphFormula (v : Fin 4 → SignType) : Prop :=
  v 0 ≠ -1 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 ≠ 1

theorem epigraphPolynomials_totalDegree_le (σ : ℤ) (i : Fin 4) :
    (epigraphPolynomials t σ i).totalDegree ≤ 12 := by
  have hX : ∀ j : Fin 2 ⊕ BoundIndex t, (X j : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).totalDegree ≤ 1 :=
    fun j => (totalDegree_X j).le
  fin_cases i
  · calc (C σ * X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).totalDegree
        ≤ (C σ : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).totalDegree +
            (X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).totalDegree :=
          totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add (le_of_eq (totalDegree_C σ)) (hX _)
      _ ≤ 12 := by norm_num
  · have h1 := (totalDegree_pow (X (Sum.inl 1) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ) 2).trans
      (Nat.mul_le_mul_left 2 (hX _))
    have h2 := (totalDegree_pow (X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ)
      2).trans (Nat.mul_le_mul_left 2 (hX _))
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
    · exact h1.trans (by norm_num)
    · exact h2.trans (by norm_num)
    · exact totalDegree_one.le.trans (Nat.zero_le _)
  · exact (totalDegree_rename_le _ _).trans
      ((physicalConstraintSumSquares_degree_le 2 t).trans (by norm_num))
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
    · exact (totalDegree_C _).le.trans (Nat.zero_le _)
    · exact (totalDegree_mul _ _).trans (by
        rw [totalDegree_C]
        exact (Nat.zero_add _).le.trans ((hX _).trans (by norm_num)))
    · exact (totalDegree_rename_le _ _).trans (controlledPhaseScoreNumeratorPolynomial_degree_le t)

theorem natAbs_coeff_rename_le {σ τ' : Type*} {f : σ → τ'} (hf : Function.Injective f)
    (p : MvPolynomial σ ℤ) {B : ℕ} (h : ∀ m, (p.coeff m).natAbs ≤ B) (m : τ' →₀ ℕ) :
    ((rename f p).coeff m).natAbs ≤ B := by
  classical
  by_cases hm : ∃ u, Finsupp.mapDomain f u = m
  · obtain ⟨u, rfl⟩ := hm
    rw [coeff_rename_mapDomain f hf]
    exact h u
  · rw [coeff_rename_eq_zero f p m (fun u hu => absurd ⟨u, hu⟩ hm)]
    simp

theorem natAbs_coeff_X_le {σ : Type*} (j : σ) (m : σ →₀ ℕ) :
    ((X j : MvPolynomial σ ℤ).coeff m).natAbs ≤ 1 := by
  classical
  rw [coeff_X]
  split_ifs <;> simp

theorem natAbs_coeff_X_sq_le {σ : Type*} (j : σ) (m : σ →₀ ℕ) :
    (((X j : MvPolynomial σ ℤ) ^ 2).coeff m).natAbs ≤ 1 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial]
  split_ifs <;> simp

theorem natAbs_coeff_C_le {σ : Type*} (a : ℤ) (m : σ →₀ ℕ) :
    ((C a : MvPolynomial σ ℤ).coeff m).natAbs ≤ a.natAbs := by
  classical
  rw [coeff_C]
  split_ifs <;> simp

theorem two_pow_bit_bound (K : ℕ) : 32 + 2 ^ 51 * K ^ 14 < 2 ^ (56 + 14 * K) := by
  have hK : K ^ 14 ≤ 2 ^ (14 * K) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 14
  have hX : 1 ≤ 2 ^ (14 * K) := Nat.one_le_two_pow
  rw [pow_add]
  have h56 : (2 : ℕ) ^ 56 = 32 * 2 ^ 51 := by norm_num
  rw [h56]
  nlinarith

/-- Every coefficient of the epigraph polynomials has bit size at most `56 + 14K`,
provided `σ = ±1` and the architecture lies in the `4K` box. -/
theorem epigraphPolynomials_bitsize {K : ℕ} (hK : 1 ≤ K) (hbox : ∀ i, t i ≤ 4 * K)
    {σ : ℤ} (hσ : σ.natAbs = 1) (i : Fin 4) :
    IntPolynomialBitsizeLE (epigraphPolynomials t σ i) (56 + 14 * K) := by
  have hbig := two_pow_bit_bound K
  have hcst := physicalConstraintSumSquares_massLE_of_four_mul_box hK t hbox
  have hsc := controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box t hbox
  have hK14 : 34406400 * K ^ 8 ≤ 2 ^ 51 * K ^ 14 :=
    (Nat.mul_le_mul_right _ (by norm_num)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hK (by norm_num)))
  intro m
  fin_cases i
  · change ((C σ * X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m).natAbs < _
    rw [coeff_C_mul, Int.natAbs_mul, hσ, one_mul]
    exact (natAbs_coeff_X_le _ m).trans_lt (by omega)
  · change ((X (Sum.inl 1) ^ 2 + X (Sum.inr (Sum.inl ())) ^ 2 - 1 :
      MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m).natAbs < _
    simp only [coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    have h1 := natAbs_coeff_X_sq_le (Sum.inl 1 : Fin 2 ⊕ BoundIndex t) m
    have h2 := natAbs_coeff_X_sq_le (Sum.inr (Sum.inl ()) : Fin 2 ⊕ BoundIndex t) m
    have h3 : ((1 : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m).natAbs ≤ 1 := by
      simpa using natAbs_coeff_C_le (σ := Fin 2 ⊕ BoundIndex t) 1 m
    have := Int.natAbs_sub_le ((X (Sum.inl 1) ^ 2).coeff m + (X (Sum.inr (Sum.inl ())) ^ 2).coeff m)
      ((1 : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m)
    have := Int.natAbs_add_le ((X (Sum.inl 1) ^ 2 : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m)
      ((X (Sum.inr (Sum.inl ())) ^ 2).coeff m)
    omega
  · change ((rename (constraintRename t) (physicalConstraintSumSquares 2 t)).coeff m).natAbs < _
    have h := natAbs_coeff_rename_le (constraintRename_injective t) _
      (fun m' => hcst.coefficient_natAbs_le m') m
    omega
  · change ((C 16 - C 16 * X (Sum.inl 0) - rename (scoreRename t)
      (controlledPhaseScoreNumeratorPolynomial t) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m).natAbs < _
    rw [coeff_sub, coeff_sub, coeff_C_mul]
    have h1 := natAbs_coeff_C_le (σ := Fin 2 ⊕ BoundIndex t) 16 m
    have h2 := natAbs_coeff_X_le (Sum.inl 0 : Fin 2 ⊕ BoundIndex t) m
    have h3 := natAbs_coeff_rename_le (scoreRename_injective t) _
      (fun m' => hsc.coefficient_natAbs_le m') m
    have := Int.natAbs_sub_le ((C 16 : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m -
      16 * (X (Sum.inl 0)).coeff m) ((rename (scoreRename t)
        (controlledPhaseScoreNumeratorPolynomial t)).coeff m)
    have := Int.natAbs_sub_le ((C 16 : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m)
      (16 * (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m)
    have h4 : (16 * (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ BoundIndex t) ℤ).coeff m).natAbs ≤ 16 := by
      rw [Int.natAbs_mul]
      simpa using Nat.mul_le_mul_left 16 h2
    change _ ≤ 16 at h1
    omega

section Evaluation

variable {t} (y : Fin 2 → ℝ) (x : BoundIndex t → ℝ)

theorem eval_epigraph_zero (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (epigraphPolynomials t σ 0) =
      σ * x (Sum.inl ()) := by
  simp only [epigraphPolynomials, Matrix.cons_val_zero, eval₂_mul, eval₂_C, eval₂_X,
    Sum.elim_inr]
  simp

theorem eval_epigraph_one (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (epigraphPolynomials t σ 1) =
      y 1 ^ 2 + x (Sum.inl ()) ^ 2 - 1 := by
  simp [epigraphPolynomials]

theorem eval_epigraph_two (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (epigraphPolynomials t σ 2) =
      eval (fun i => x (Sum.inr i)) (physicalConstraintSumSquares 2 t) := by
  simp only [epigraphPolynomials, Matrix.cons_val, eval₂_rename]
  rfl

theorem eval_epigraph_three (σ : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (epigraphPolynomials t σ 3) =
      16 - 16 * y 0 - eval (Sum.elim ![y 1, x (Sum.inl ())] fun i => x (Sum.inr i))
        (controlledPhaseScoreNumeratorPolynomial t) := by
  have hcomp : (Sum.elim y x ∘ scoreRename t) =
      Sum.elim ![y 1, x (Sum.inl ())] fun i => x (Sum.inr i) := by
    funext u
    rcases u with u | u
    · fin_cases u <;> rfl
    · rfl
  simp only [epigraphPolynomials, Matrix.cons_val, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
    eval₂_rename, hcomp]
  simp
  rfl

end Evaluation

end ExplicitGate

open ExplicitGate

/-- **Epigraph boundary point.** For an attaining architecture of the
polynomial model and `σ = sign sin θ ≠ 0`, the existential epigraph formula
holds at `(g_K(θ), cos θ)` and fails at `(y, cos θ)` for every `y < g_K(θ)`. -/
theorem epigraph_boundary {K : ℕ} {θ : ℝ} (hsin : Real.sin θ ≠ 0)
    {t : Fin 8 → ℕ}
    (hupper : ∀ x : PhysicalBlocks 2 t,
      eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 →
      eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
          (controlledPhaseScoreNumeratorPolynomial t) ≤
        16 * (1 - controlledPhaseLeastDeficit K θ))
    (hattain : ∃ x : PhysicalBlocks 2 t,
      eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 ∧
      eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
          (controlledPhaseScoreNumeratorPolynomial t) =
        16 * (1 - controlledPhaseLeastDeficit K θ)) :
    let σ : ℤ := if 0 < Real.sin θ then 1 else -1
    let E : (Fin 2 → ℝ) → Prop := fun y => ∃ x : BoundIndex t → ℝ,
      epigraphFormula (fun i => SignType.sign
        (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (epigraphPolynomials t σ i)))
    E ![controlledPhaseLeastDeficit K θ, Real.cos θ] ∧
      ∀ y₀ < controlledPhaseLeastDeficit K θ, ¬ E ![y₀, Real.cos θ] := by
  intro σ E
  set g := controlledPhaseLeastDeficit K θ
  have hσsin : 0 < (σ : ℝ) * Real.sin θ := by
    by_cases h : 0 < Real.sin θ
    · simp [σ, h]
    · have hneg : Real.sin θ < 0 := lt_of_le_of_ne (not_lt.mp h) hsin
      simp [σ, h]
      linarith
  have hcoords (w : PhysicalCoordinateIndex 2 t → ℝ) (c s : ℝ) :
      phaseScoreCoordinates t c s ((physicalCoordinatesEquiv 2 t).symm w) =
        Sum.elim ![c, s] w := by
    simp [phaseScoreCoordinates]
  constructor
  · obtain ⟨xb, hx0, hxs⟩ := hattain
    refine ⟨Sum.elim (fun _ => Real.sin θ) (physicalCoordinatesEquiv 2 t xb), ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [eval_epigraph_zero]
      simp only [Sum.elim_inl]
      rw [sign_pos hσsin]
      decide
    · rw [eval_epigraph_one]
      simp [Real.cos_sq_add_sin_sq]
    · rw [eval_epigraph_two]
      simp only [Sum.elim_inr]
      rw [hx0]
      simp
    · rw [eval_epigraph_three]
      have hcoord : (Sum.elim ![(![g, Real.cos θ] : Fin 2 → ℝ) 1,
          Sum.elim (fun _ => Real.sin θ) (physicalCoordinatesEquiv 2 t xb) (Sum.inl ())]
          fun i => Sum.elim (fun _ : Unit => Real.sin θ) (physicalCoordinatesEquiv 2 t xb)
            (Sum.inr i)) = phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) xb := by
        funext u
        rcases u with u | u
        · fin_cases u <;> rfl
        · rfl
      rw [hcoord, hxs]
      have : (16 : ℝ) - 16 * (![g, Real.cos θ] : Fin 2 → ℝ) 0 - 16 * (1 - g) = 0 := by
        simp
        ring
      rw [this, sign_zero]
      decide
  · intro y₀ hy₀ ⟨x, h0, h1, h2, h3⟩
    dsimp only at h0 h1 h2 h3
    rw [eval_epigraph_zero] at h0
    rw [eval_epigraph_one] at h1
    rw [eval_epigraph_two] at h2
    rw [eval_epigraph_three] at h3
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
    have hcst : eval (physicalCoordinatesEquiv 2 t
        ((physicalCoordinatesEquiv 2 t).symm fun i => x (Sum.inr i)))
        (physicalConstraintSumSquares 2 t) = 0 := by
      simpa using sign_eq_zero_iff.mp h2
    have hle := hupper _ hcst
    rw [hcoords, ← hxs] at hle
    have hpos : 0 < 16 - 16 * y₀ - eval (Sum.elim ![Real.cos θ, x (Sum.inl ())]
        fun i => x (Sum.inr i)) (controlledPhaseScoreNumeratorPolynomial t) := by
      linarith
    exact h3 (sign_pos hpos)

end NLQCLean
