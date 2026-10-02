import NLQCLean.Bounds.ExplicitControlledPhaseQE
import NLQCLean.Arithmetic.EliminationLagrangeSystem
import NLQCLean.Arithmetic.EliminationPhysicalLICQ

/-!
# The effective bound for `C₁` without external inputs

The least deficit `g = g_K(1)` is a root, together with `cos 1`, of an explicit nonzero
integer polynomial `α(y, c)`. The physical maximizer with Lagrange multipliers (the constraint
gradients are independent) is a real zero of the Lagrange system; at the generic parameter
point the system has no zero (`lagrangeSystem_generic`), so iterated resultants produce `α`,
of degree at most `L = (835 K²)^(2^(2 + 164 K²))` and coefficients at most
`(2⁵⁵ K¹⁴)^(L³)`. With the hypothesis-free measure for `e^i` this gives

`g_K(1) ≥ exp(-exp(exp(exp(171 K²))))`

with no hypothesis. The theorems assuming quantifier elimination (triple exponential) or both
arithmetic inputs (double exponential) are kept.
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial Elimination ExplicitGate ClassicalCommunication

/-- The independent equations among all physical equations. -/
def indepToConstraint (t : Fin 8 → ℕ) : IndepIndex t → PhysicalConstraintIndex 2 t :=
  Sum.map id (Sum.map Subtype.val (Sum.map Subtype.val (Sum.map Subtype.val Subtype.val)))

theorem indepConstraint_eq (t : Fin 8 → ℕ) (q : IndepIndex t) :
    indepConstraint t q = physicalConstraintPolynomial 2 t (indepToConstraint t q) := by
  rcases q with q | q | q | q | q <;> rfl

theorem card_NR_le (n : Type*) [Fintype n] [DecidableEq n] :
    Fintype.card (NR n) ≤ 2 * Fintype.card n ^ 2 := by
  calc Fintype.card (NR n) ≤ Fintype.card ((n × n) × Fin 2) := Fintype.card_subtype_le _
    _ = 2 * Fintype.card n ^ 2 := by simp [Fintype.card_prod]; ring

/-- With a physical point, the independent equations are at most one more than the raw
coordinates. -/
theorem card_indepIndex_le (t : Fin 8 → ℕ) (y : PhysicalBlocks 2 t) (hy : y ∈ physicalSet 2 t) :
    Fintype.card (IndepIndex t) ≤ 1 + physicalRawRealCoordinateCount 2 t := by
  obtain ⟨-, hA, hB, hDA, hDB⟩ := hy
  have cA := IsIsometry.card_le hA
  have cB := IsIsometry.card_le hB
  have cDA := IsIsometry.card_le hDA
  have cDB := IsIsometry.card_le hDB
  simp only [Fintype.card_prod, Fintype.card_fin] at cA cB cDA cDB
  have eA : Fintype.card (NR (EncoderAInputIndex 2 t)) ≤ 2 * ((t 2 * t 4) * (2 * t 0)) := by
    refine (card_NR_le _).trans (Nat.mul_le_mul_left 2 ?_)
    simp only [EncoderAInputIndex, Fintype.card_prod, Fintype.card_fin]
    rw [pow_two]; exact Nat.mul_le_mul_right _ cA
  have eB : Fintype.card (NR (EncoderBInputIndex 2 t)) ≤ 2 * ((t 3 * t 5) * (2 * t 1)) := by
    refine (card_NR_le _).trans (Nat.mul_le_mul_left 2 ?_)
    simp only [EncoderBInputIndex, Fintype.card_prod, Fintype.card_fin]
    rw [pow_two]; exact Nat.mul_le_mul_right _ cB
  have eDA : Fintype.card (NR (DecoderAInputIndex t)) ≤ 2 * ((2 * t 6) * (t 2 * t 5)) := by
    refine (card_NR_le _).trans (Nat.mul_le_mul_left 2 ?_)
    simp only [DecoderAInputIndex, Fintype.card_prod, Fintype.card_fin]
    rw [pow_two]; exact Nat.mul_le_mul_right _ cDA
  have eDB : Fintype.card (NR (DecoderBInputIndex t)) ≤ 2 * ((2 * t 7) * (t 3 * t 4)) := by
    refine (card_NR_le _).trans (Nat.mul_le_mul_left 2 ?_)
    simp only [DecoderBInputIndex, Fintype.card_prod, Fintype.card_fin]
    rw [pow_two]; exact Nat.mul_le_mul_right _ cDB
  change Fintype.card (Unit ⊕ (NR (EncoderAInputIndex 2 t) ⊕ (NR (EncoderBInputIndex 2 t) ⊕
    (NR (DecoderAInputIndex t) ⊕ NR (DecoderBInputIndex t))))) ≤ _
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_sum, physicalRawRealCoordinateCount]
  have h0 : 0 ≤ 2 * (t 0 * t 1) := Nat.zero_le _
  linarith

theorem ev_rename_inr {t : Fin 8 → ℕ} (a : Fin 2 → ℝ) (z : PhysicalCoordinateIndex 2 t → ℝ)
    (P : MvPolynomial (PhysicalCoordinateIndex 2 t) ℤ) :
    ev (Sum.elim a z) (MvPolynomial.rename Sum.inr P) = PhysicalPolynomial.eval z P := by
  simp [ev, eval₂_rename, PhysicalPolynomial.eval, Function.comp_def]

/-- **The hypothesis-free eliminant for `C₁`.** -/
theorem exists_controlledPhase_one_eliminant {K : ℕ} (hK : 1 ≤ K) :
    ∃ α : MvPolynomial (Fin 2) ℤ, α ≠ 0 ∧
      eval₂ (Int.castRingHom ℝ) ![controlledPhaseLeastDeficit K 1, Real.cos 1] α = 0 ∧
      α.totalDegree ≤ (5 * (167 * K ^ 2)) ^ (2 ^ (2 + 164 * K ^ 2)) ∧
      ∀ m, (α.coeff m).natAbs ≤
        (2 ^ 55 * K ^ 14) ^ (((5 * (167 * K ^ 2)) ^ (2 ^ (2 + 164 * K ^ 2))) ^ 3) := by
  classical
  obtain ⟨t, hbox, hcount, -, hFdeg, -, hFmass, hupper, ⟨y, hy, hFy⟩⟩ :=
    exists_controlledPhaseLeastDeficit_polynomial_certificate hK 1
  set g := controlledPhaseLeastDeficit K 1 with hg
  set F := controlledPhaseScoreNumeratorPolynomial t with hFdef
  set a : Fin 2 → ℝ := ![Real.cos 1, Real.sin 1] with ha
  set x := physicalCoordinatesEquiv 2 t y with hx
  have hyP : y ∈ physicalSet 2 t := (physicalConstraintSumSquares_eval_coordinates_eq_zero_iff 2 t y).mp hy
  have hphase : ∀ y' : PhysicalBlocks 2 t, phaseScoreCoordinates t (Real.cos 1) (Real.sin 1) y' =
      Sum.elim a (physicalCoordinatesEquiv 2 t y') := fun y' => rfl
  have hfeasx : ∀ q, PhysicalPolynomial.eval x (indepConstraint t q) = 0 := by
    have := (physicalSet_iff_indep t x).mp (by rw [hx, LinearEquiv.symm_apply_apply]; exact hyP)
    exact this
  -- Lagrange multipliers at the maximizer
  obtain ⟨μ, hμ⟩ := exists_multipliers_of_isMax (κ := Fin 2) F a
    (fun q => MvPolynomial.rename Sum.inr (indepConstraint t q)) x
    (fun q => by rw [ev_rename_inr]; exact hfeasx q)
    (fun x' hx' => by
      have hx'P : (physicalCoordinatesEquiv 2 t).symm x' ∈ physicalSet 2 t :=
        (physicalSet_iff_indep t x').mpr fun q => by rw [← ev_rename_inr a]; exact hx' q
      have h1 := hupper _ ((physicalConstraintSumSquares_eval_coordinates_eq_zero_iff 2 t _).mpr hx'P)
      rw [hphase, LinearEquiv.apply_symm_apply] at h1
      have h2 := hFy
      rw [hphase] at h2
      change ev (Sum.elim a x') F ≤ ev (Sum.elim a x) F
      change PhysicalPolynomial.eval (Sum.elim a x') F ≤ _ at h1
      change PhysicalPolynomial.eval (Sum.elim a x) F = _ at h2
      simp only [PhysicalPolynomial.eval, coe_eval₂Hom] at h1 h2
      simp only [ev]
      linarith)
    (fun b => by
      obtain ⟨δ, hδ⟩ := exists_line_of_physical t y hyP b
      refine ⟨δ, fun q => ?_⟩
      obtain ⟨B, hB⟩ := hδ q
      refine polyDeriv_eq_of_quadratic _ a x δ (b q) B fun s => ?_
      rw [ev_rename_inr, ev_rename_inr]
      exact hB s)
  -- the real zero of the Lagrange system
  set w : Unit ⊕ (PhysicalCoordinateIndex 2 t ⊕ IndepIndex t) → ℝ := Sum.elim (fun _ => Real.sin 1) (Sum.elim x μ) with hw
  set pt : SysVar (PhysicalCoordinateIndex 2 t) (IndepIndex t) → ℝ := Sum.elim ![g, Real.cos 1] w with hpt
  have hptF : ∀ G : MvPolynomial (Fin 2 ⊕ PhysicalCoordinateIndex 2 t) ℤ,
      eval₂ (Int.castRingHom ℝ) pt (liftF (Q := IndepIndex t) G) = ev (Sum.elim a x) G := by
    intro G
    rw [liftF, eval₂_rename]
    congr 1
    funext v
    rcases v with k | j
    · fin_cases k <;> rfl
    · rfl
  have hptH : ∀ G : MvPolynomial (PhysicalCoordinateIndex 2 t) ℤ,
      eval₂ (Int.castRingHom ℝ) pt (liftH (Q := IndepIndex t) G) = PhysicalPolynomial.eval x G := by
    intro G
    rw [liftH, eval₂_rename]
    rfl
  have hzero : ∀ e, eval₂ (Int.castRingHom ℝ) pt (lagrangeSystem F (indepConstraint t) e) = 0 := by
    rintro (_ | q | j | _)
    · show eval₂ (Int.castRingHom ℝ) pt (X cV ^ 2 + X σV ^ 2 - 1) = 0
      simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
      change Real.cos 1 ^ 2 + Real.sin 1 ^ 2 - 1 = 0
      rw [Real.cos_sq_add_sin_sq, sub_self]
    · show eval₂ (Int.castRingHom ℝ) pt (liftH (indepConstraint t q)) = 0
      rw [hptH]; exact hfeasx q
    · show eval₂ (Int.castRingHom ℝ) pt (liftF (pderiv (Sum.inr j) F) -
        ∑ q, X (lamV q) * liftH (pderiv j (indepConstraint t q))) = 0
      rw [eval₂_sub, eval₂_sum, hptF, hμ j, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [eval₂_mul, eval₂_X, hptH, pderiv_rename Sum.inr_injective, ev_rename_inr]
      rfl
    · show eval₂ (Int.castRingHom ℝ) pt (16 - 16 * X yV - liftF F) = 0
      rw [eval₂_sub, eval₂_sub, eval₂_mul, eval₂_X, hptF]
      have h16 : eval₂ (Int.castRingHom ℝ) pt (16 : MvPolynomial (SysVar (PhysicalCoordinateIndex 2 t) (IndepIndex t)) ℤ) = 16 :=
        map_ofNat (eval₂Hom (Int.castRingHom ℝ) pt) 16
      rw [h16]
      have h2 := hFy
      rw [hphase] at h2
      change PhysicalPolynomial.eval (Sum.elim a x) F = _ at h2
      simp only [PhysicalPolynomial.eval, coe_eval₂Hom] at h2
      change 16 - 16 * g - eval₂ (Int.castRingHom ℝ) (Sum.elim a x) F = 0
      rw [h2]; ring
  -- sizes
  have hF : SizeLE F 12 (2 ^ 51 * K ^ 14) := ⟨hFdeg, hFmass⟩
  have hh : ∀ q, SizeLE (indepConstraint t q) 2 (80 * K ^ 2) := fun q =>
    ⟨indepConstraint_degree_le t q, by
      rw [indepConstraint_eq]
      exact (physicalConstraintPolynomial_massLE (by omega : 1 ≤ 4 * K) t hbox _).mono
        (le_of_eq (by ring))⟩
  have hQcard : Fintype.card (IndepIndex t) ≤ 1 + 82 * K ^ 2 := (card_indepIndex_le t y hyP).trans (by omega)
  have hJcard : Fintype.card (PhysicalCoordinateIndex 2 t) ≤ 82 * K ^ 2 := by
    rw [card_physicalCoordinateIndex]; exact hcount
  have hK2 : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
  have hK14 : 1 ≤ K ^ 14 := Nat.one_le_pow _ _ hK
  have k2 : K ^ 2 ≤ K ^ 14 := Nat.pow_le_pow_right hK (by norm_num)
  have k4 : K ^ 4 ≤ K ^ 14 := Nat.pow_le_pow_right hK (by norm_num)
  set D := 167 * K ^ 2 with hD
  set M := 2 ^ 55 * K ^ 14 with hM
  have hD1 : 1 ≤ D := by omega
  have hM2 : 2 ≤ M := by
    calc 2 ≤ 2 ^ 55 * 1 := by norm_num
      _ ≤ M := Nat.mul_le_mul_left _ hK14
  have hsizeD : ∀ e, SizeLE (lagrangeSystem F (indepConstraint t) e) D M := by
    intro e
    refine (lagrangeSystem_size F (indepConstraint t) hF hh e).mono (by omega) ?_
    have hQ80 : 4 * Fintype.card (IndepIndex t) * (80 * K ^ 2) ≤ 320 * K ^ 2 + 26240 * K ^ 4 := by
      calc 4 * Fintype.card (IndepIndex t) * (80 * K ^ 2) ≤ 4 * (1 + 82 * K ^ 2) * (80 * K ^ 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQcard)
        _ = 320 * K ^ 2 + 26240 * K ^ 4 := by ring
    have : 13 * (2 ^ 51 * K ^ 14) + 4 * Fintype.card (IndepIndex t) * (80 * K ^ 2) + 32 ≤ M := by
      rw [hM]
      have h2 : (2 : ℕ) ^ 55 = 16 * 2 ^ 51 := by norm_num
      rw [h2]
      have hbig : 320 * K ^ 2 + 26240 * K ^ 4 + 32 ≤ 2 ^ 51 * K ^ 14 := by
        have : 320 * K ^ 2 + 26240 * K ^ 4 + 32 ≤ 26592 * K ^ 14 := by omega
        exact this.trans (Nat.mul_le_mul_right _ (by norm_num))
      nlinarith
    exact this
  have hcardE : Fintype.card (SysEq (PhysicalCoordinateIndex 2 t) (IndepIndex t)) ≤ D := by
    show Fintype.card (Unit ⊕ (IndepIndex t ⊕ (PhysicalCoordinateIndex 2 t ⊕ Unit))) ≤ D
    rw [Fintype.card_sum (α := Unit), Fintype.card_sum (α := IndepIndex t),
      Fintype.card_sum (α := PhysicalCoordinateIndex 2 t), Fintype.card_unit]
    omega
  have hcardW : Fintype.card (Unit ⊕ (PhysicalCoordinateIndex 2 t ⊕ IndepIndex t)) ≤
      2 + 164 * K ^ 2 := by
    rw [Fintype.card_sum (α := Unit), Fintype.card_sum (α := PhysicalCoordinateIndex 2 t),
      Fintype.card_unit]
    omega
  obtain ⟨α, hα0, hαsize, hαvan⟩ := elim_flat (Fintype.equivFin (Unit ⊕ (PhysicalCoordinateIndex 2 t ⊕ IndepIndex t)))
    (lagrangeSystem F (indepConstraint t)) hD1 (by omega) hcardE hsizeD
    (fun w' => lagrangeSystem_generic F (indepConstraint t) w')
  set n := Fintype.card (Unit ⊕ (PhysicalCoordinateIndex 2 t ⊕ IndepIndex t))
  have hdeg : elimDeg n D ≤ (5 * D) ^ (2 ^ (2 + 164 * K ^ 2)) :=
    (elimDeg_le n D).trans (Nat.pow_le_pow_right (by omega)
      (Nat.pow_le_pow_right (by norm_num) hcardW))
  refine ⟨α, hα0, hαvan ![g, Real.cos 1] w hzero, hαsize.1.trans hdeg, fun m => ?_⟩
  refine (hαsize.2.coefficient_natAbs_le m).trans ((elimMass_le n D M M hD1 hM2
    (Nat.le_self_pow (by positivity) _)).trans ?_)
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hdeg 3)

/-- The gap step: if `(g, cos 1)` is a root of a nonzero integer polynomial of degree at most
`M` with coefficients below `2^τ'`, and nonconstant integer polynomials of degree at most `2M`
and height at most `(M+1) 2^M 2^τ'` are at least `exp(-W)` at `e^i`, with `4M + τ' ≤ W`, then
`g ≥ exp(-2W)`. -/
theorem gap_ge_of_separation {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    {A : MvPolynomial (Fin 2) ℤ} (hA0 : A ≠ 0) {M τ' : ℕ}
    (hdeg : A.totalDegree ≤ M) (hbits : ∀ m, (A.coeff m).natAbs < 2 ^ τ')
    (hQzero : eval₂ (Int.castRingHom ℝ) ![g, Real.cos 1] A = 0) {W : ℝ}
    (hsmall : ((4 * M + τ' : ℕ) : ℝ) ≤ W)
    (hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      Real.exp (-W) ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖) :
    Real.exp (-(2 * W)) ≤ g := by
  have hzero : bivariateEval (bivariateOfMv A) (Real.cos 1) g = 0 := by
    rw [bivariateEval_bivariateOfMv]
    have hfun : (Fin.cons g (fun _ : Fin 1 => Real.cos 1) : Fin 2 → ℝ) = ![g, Real.cos 1] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]
    exact hQzero
  have hheight : BivariateHeightLE (bivariateOfMv A) ((2 : ℝ) ^ τ') :=
    bivariateOfMv_heightLE fun m => abs_intCast_le_of_natAbs_lt (hbits m)
  have hcert := bivariate_cosine_gap_lower_bound_of_complex_separation 1
    (bivariateOfMv_ne_zero hA0) (bivariateOfMv_degreeLE hdeg) (one_le_pow₀ (by norm_num))
    hheight hg0 hg1 hzero (Real.exp_pos _) hseparation
  have hW0 : (0 : ℝ) ≤ W := le_trans (Nat.cast_nonneg _) hsmall
  have hgap : Real.exp (-(2 * W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) /
      ((M + 1 : ℕ) ^ 3 * (2 : ℝ) ^ τ') := by
    have h2M : (2 : ℝ) ^ M ≤ Real.exp M := two_pow_nat_le_exp M
    have h2τ : (2 : ℝ) ^ τ' ≤ Real.exp τ' := two_pow_nat_le_exp τ'
    have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp M := natCast_succ_le_exp M
    have hmin : Real.exp (-((M : ℝ) + W)) ≤ min 1 (((2 : ℝ) ^ M)⁻¹ * Real.exp (-W)) := by
      apply le_min
      · rw [Real.exp_le_one_iff]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      · rw [show -((M : ℝ) + W) = -(M : ℝ) + -W by ring, Real.exp_add, Real.exp_neg]
        exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr h2M)
          (Real.exp_pos _).le
    have hden : ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ' ≤ Real.exp (3 * M + τ') := by
      rw [Real.exp_add, show (3 : ℝ) * M = M + M + M by ring, Real.exp_add, Real.exp_add]
      calc ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ'
          ≤ Real.exp M ^ 3 * Real.exp τ' := mul_le_mul (pow_le_pow_left₀ (by positivity) hM1 3)
            h2τ (by positivity) (by positivity)
        _ = _ := by ring
    have hdenpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ' := by positivity
    rw [le_div_iff₀ hdenpos]
    calc Real.exp (-(2 * W)) * (((M + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ τ')
        ≤ Real.exp (-(2 * W)) * Real.exp (3 * M + τ') :=
          mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-(2 * W) + (3 * M + τ')) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-((M : ℝ) + W)) := by
          apply Real.exp_le_exp.mpr
          have := hsmall; push_cast at this; linarith
      _ ≤ _ := hmin
  exact hgap.trans hcert

/-- The separation step: a root `(g, cos 1)` of a nonzero integer polynomial of degree at most
`M` with coefficients below `2^τ'` forces `g ≥ exp(-2 Z^{4M+10})`,
`Z = measureZ (2M) ((M+1) 2^M 2^τ)`, by the hypothesis-free measure for `e^i`. -/
theorem gap_ge_of_cos_one_eliminant {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    {A : MvPolynomial (Fin 2) ℤ} (hA0 : A ≠ 0) {M τ' : ℕ} (hM : 1 ≤ M)
    (hdeg : A.totalDegree ≤ M) (hbits : ∀ m, (A.coeff m).natAbs < 2 ^ τ')
    (hQzero : eval₂ (Int.castRingHom ℝ) ![g, Real.cos 1] A = 0) :
    Real.exp (-(2 * ((ExpITranscendence.measureZ (2 * M) ((M + 1) * 2 ^ M * 2 ^ τ') : ℝ) ^
      (4 * M + 10)))) ≤ g := by
  set Hn : ℕ := (M + 1) * 2 ^ M * 2 ^ τ' with hHndef
  set Zn := ExpITranscendence.measureZ (2 * M) Hn with hZndef
  set W : ℝ := (Zn : ℝ) ^ (4 * M + 10) with hWdef
  have hseparation : ∀ S : Polynomial ℤ, 0 < S.natDegree → S.natDegree ≤ 2 * M →
      (∀ i, |(S.coeff i : ℝ)| ≤ (M + 1 : ℕ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ') →
      Real.exp (-W) ≤ ‖S.eval₂ (Int.castRingHom ℂ) (Complex.exp (((1 : ℝ) : ℂ) * Complex.I))‖ := by
    intro S hS hSdeg hScoeff
    refine exp_neg_le_norm_eval_exp_I hM S hS hSdeg fun i => ?_
    have h := hScoeff i
    have hcast : ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ M * (2 : ℝ) ^ τ' = ((Hn : ℤ) : ℝ) := by
      simp [Hn]
    rw [hcast, ← Int.cast_abs] at h
    exact_mod_cast h
  have hZn1 : (1 : ℝ) ≤ Zn := by
    have : 1 ≤ Zn := Nat.one_le_iff_ne_zero.mpr (by rw [hZndef, ExpITranscendence.measureZ]; positivity)
    exact_mod_cast this
  have hsmall : (4 * M + τ' : ℕ) ≤ (W : ℝ) := by
    have h1 : 4 * M + τ' ≤ Hn := by
      have h2M : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
      have h2τ : τ' + 1 ≤ 2 ^ τ' := Nat.lt_two_pow_self
      have ha : 4 * M ≤ (M + 1) * 2 ^ M := by nlinarith
      rw [hHndef]
      nlinarith
    have h2 : Hn ≤ Zn := by
      rw [hZndef, ExpITranscendence.measureZ]
      calc Hn ≤ (Hn + 1) ^ 2 := by nlinarith
        _ ≤ 6 * (2 * M + 1) ^ 2 * (Hn + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    have h3 : (Zn : ℝ) ≤ W := by
      rw [hWdef]
      calc (Zn : ℝ) = (Zn : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hZn1 (by omega)
    exact le_trans (by exact_mod_cast h1.trans h2) h3
  exact gap_ge_of_separation hg0 hg1 hA0 hdeg hbits hQzero hsmall hseparation

theorem pow_2718_le_exp (n : ℕ) : (2.718 : ℝ) ^ n ≤ Real.exp n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n

/-- `2 Z^{4L+10} ≤ exp(2129 K L⁴)` for `Z = measureZ (2L) ((L+1) 2^L 2^τ)` and
`τ ≤ 70 K L³`. -/
theorem two_mul_measureZ_pow_le {K L τ' : ℕ} (hK : 1 ≤ K) (hL1 : 1 ≤ L)
    (hτr : (τ' : ℝ) ≤ 70 * K * (L : ℝ) ^ 3) :
    2 * (ExpITranscendence.measureZ (2 * L) ((L + 1) * 2 ^ L * 2 ^ τ') : ℝ) ^ (4 * L + 10) ≤
      Real.exp (2129 * K * (L : ℝ) ^ 4) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hHnexp : (((L + 1) * 2 ^ L * 2 ^ τ' : ℕ) : ℝ) ≤ Real.exp (2 * L + τ') := by
    push_cast
    rw [show (2 : ℝ) * L + τ' = L + L + τ' by ring, Real.exp_add, Real.exp_add]
    have h1 := natCast_succ_le_exp L
    push_cast at h1
    exact mul_le_mul (mul_le_mul h1 (two_pow_nat_le_exp L) (by positivity) (by positivity))
      (two_pow_nat_le_exp τ') (by positivity) (by positivity)
  have hZ : (ExpITranscendence.measureZ (2 * L) ((L + 1) * 2 ^ L * 2 ^ τ') : ℝ) ≤
      Real.exp (4 + 8 * L + 2 * τ') := by
    generalize hHn : (L + 1) * 2 ^ L * 2 ^ τ' = Hn at hHnexp ⊢
    have hHn1 : 1 ≤ Hn := by rw [← hHn]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hZle : ExpITranscendence.measureZ (2 * L) Hn ≤ 24 * (2 * L + 1) ^ 2 * Hn ^ 2 := by
      rw [ExpITranscendence.measureZ]
      have : (Hn + 1) ^ 2 ≤ 4 * Hn ^ 2 := by nlinarith
      calc 6 * (2 * L + 1) ^ 2 * (Hn + 1) ^ 2 ≤ 6 * (2 * L + 1) ^ 2 * (4 * Hn ^ 2) :=
            Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have h24 : (24 : ℝ) ≤ Real.exp 4 := by
      have := pow_2718_le_exp 4; norm_num at this ⊢; linarith
    have h2L : ((2 * L + 1 : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
      have := Real.add_one_le_exp (2 * (L : ℝ)); push_cast; linarith
    calc (ExpITranscendence.measureZ (2 * L) Hn : ℝ)
        ≤ ((24 * (2 * L + 1) ^ 2 * Hn ^ 2 : ℕ) : ℝ) := by exact_mod_cast hZle
      _ = 24 * ((2 * L + 1 : ℕ) : ℝ) ^ 2 * (Hn : ℝ) ^ 2 := by push_cast; ring
      _ ≤ Real.exp 4 * Real.exp (2 * L) ^ 2 * Real.exp (2 * L + τ') ^ 2 := by gcongr
      _ = Real.exp (4 + 8 * L + 2 * τ') := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
          push_cast; ring_nf
  have hKL3 : (1 : ℝ) ≤ K * (L : ℝ) ^ 3 := one_le_mul_of_one_le_of_one_le hKr (one_le_pow₀ hLr)
  have hLKL : (L : ℝ) ≤ K * (L : ℝ) ^ 3 := by
    calc (L : ℝ) = 1 * L := by ring
      _ ≤ K * (L : ℝ) ^ 2 * L :=
          mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hKr (one_le_pow₀ hLr))
            (by linarith)
      _ = K * (L : ℝ) ^ 3 := by ring
  have hB : 4 + 8 * (L : ℝ) + 2 * τ' ≤ 152 * (K * (L : ℝ) ^ 3) := by nlinarith
  have hW : (ExpITranscendence.measureZ (2 * L) ((L + 1) * 2 ^ L * 2 ^ τ') : ℝ) ^ (4 * L + 10) ≤
      Real.exp (2128 * K * (L : ℝ) ^ 4) := by
    calc _ ≤ Real.exp (4 + 8 * L + 2 * τ') ^ (4 * L + 10) := pow_le_pow_left₀ (by positivity) hZ _
      _ = Real.exp ((4 * L + 10 : ℕ) * (4 + 8 * L + 2 * τ')) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2128 * K * (L : ℝ) ^ 4) := by
          apply Real.exp_le_exp.mpr
          push_cast
          calc (4 * (L : ℝ) + 10) * (4 + 8 * L + 2 * τ') ≤ (14 * L) * (152 * (K * (L : ℝ) ^ 3)) :=
                mul_le_mul (by linarith) hB (by positivity) (by positivity)
            _ = 2128 * K * (L : ℝ) ^ 4 := by ring
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hKL : (1 : ℝ) ≤ K * (L : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le hKr (one_le_pow₀ hLr)
  calc 2 * (ExpITranscendence.measureZ (2 * L) ((L + 1) * 2 ^ L * 2 ^ τ') : ℝ) ^ (4 * L + 10)
      ≤ Real.exp 1 * Real.exp (2128 * K * (L : ℝ) ^ 4) :=
        mul_le_mul h2e hW (by positivity) (Real.exp_pos _).le
    _ = Real.exp (1 + 2128 * K * (L : ℝ) ^ 4) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- `2129 K L⁴ ≤ exp(exp(171 K²))` for `L ≤ exp(9 K 2^N)`, `2^N ≤ exp(2 + 164 K²)`. -/
theorem tower_arith {K : ℕ} (hK : 1 ≤ K) {L T : ℝ} (hL0 : 0 ≤ L) (hT1 : 1 ≤ T)
    (hL : L ≤ Real.exp (T * (9 * K))) (hT : T ≤ Real.exp (2 + 164 * (K : ℝ) ^ 2)) :
    2129 * K * L ^ 4 ≤ Real.exp (Real.exp (171 * (K : ℝ) ^ 2)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h2129 : (2129 : ℝ) ≤ Real.exp 8 := by
    have := pow_2718_le_exp 8; norm_num at this ⊢; linarith
  have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have h45 : (45 : ℝ) ≤ Real.exp 4 := by
    have := pow_2718_le_exp 4; norm_num at this ⊢; linarith
  have step1 : 2129 * K * L ^ 4 ≤ Real.exp (45 * K * T) := by
    calc 2129 * K * L ^ 4 ≤ Real.exp 8 * Real.exp K * Real.exp (T * (9 * K)) ^ 4 := by gcongr
      _ = Real.exp (8 + K + 36 * K * T) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (45 * K * T) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul hKr hT1 zero_le_one (by linarith : (0 : ℝ) ≤ K)]
  have step2 : 45 * K * T ≤ Real.exp (171 * (K : ℝ) ^ 2) := by
    calc 45 * (K : ℝ) * T ≤ Real.exp 4 * Real.exp K * Real.exp (2 + 164 * (K : ℝ) ^ 2) := by
          gcongr
      _ = Real.exp (6 + K + 164 * (K : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (171 * (K : ℝ) ^ 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith
  exact step1.trans (Real.exp_le_exp.mpr step2)

/-- **Theorem E for `C₁` without external inputs.** For every footprint `K ≥ 1`,
`exp(-exp(exp(exp(171 K²)))) ≤ g_K(1)`. -/
theorem controlledPhase_one_lower_bound_free {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-Real.exp (Real.exp (Real.exp (171 * (K : ℝ) ^ 2)))) ≤
      controlledPhaseLeastDeficit K 1 := by
  obtain ⟨α, hα0, hαzero, hαdeg, hαcoeff⟩ := exists_controlledPhase_one_eliminant hK
  generalize hN : 2 + 164 * K ^ 2 = N at hαdeg hαcoeff
  generalize hL : (5 * (167 * K ^ 2)) ^ (2 ^ N) = L at hαdeg hαcoeff
  have hL1 : 1 ≤ L := by rw [← hL]; exact Nat.one_le_pow _ _ (by positivity)
  have hbits : ∀ m, (α.coeff m).natAbs < 2 ^ ((55 + 14 * K) * L ^ 3 + 1) := by
    intro m
    have hK2 : K ≤ 2 ^ K := (Nat.lt_two_pow_self).le
    have hbase : 2 ^ 55 * K ^ 14 ≤ 2 ^ (55 + 14 * K) := by
      rw [pow_add, show 14 * K = K * 14 by ring, pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK2 14)
    calc (α.coeff m).natAbs ≤ (2 ^ 55 * K ^ 14) ^ (L ^ 3) := hαcoeff m
      _ ≤ (2 ^ (55 + 14 * K)) ^ (L ^ 3) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((55 + 14 * K) * L ^ 3) := (pow_mul _ _ _).symm
      _ < 2 ^ ((55 + 14 * K) * L ^ 3 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hg0 : 0 < controlledPhaseLeastDeficit K 1 :=
    controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hg1 : controlledPhaseLeastDeficit K 1 ≤ 1 := (controlledPhaseLeastDeficit_mem_Icc hK 1).2
  have hgap := gap_ge_of_cos_one_eliminant hg0 hg1 hα0 hL1 hαdeg hbits hαzero
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hτr : (((55 + 14 * K) * L ^ 3 + 1 : ℕ) : ℝ) ≤ 70 * K * (L : ℝ) ^ 3 := by
    push_cast
    have hL3 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hLr
    nlinarith [mul_le_mul hKr hL3 zero_le_one (by linarith : (0 : ℝ) ≤ K)]
  refine (two_mul_measureZ_pow_le hK hL1 hτr).trans (Real.exp_le_exp.mpr ?_)
  have hbase : ((5 * (167 * K ^ 2) : ℕ) : ℝ) ≤ Real.exp (9 * K) := by
    have h835 : (835 : ℝ) ≤ Real.exp 7 := by
      have := pow_2718_le_exp 7; norm_num at this ⊢; linarith
    have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    calc ((5 * (167 * K ^ 2) : ℕ) : ℝ) = 835 * (K : ℝ) ^ 2 := by push_cast; ring
      _ ≤ Real.exp 7 * Real.exp K ^ 2 := by gcongr
      _ = Real.exp (7 + 2 * K) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  have hLexp : (L : ℝ) ≤ Real.exp (((2 ^ N : ℕ) : ℝ) * (9 * K)) := by
    rw [← hL, Real.exp_nat_mul]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _
  have h2N : ((2 ^ N : ℕ) : ℝ) ≤ Real.exp (2 + 164 * (K : ℝ) ^ 2) := by
    have := two_pow_nat_le_exp N
    rw [← hN] at this ⊢
    push_cast at this ⊢
    exact this
  exact tower_arith hK (by positivity) (by exact_mod_cast Nat.one_le_two_pow) hLexp h2N

/-- **Theorem E for `C₁` without external inputs, protocol form.** Every pure or common-map
mixed protocol of footprint `K ≥ 1` implementing `C₁` with score deficit at most `ε` has
`ε ≥ exp(-exp(exp(exp(171 K²))))`; with free standard-Borel classical messages and quantum
footprint `Kq ≥ 1`, `ε ≥ exp(-exp(exp(exp(43776 Kq¹⁰))))`. -/
theorem controlledPhase_one_protocol_bound_free :
    (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
        Real.exp (-Real.exp (Real.exp (Real.exp (171 * (K : ℝ) ^ 2)))) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (Real.exp (Real.exp (43776 * (Kq : ℝ) ^ 10)))) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (Real.exp (Real.exp (43776 * (Kq : ℝ) ^ 10)))) ≤ ε))) := by
  refine ⟨fun P K ε hK hP hs => (controlledPhase_one_lower_bound_free hK).trans
    (P.controlledPhaseLeastDeficit_le hK hP hs), fun P Kq ε hKq => ?_⟩
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hexp : Real.exp (-Real.exp (Real.exp (Real.exp (43776 * (Kq : ℝ) ^ 10)))) =
      Real.exp (-Real.exp (Real.exp (Real.exp (171 * ((16 * Kq ^ 5 : ℕ) : ℝ) ^ 2)))) := by
    push_cast; ring_nf
  obtain ⟨hpure, hmixed⟩ :=
    NLQCLean.StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le P (θ := 1) (ε := ε) hKq
  exact ⟨fun hK hs => hexp ▸ (controlledPhase_one_lower_bound_free h64).trans (hpure hK hs),
    fun n m hK hs => hexp ▸ (controlledPhase_one_lower_bound_free h64).trans (hmixed n m hK hs)⟩

/-- **Theorem E for `C₁` without external inputs, iterated-logarithm form.** For
`0 < ε < exp(-exp(e))`, a charged footprint `K ≥ 1` with least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln ln ln(1/ε) - ½ log₂ 171`. -/
theorem controlledPhase_one_quadruple_log_bound_free (K : ℕ) (ε : ℝ) (hK : 1 ≤ K) (hε : 0 < ε)
    (hεe : ε < Real.exp (-Real.exp (Real.exp 1))) (hle : controlledPhaseLeastDeficit K 1 ≤ ε) :
    (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (Real.log (Real.log (1 / ε))))) -
      (1 / 2 : ℝ) * Real.logb 2 171 ≤ Real.logb 2 K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := (controlledPhase_one_lower_bound_free hK).trans hle
  have hL1 : Real.exp (Real.exp 1) < Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-Real.exp (Real.exp 1))) := Real.log_lt_log hε hεe
      _ = -Real.exp (Real.exp 1) := Real.log_exp _
  have hL0 : 0 < Real.log (1 / ε) := lt_trans (Real.exp_pos _) hL1
  have hlog : Real.log (1 / ε) ≤ Real.exp (Real.exp (Real.exp (171 * (K : ℝ) ^ 2))) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hll1 : Real.exp 1 < Real.log (Real.log (1 / ε)) := by
    have := Real.log_lt_log (Real.exp_pos _) hL1
    rwa [Real.log_exp] at this
  have hll0 : 0 < Real.log (Real.log (1 / ε)) := lt_trans (Real.exp_pos _) hll1
  have hloglog : Real.log (Real.log (1 / ε)) ≤ Real.exp (Real.exp (171 * (K : ℝ) ^ 2)) := by
    have := Real.log_le_log hL0 hlog
    rwa [Real.log_exp] at this
  have hlll1 : 1 < Real.log (Real.log (Real.log (1 / ε))) := by
    have := Real.log_lt_log (Real.exp_pos _) hll1
    rwa [Real.log_exp] at this
  have hlll : Real.log (Real.log (Real.log (1 / ε))) ≤ Real.exp (171 * (K : ℝ) ^ 2) := by
    have := Real.log_le_log hll0 hloglog
    rwa [Real.log_exp] at this
  have hllll : Real.log (Real.log (Real.log (Real.log (1 / ε)))) ≤ 171 * (K : ℝ) ^ 2 := by
    have := Real.log_le_log (by linarith) hlll
    rwa [Real.log_exp] at this
  have hllll0 : 0 < Real.log (Real.log (Real.log (Real.log (1 / ε)))) := Real.log_pos hlll1
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hllll0 hllll
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at hb
  push_cast at hb
  linarith

end NLQCLean
