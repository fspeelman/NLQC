import NLQCLean.Bounds.ExplicitControlledPhase
import NLQCLean.Arithmetic.EliminationLagrangeSystem
import NLQCLean.Arithmetic.EliminationPhysicalLICQ

/-!
# The resultant eliminant for `C₁`

The least deficit `g = g_K(1)` is a root, together with `cos 1`, of an explicit nonzero
integer polynomial `α(y, c)`. The physical maximizer with Lagrange multipliers (the constraint
gradients are independent) is a real zero of the Lagrange system; at the generic parameter
point the system has no zero (`lagrangeSystem_generic`), so iterated resultants produce `α`,
of degree at most `L = (835 K²)^(2^(2 + 164 K²))` and coefficients at most
`(2⁵⁵ K¹⁴)^(L³)`, all explicit. With the Gelfond measure for `e^i` it gives the bound with
explicit constant `controlledPhase_one_triple_exp_bound`
(`Bounds/ExplicitControlledPhaseGelfond`). The file also proves the gap step
`gap_ge_of_separation` shared by both eliminants. The deformation eliminant
(`Bounds/ControlledPhaseEliminant`) has singly exponential size and gives the stated rate.
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

/-- **Resultant eliminant for `C₁`.** -/
theorem exists_controlledPhase_one_resultant_eliminant {K : ℕ} (hK : 1 ≤ K) :
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

theorem pow_2718_le_exp (n : ℕ) : (2.718 : ℝ) ^ n ≤ Real.exp n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n

end NLQCLean
