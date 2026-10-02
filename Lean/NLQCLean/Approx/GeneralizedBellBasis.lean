import NLQCLean.Approx.PVMSpectralFootprintFloors
import NLQCLean.Models.ForwardReindex
import NLQCLean.Models.PVMUniversalReachability
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A complete generalized Bell basis in every positive finite dimension

The standard character of `ZMod d` supplies the phase, and the second
coordinate records a cyclic shift. The column Gram matrix proves completeness;
each column's laboratory Gram matrix is flat with weight `1 / d`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix
open scoped Matrix.Norms.Frobenius

/-- The standard cyclic character has unit norm. -/
theorem norm_stdAddChar {d : ℕ} [NeZero d] (x : ZMod d) :
    ‖ZMod.stdAddChar x‖ = 1 := Circle.norm_coe (ZMod.toCircle x)

/-- Complex conjugation reverses the cyclic character. -/
theorem star_stdAddChar {d : ℕ} [NeZero d] (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change star (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

/-- Bell columns `(p,s)` have phase `χ(x*p)` on the cyclic diagonal `y=x+s`. -/
noncomputable def generalizedBellMatrix (d : ℕ) [NeZero d] :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ := fun xy ps ↦
  if xy.2 = xy.1 + ps.2 then
    ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * ZMod.stdAddChar (xy.1 * ps.1)
  else 0

private theorem bell_normalization_sq (d : ℕ) [NeZero d] :
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) ^ 2 = (d : ℂ)⁻¹ := by
  rw [inv_pow]
  congr 1
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)

private theorem bell_phase_inner {d : ℕ} [NeZero d] (x p q : ZMod d) :
    star ((((Real.sqrt (d : ℝ))⁻¹ : ℂ)) * ZMod.stdAddChar (x * p)) *
        ((((Real.sqrt (d : ℝ))⁻¹ : ℂ)) * ZMod.stdAddChar (x * q)) =
      (d : ℂ)⁻¹ * ZMod.stdAddChar (x * (q - p)) := by
  rw [star_mul, star_stdAddChar]
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [show - (x * p) = x * (-p) by ring]
  rw [show x * (q - p) = x * (-p) + x * q by ring,
    AddChar.map_add_eq_mul]
  have h := bell_normalization_sq d
  rw [pow_two] at h
  calc
    _ = ((((Real.sqrt (d : ℝ))⁻¹ : ℂ)) * (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
        (ZMod.stdAddChar (x * (-p)) * ZMod.stdAddChar (x * q)) := by ring
    _ = _ := by rw [h]

/-- Orthogonality and normalization of all `d²` generalized Bell columns. -/
theorem isIsometry_generalizedBellMatrix (d : ℕ) [NeZero d] :
    IsIsometry (generalizedBellMatrix d) := by
  classical
  rw [IsIsometry]
  ext ⟨p, s⟩ ⟨q, t⟩
  change (∑ xy : ZMod d × ZMod d, star (generalizedBellMatrix d xy (p, s)) *
    generalizedBellMatrix d xy (q, t)) = if (p, s) = (q, t) then 1 else 0
  rw [Fintype.sum_prod_type]
  by_cases hst : s = t
  · subst t
    have hrow (x : ZMod d) :
        (∑ y : ZMod d, star (generalizedBellMatrix d (x, y) (p, s)) *
          generalizedBellMatrix d (x, y) (q, s)) =
        (d : ℂ)⁻¹ * ZMod.stdAddChar (x * (q - p)) := by
      rw [Finset.sum_eq_single (x + s)]
      · simpa only [generalizedBellMatrix, ite_eq_left rfl, ite_true] using bell_phase_inner x p q
      · intro y _ hy
        simp only [generalizedBellMatrix, ite_eq_right hy, star_zero, zero_mul]
      · simp
    simp_rw [hrow]
    rw [← Finset.mul_sum, AddChar.sum_mulShift (q - p) (ZMod.isPrimitive_stdAddChar d)]
    by_cases hpq : p = q
    · subst q
      simp [NeZero.ne (d : ℂ)]
    · have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
      simp [hpq, hqp]
  · have hrow (x : ZMod d) :
        (∑ y : ZMod d, star (generalizedBellMatrix d (x, y) (p, s)) *
          generalizedBellMatrix d (x, y) (q, t)) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      by_cases hs : y = x + s
      · have ht : y ≠ x + t := by
          intro ht
          exact hst (add_left_cancel (hs.symm.trans ht))
        simp only [generalizedBellMatrix, ite_eq_left hs, ite_eq_right ht, mul_zero]
      · simp only [generalizedBellMatrix, ite_eq_right hs, star_zero, zero_mul]
    have hpair : (p, s) ≠ (q, t) := fun h ↦ hst (congrArg Prod.snd h)
    rw [ite_eq_right hpair]
    simp_rw [hrow]
    exact Finset.sum_const_zero

/-- Every conjugate Bell column has exactly flat laboratory Gram matrix. -/
theorem pvmConjugateColumnMatrix_generalizedBellMatrix_gram (d : ℕ) [NeZero d]
    (i : ZMod d × ZMod d) :
    pvmConjugateColumnMatrix (generalizedBellMatrix d) i *
        (pvmConjugateColumnMatrix (generalizedBellMatrix d) i)ᴴ =
      Matrix.diagonal (fun _ : ZMod d ↦ ((Fintype.card (ZMod d) : ℝ)⁻¹ : ℂ)) := by
  classical
  ext x z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pvmConjugateColumnMatrix,
    Matrix.of_apply, star_star, Matrix.diagonal_apply]
  by_cases hxz : x = z
  · subst z
    have hterm : (∑ y : ZMod d, star (generalizedBellMatrix d (x, y) i) *
        generalizedBellMatrix d (x, y) i) = (d : ℂ)⁻¹ := by
      rw [Finset.sum_eq_single (x + i.2)]
      · simpa only [generalizedBellMatrix, ite_eq_left rfl, ite_true, sub_self, mul_zero,
          AddChar.map_zero_eq_one, mul_one] using bell_phase_inner x i.1 i.1
      · intro y _ hy
        simp only [generalizedBellMatrix, ite_eq_right hy, star_zero, zero_mul]
      · simp
    simpa using hterm
  · have hterm (y : ZMod d) : star (generalizedBellMatrix d (x, y) i) *
        generalizedBellMatrix d (z, y) i = 0 := by
      by_cases hx : y = x + i.2
      · have hz : y ≠ z + i.2 := by
          intro hz
          exact hxz (add_right_cancel (hx.symm.trans hz))
        simp only [generalizedBellMatrix, ite_eq_left hx, ite_eq_right hz, mul_zero]
      · simp only [generalizedBellMatrix, ite_eq_right hx, star_zero, zero_mul]
    rw [ite_eq_right hxz]
    simp_rw [hterm]
    exact Finset.sum_const_zero

/-- The same concrete generalized Bell basis on the standard `Fin d` registers. -/
noncomputable def generalizedBellFinMatrix (d : ℕ) [NeZero d] :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (generalizedBellMatrix d).submatrix
    (Equiv.prodCongr (ZMod.finEquiv d).toEquiv (ZMod.finEquiv d).toEquiv)
    (Equiv.prodCongr (ZMod.finEquiv d).toEquiv (ZMod.finEquiv d).toEquiv)

/-- All `d²` finite-register Bell columns are orthonormal. -/
theorem isIsometry_generalizedBellFinMatrix (d : ℕ) [NeZero d] :
    IsIsometry (generalizedBellFinMatrix d) :=
  (isIsometry_generalizedBellMatrix d).submatrix_equiv _ _

/-- Relabeling preserves the maximally entangled Bell column Gram identities. -/
theorem pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram (d : ℕ) [NeZero d]
    (i : Fin d × Fin d) :
    pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i *
        (pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i)ᴴ =
      Matrix.diagonal (fun _ : Fin d ↦ ((Fintype.card (Fin d) : ℝ)⁻¹ : ℂ)) := by
  let e := (ZMod.finEquiv d).toEquiv
  have hcolumn : pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i =
      (pvmConjugateColumnMatrix (generalizedBellMatrix d) (e i.1, e i.2)).submatrix e e := rfl
  rw [hcolumn, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    pvmConjugateColumnMatrix_generalizedBellMatrix_gram]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, ite_eq_left, Fintype.card_fin,
      ZMod.card]
  · have hexy : e x ≠ e y := fun h ↦ hxy (e.injective h)
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, ite_eq_right hxy, ite_eq_right hexy]

section Protocol

variable {d : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- The concrete Bell target forces `d³ (1-ε)²` in the charged pure model. -/
theorem PureProtocol.generalizedBellPVM_footprint_floor
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) P.operationalChannel) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K := by
  have h := P.maximallyEntangledPVM_footprint_floor (generalizedBellFinMatrix d)
    (isIsometry_generalizedBellFinMatrix d)
    (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d) hK hε hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_succ, pow_two,
    pow_one, pow_zero, one_mul, mul_one, mul_assoc] using h

/-- The Bell-target cubic floor for finite mixed resources with common maps. -/
theorem MixedResource.generalizedBellPVM_footprint_floor {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (m.mixedChannel VA VB DA DB)) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K := by
  have h := m.maximallyEntangledPVM_footprint_floor VA VB DA DB hVA hVB hDA hDB
    (generalizedBellFinMatrix d) (isIsometry_generalizedBellFinMatrix d)
    (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d) hR hK hε hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_succ, pow_two,
    pow_one, pow_zero, one_mul, mul_one, mul_assoc] using h

end Protocol

/-- A concrete Bell basis lift, with both unitary identities proved. -/
noncomputable def generalizedBellUnitary (d : ℕ) [NeZero d] :
    Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
  ⟨generalizedBellFinMatrix d, Matrix.mem_unitaryGroup_iff'.mpr
    (isIsometry_generalizedBellFinMatrix d)⟩

/-- Universal score approximation must approximate the concrete Bell basis. -/
theorem PurePVMUniversalScore.cubic_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε : 0 ≤ ε ∧ ε ≤ 1) (h : PurePVMUniversalScore d K ε) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K := by
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨s, P, hP, hscore⟩ := h (generalizedBellUnitary d)
  exact P.generalizedBellPVM_footprint_floor hP hε hscore

/-- Universal finite-mixed approximation has the same concrete cubic floor. -/
theorem MixedPVMUniversalScore.cubic_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε : 0 ≤ ε ∧ ε ≤ 1) (h : MixedPVMUniversalScore d K ε) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K :=
  ((mixedPVMUniversalScore_iff_pure d K ε).mp h).cubic_floor hd hε

/-- At deficit at most one half, the unconditional universal floor is `d³/4`. -/
theorem PurePVMUniversalScore.cubic_quarter_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : PurePVMUniversalScore d K ε) : (d : ℝ) ^ 3 / 4 ≤ K := by
  have hf := h.cubic_floor hd ⟨hε0, by linarith⟩
  have hsquare : (1 / 4 : ℝ) ≤ (1 - ε) ^ 2 := by nlinarith [sq_nonneg (ε - 1 / 2)]
  have hmult := mul_le_mul_of_nonneg_left hsquare (pow_nonneg (Nat.cast_nonneg d) 3)
  nlinarith

/-- The `d³/4` universal floor also holds with a finite mixed resource. -/
theorem MixedPVMUniversalScore.cubic_quarter_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : MixedPVMUniversalScore d K ε) : (d : ℝ) ^ 3 / 4 ≤ K :=
  ((mixedPVMUniversalScore_iff_pure d K ε).mp h).cubic_quarter_floor hd hε0 hε

/-- For `d=2ⁿ`, the cubic floor contributes the unconditional term `3n-2`. -/
theorem PurePVMUniversalScore.cubic_qubit_floor {n K : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : PurePVMUniversalScore (2 ^ n) K ε) :
    3 * (n : ℝ) - 2 ≤ Real.logb 2 (K : ℝ) := by
  have hf := h.cubic_quarter_floor (pow_pos (by norm_num) n) hε0 hε
  have hpos : 0 < (((2 ^ n : ℕ) : ℝ) ^ 3 / 4) := by positivity
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hf
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow, h4] at hlog
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact hlog

/-- The universal cubic qubit term for finite mixed resources. -/
theorem MixedPVMUniversalScore.cubic_qubit_floor {n K : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : MixedPVMUniversalScore (2 ^ n) K ε) :
    3 * (n : ℝ) - 2 ≤ Real.logb 2 (K : ℝ) :=
  ((mixedPVMUniversalScore_iff_pure (2 ^ n) K ε).mp h).cubic_qubit_floor hε0 hε

/-- Joint-TV universality transfers to the concrete cubic score floor. -/
theorem PurePVMUniversalTV.cubic_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (h : PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K := (h.score hd).cubic_floor hd hε

/-- Finite-mixed joint-TV universality has the same cubic floor. -/
theorem MixedPVMUniversalTV.cubic_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (h : MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε) :
    (d : ℝ) ^ 3 * (1 - ε) ^ 2 ≤ K := (h.score hd).cubic_floor hd hε

/-- The cubic quarter floor for arbitrary-register joint-TV universality. -/
theorem PurePVMUniversalTV.cubic_quarter_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε) :
    (d : ℝ) ^ 3 / 4 ≤ K := (h.score hd).cubic_quarter_floor hd hε0 hε

/-- The cubic quarter floor for finite-mixed joint-TV universality. -/
theorem MixedPVMUniversalTV.cubic_quarter_floor {d K : ℕ} {ε : ℝ}
    (hd : 0 < d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε) :
    (d : ℝ) ^ 3 / 4 ≤ K := (h.score hd).cubic_quarter_floor hd hε0 hε

/-- The unconditional cubic qubit term for arbitrary-register TV protocols. -/
theorem PurePVMUniversalTV.cubic_qubit_floor {n K : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K ε) :
    3 * (n : ℝ) - 2 ≤ Real.logb 2 (K : ℝ) :=
  (h.score (pow_pos (by norm_num) n)).cubic_qubit_floor hε0 hε

/-- The unconditional cubic qubit term for finite-mixed TV protocols. -/
theorem MixedPVMUniversalTV.cubic_qubit_floor {n K : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K ε) :
    3 * (n : ℝ) - 2 ≤ Real.logb 2 (K : ℝ) :=
  (h.score (pow_pos (by norm_num) n)).cubic_qubit_floor hε0 hε

end NLQCLean
