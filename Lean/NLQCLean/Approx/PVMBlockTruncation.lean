import NLQCLean.LinearAlgebra.SchmidtOverlap

/-!
# Normalizing individual PVM environment blocks

For per-block normalization, a chosen finite set of rows in
Schmidt coordinates gives the usual normalized truncation when its retained
mass is positive.  When that mass vanishes, a phase-adjusted matrix unit gives
a unit rank-one fallback with nonnegative real overlap.  Thus every block can
be normalized while charging at most one additional Schmidt term.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius ComplexConjugate

/-- A matrix unit whose phase is aligned with one coefficient of `A` is a
unit rank-one matrix with nonnegative real Frobenius overlap.  This also covers
the case in which the chosen coefficient vanishes. -/
theorem exists_unit_rank_one_nonnegative_frobInner {m n : Type*}
    [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (A : Matrix m n ℂ) :
    ∃ U : Matrix m n ℂ, ‖U‖ = 1 ∧ U.rank ≤ 1 ∧
      frobInner U A = ((frobInner U A).re : ℂ) ∧ 0 ≤ (frobInner U A).re := by
  classical
  let i : m := Classical.choice inferInstance
  let j : n := Classical.choice inferInstance
  let a : ℂ := A i j
  let c : ℂ := if a = 0 then 1 else a / (‖a‖ : ℂ)
  let U : Matrix m n ℂ := Matrix.single i j c
  have hc_norm : ‖c‖ = 1 := by
    by_cases ha : a = 0
    · simp [c, ha]
    · simp only [c, if_neg ha, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg a)]
      exact div_self (norm_ne_zero_iff.mpr ha)
  have hU_norm : ‖U‖ = 1 := by
    simp [U, Matrix.frobenius_norm_def, Matrix.single_apply, ite_and,
      apply_ite, hc_norm]
  have hU_rank : U.rank ≤ 1 := by
    change (Matrix.single i j c).rank ≤ 1
    have hr := Matrix.rank_le_card_of_support_subset
      (Matrix.single i j c) ({i} : Finset m) (by
        rw [Function.support_subset_iff']
        intro x hx
        have hxi : x ≠ i := by simpa using hx
        funext y
        simp [Matrix.row, Ne.symm hxi])
    simpa using hr
  have hinner : frobInner U A = (‖a‖ : ℂ) := by
    have hsingle : frobInner U A = star c * a := by
      simp [frobInner, U, Matrix.single_apply, ite_and, apply_ite, ite_mul, a]
    rw [hsingle]
    by_cases ha : a = 0
    · simp [a, c, ha]
    · simp only [c, if_neg ha, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, pow_two, Complex.ofReal_mul, mul_div_cancel_left₀]
      exact_mod_cast norm_ne_zero_iff.mpr ha
  refine ⟨U, hU_norm, hU_rank, ?_, ?_⟩
  · rw [hinner]
    simp
  · rw [hinner]
    change 0 ≤ ‖a‖
    exact norm_nonneg a

/-- Normalize the rows selected by `s` in diagonal Gram coordinates.  The
positive retained-mass premise is the only condition needed in this branch. -/
theorem exists_normalized_truncateRows_of_diagonal_gram {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℂ) (w : m → ℝ) (s : Finset m)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ)))
    (hpos : 0 < ∑ i ∈ s, w i) :
    ∃ W : Matrix m n ℂ, ‖W‖ = 1 ∧ W.rank ≤ s.card ∧
      frobInner W M = (Real.sqrt (∑ i ∈ s, w i) : ℂ) := by
  classical
  let u : ℝ := ∑ i ∈ s, w i
  let T := truncateRows s M
  have hT_sq : ‖T‖ ^ 2 = u := norm_sq_truncateRows_of_diagonal_gram s M w hgram
  have hT : ‖T‖ = Real.sqrt u := by
    rw [← hT_sq, Real.sqrt_sq (norm_nonneg _)]
  have hinner : frobInner T M = (u : ℂ) :=
    frobInner_truncateRows_of_diagonal_gram s M w hgram
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hpos
  let W : Matrix m n ℂ := ((Real.sqrt u)⁻¹ : ℂ) • T
  refine ⟨W, ?_, (rank_smul_le _ T).trans (rank_truncateRows_le s M), ?_⟩
  · change ‖((Real.sqrt u)⁻¹ : ℂ) • T‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsqrt.le, hT, inv_mul_cancel₀ hsqrt.ne']
  · change frobInner (((Real.sqrt u)⁻¹ : ℂ) • T) M = _
    rw [frobInner_smul_left, hinner]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have hu_sq : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by
      exact_mod_cast Real.sq_sqrt hpos.le
    rw [← hu_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hsqrt.ne'), one_mul]

/-- Pull a normalized chosen-row truncation back through unitary Schmidt
coordinates.  The rank charge is exactly the number of selected rows. -/
theorem exists_normalized_spectral_support_of_pos {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℂ) (V : Matrix m m ℂ) (s : Finset m)
    (hV : IsIsometry V)
    (hgram : (Vᴴ * A) * (Vᴴ * A)ᴴ =
      Matrix.diagonal (fun i ↦ (schmidtWeights A i : ℂ)))
    (hpos : 0 < ∑ i ∈ s, schmidtWeights A i) :
    ∃ U : Matrix m n ℂ, ‖U‖ = 1 ∧ U.rank ≤ s.card ∧
      frobInner U A = (Real.sqrt (∑ i ∈ s, schmidtWeights A i) : ℂ) := by
  obtain ⟨T, hT, hTrank, hinner⟩ :=
    exists_normalized_truncateRows_of_diagonal_gram
      (Vᴴ * A) (schmidtWeights A) s hgram hpos
  refine ⟨V * T, (hV.frobNorm_mul_eq T).trans hT,
    (Matrix.rank_mul_le_right V T).trans hTrank, ?_⟩
  rw [frobInner_mul_left]
  exact hinner

/-- Normalize an arbitrary chosen Schmidt-row support.  A positive block keeps
the sharp rank bound `s.card`; a zero block uses one phase-aligned product
term.  The final overlap is real, lies between the square root of the retained
mass and one, and the uniform rank bound is `s.card + 1`. -/
theorem exists_normalized_spectral_support {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [Nonempty m] [Nonempty n]
    (A : Matrix m n ℂ) (V : Matrix m m ℂ) (s : Finset m)
    (hA : ‖A‖ ≤ 1) (hV : IsIsometry V)
    (hgram : (Vᴴ * A) * (Vᴴ * A)ᴴ =
      Matrix.diagonal (fun i ↦ (schmidtWeights A i : ℂ))) :
    ∃ U : Matrix m n ℂ, ‖U‖ = 1 ∧ U.rank ≤ s.card + 1 ∧
      frobInner U A = ((frobInner U A).re : ℂ) ∧
      Real.sqrt (∑ i ∈ s, schmidtWeights A i) ≤ (frobInner U A).re ∧
      (frobInner U A).re ≤ 1 := by
  classical
  let q : ℝ := ∑ i ∈ s, schmidtWeights A i
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ ↦ schmidtWeights_nonneg A i
  by_cases hpos : 0 < q
  · obtain ⟨U, hU, hUrank, hinner⟩ :=
      exists_normalized_spectral_support_of_pos A V s hV hgram hpos
    have hroot : Real.sqrt q ≤ 1 := by
      have hi := norm_frobInner_le U A
      rw [hU, one_mul, hinner, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg q)] at hi
      exact hi.trans hA
    refine ⟨U, hU, hUrank.trans (Nat.le_add_right _ _), ?_, ?_, ?_⟩
    · rw [hinner]
      simp
    · rw [hinner]
      exact le_rfl
    · rw [hinner]
      exact hroot
  · have hq0 : q = 0 := le_antisymm (le_of_not_gt hpos) hq
    obtain ⟨U, hU, hUrank, hreal, hnonneg⟩ :=
      exists_unit_rank_one_nonnegative_frobInner A
    have hupper : (frobInner U A).re ≤ 1 := by
      have hi := norm_frobInner_le U A
      rw [hU, one_mul] at hi
      have hre_norm : ‖frobInner U A‖ = (frobInner U A).re := by
        calc
          ‖frobInner U A‖ = ‖((frobInner U A).re : ℂ)‖ := congrArg norm hreal
          _ = (frobInner U A).re := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      rw [hre_norm] at hi
      exact hi.trans hA
    refine ⟨U, hU, hUrank.trans ?_, hreal, ?_, hupper⟩
    · omega
    · rw [show (∑ i ∈ s, schmidtWeights A i) = 0 from hq0,
        Real.sqrt_zero]
      exact hnonneg

end NLQCLean
