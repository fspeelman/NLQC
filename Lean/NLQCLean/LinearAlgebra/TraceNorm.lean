import NLQCLean.LinearAlgebra.SchmidtOverlap
import NLQCLean.LinearAlgebra.TensorOperatorNorm

/-!
# Finite matrix trace norm by operator-norm duality

The dual formula is `sup_{opNorm B ≤ 1} |Tr(B† A)|`.
The supremum is finite by compactness of the finite-dimensional operator
ball. All dimensions are arbitrary finite types, including empty types.
-/

namespace NLQCLean

open Matrix

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

section Operator
open scoped Matrix.Norms.L2Operator

omit [DecidableEq m] in
theorem isCompact_opNorm_ball : IsCompact {B : Matrix m n ℂ | opNorm B ≤ 1} := by
  let : ProperSpace (Matrix m n ℂ) := FiniteDimensional.proper ℂ (Matrix m n ℂ)
  simpa only [Metric.closedBall, dist_zero_right, ← opNorm_eq_l2_opNorm] using
    isCompact_closedBall (0 : Matrix m n ℂ) 1

omit [DecidableEq m] in
theorem opNorm_eq_zero_iff (A : Matrix m n ℂ) : opNorm A = 0 ↔ A = 0 := by
  rw [opNorm_eq_l2_opNorm]
  exact norm_eq_zero

end Operator

open scoped Matrix.Norms.Frobenius

/-- The finite-dimensional trace norm, in its operator-dual definition. -/
noncomputable def traceNorm (A : Matrix m n ℂ) : ℝ :=
  sSup ((fun B : Matrix m n ℂ => ‖frobInner B A‖) '' {B | opNorm B ≤ 1})

omit [DecidableEq m] in
private theorem traceNorm_test_nonempty (A : Matrix m n ℂ) :
    ((fun B : Matrix m n ℂ => ‖frobInner B A‖) '' {B | opNorm B ≤ 1}).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · change ‖toCLM (0 : Matrix m n ℂ)‖ ≤ 1
    simp [toCLM]
  · simp [frobInner]

omit [DecidableEq m] in
private theorem traceNorm_test_bddAbove (A : Matrix m n ℂ) :
    BddAbove ((fun B : Matrix m n ℂ => ‖frobInner B A‖) '' {B | opNorm B ≤ 1}) := by
  apply IsCompact.bddAbove
  apply isCompact_opNorm_ball.image
  apply Continuous.norm
  unfold frobInner
  fun_prop

omit [DecidableEq m] in
theorem norm_frobInner_le_traceNorm (A B : Matrix m n ℂ) (hB : opNorm B ≤ 1) :
    ‖frobInner B A‖ ≤ traceNorm A :=
  le_csSup (traceNorm_test_bddAbove A) ⟨B, hB, rfl⟩

omit [DecidableEq m] in
theorem traceNorm_nonneg (A : Matrix m n ℂ) : 0 ≤ traceNorm A := by
  apply le_csSup (traceNorm_test_bddAbove A)
  refine ⟨0, ?_, ?_⟩
  · change ‖toCLM (0 : Matrix m n ℂ)‖ ≤ 1
    simp [toCLM]
  · simp [frobInner]

omit [DecidableEq m] in
theorem traceNorm_le {A : Matrix m n ℂ} {c : ℝ}
    (h : ∀ B : Matrix m n ℂ, opNorm B ≤ 1 → ‖frobInner B A‖ ≤ c) : traceNorm A ≤ c := by
  apply csSup_le (traceNorm_test_nonempty A)
  rintro _ ⟨B, hB, rfl⟩
  exact h B hB

omit [DecidableEq m] in
@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix m n ℂ) = 0 := by
  apply le_antisymm _ (traceNorm_nonneg _)
  apply traceNorm_le
  intro B hB
  simp [frobInner]

omit [DecidableEq m] in
theorem traceNorm_add_le (A B : Matrix m n ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  apply traceNorm_le
  intro T hT
  calc
    ‖frobInner T (A + B)‖ = ‖frobInner T A + frobInner T B‖ := by
      congr 1
      simp [frobInner, mul_add, Finset.sum_add_distrib]
    _ ≤ ‖frobInner T A‖ + ‖frobInner T B‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_frobInner_le_traceNorm A T hT) (norm_frobInner_le_traceNorm B T hT)

omit [DecidableEq m] in
theorem traceNorm_smul_le (c : ℂ) (A : Matrix m n ℂ) :
    traceNorm (c • A) ≤ ‖c‖ * traceNorm A := by
  apply traceNorm_le
  intro B hB
  rw [frobInner_smul_right, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_frobInner_le_traceNorm A B hB) (norm_nonneg c)

omit [DecidableEq m] in
@[simp] theorem traceNorm_smul (c : ℂ) (A : Matrix m n ℂ) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  by_cases hc : c = 0
  · simp [hc]
  apply le_antisymm (traceNorm_smul_le c A)
  have h := traceNorm_smul_le c⁻¹ (c • A)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
  calc
    ‖c‖ * traceNorm A ≤ ‖c‖ * (‖c‖⁻¹ * traceNorm (c • A)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg c)
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]

omit [DecidableEq m] in
@[simp] theorem traceNorm_neg (A : Matrix m n ℂ) : traceNorm (-A) = traceNorm A := by
  simpa using traceNorm_smul (-1 : ℂ) A

theorem opNorm_single_one_le (i : m) (j : n) : opNorm (Matrix.single i j (1 : ℂ)) ≤ 1 := by
  apply (opNorm_le_frobNorm _).trans
  simp [Matrix.frobenius_norm_def, Matrix.single_apply, ite_and, apply_ite]

/-- Entry tests establish definiteness, without a nonempty dimension premise. -/
theorem norm_entry_le_traceNorm (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ traceNorm A := by
  simpa [frobInner, Matrix.single_apply, ite_and, apply_ite, ite_mul] using
    norm_frobInner_le_traceNorm A (Matrix.single i j 1) (opNorm_single_one_le i j)

@[simp] theorem traceNorm_eq_zero_iff (A : Matrix m n ℂ) : traceNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    apply norm_eq_zero.mp
    exact le_antisymm (h ▸ norm_entry_le_traceNorm A i j) (norm_nonneg _)
  · rintro rfl
    exact traceNorm_zero

omit [DecidableEq m] in
/-- Hölder duality with an arbitrary, unnormalized operator test. -/
theorem norm_frobInner_le_opNorm_mul_traceNorm (A B : Matrix m n ℂ) :
    ‖frobInner B A‖ ≤ opNorm B * traceNorm A := by
  by_cases hB : opNorm B = 0
  · have hz : B = 0 := (opNorm_eq_zero_iff B).mp hB
    simp [hz, frobInner, opNorm, toCLM]
  have hp : 0 < opNorm B := lt_of_le_of_ne (opNorm_nonneg B) (Ne.symm hB)
  have htest : opNorm ((opNorm B)⁻¹ • B) ≤ 1 := by
    rw [opNorm_smul_real, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hB]
  have h := norm_frobInner_le_traceNorm A ((opNorm B)⁻¹ • B) htest
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), frobInner_smul_left, norm_mul,
    norm_star] at h
  rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hp)] at h
  calc
    ‖frobInner B A‖ = opNorm B * ((opNorm B)⁻¹ * ‖frobInner B A‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hB, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp.le

/-- Multiplication on either side costs only the operator norms. -/
theorem traceNorm_mul_mul_le (L : Matrix p m ℂ) (A : Matrix m n ℂ) (R : Matrix n q ℂ) :
    traceNorm (L * A * R) ≤ opNorm L * traceNorm A * opNorm R := by
  apply traceNorm_le
  intro B hB
  have he : frobInner B (L * A * R) = frobInner (Lᴴ * B * Rᴴ) A := by
    simp only [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ L, ← Matrix.mul_assoc (Bᴴ * L) A,
      Matrix.trace_mul_comm ((Bᴴ * L) * A)]
    simp only [Matrix.mul_assoc]
  rw [he]
  have ho : opNorm (Lᴴ * B * Rᴴ) ≤ opNorm L * opNorm R := by
    calc
      _ ≤ (opNorm Lᴴ * opNorm B) * opNorm Rᴴ :=
        (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _))
      _ ≤ _ := by
        rw [opNorm_conjTranspose, opNorm_conjTranspose]
        simpa using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB (opNorm_nonneg L)) (opNorm_nonneg R)
  exact (norm_frobInner_le_opNorm_mul_traceNorm A _).trans (by
    nlinarith [mul_le_mul_of_nonneg_right ho (traceNorm_nonneg A)])

omit [DecidableEq m] in
/-- Finite sums retain the triangle bound used in channel amplification. -/
theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

omit [DecidableEq m] in
theorem traceNorm_sub_le (A B : Matrix m n ℂ) :
    traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le A (-B)

end NLQCLean
