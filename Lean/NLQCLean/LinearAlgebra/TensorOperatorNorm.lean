import NLQCLean.LinearAlgebra.Isometry

/-!
# Operator norms for tensor velocities

Operator norms of tensor products are bounded without a
Frobenius dimension factor. The amplification estimates apply the ordinary
operator-norm inequality independently to each Euclidean vector slice.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

section Elementary

open scoped Matrix.Norms.L2Operator

omit [DecidableEq m] in
theorem opNorm_add_le (A B : Matrix m n 𝕜) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  simpa only [opNorm_eq_l2_opNorm] using norm_add_le A B

omit [DecidableEq m] in
theorem opNorm_smul_real (c : ℝ) (A : Matrix m n 𝕜) : opNorm (c • A) = |c| * opNorm A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  simpa only [opNorm_eq_l2_opNorm, RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul (c : 𝕜) A

omit [DecidableEq m] in
theorem opNorm_adjoint_mul_self (A : Matrix m n 𝕜) : opNorm (Aᴴ * A) = opNorm A ^ 2 := by
  simpa only [opNorm_eq_l2_opNorm, pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self A

end Elementary

theorem opNorm_one_le : opNorm (1 : Matrix n n 𝕜) ≤ 1 := by
  have h : toCLM (1 : Matrix n n 𝕜) = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 n) := by
    ext x i
    simp [toCLM_apply]
  change ‖toCLM (1 : Matrix n n 𝕜)‖ ≤ 1
  rw [h]
  exact ContinuousLinearMap.norm_id_le

omit [DecidableEq m] in
theorem IsIsometry.opNorm_le_one {A : Matrix m n 𝕜} (hA : IsIsometry A) : opNorm A ≤ 1 := by
  have h := opNorm_adjoint_mul_self A
  rw [hA.conjTranspose_mul_self] at h
  have h1 := opNorm_one_le (n := n) (𝕜 := 𝕜)
  have h0 := opNorm_nonneg A
  nlinarith

omit [DecidableEq m] in
theorem opNorm_isometry_mul_le {A : Matrix m n 𝕜} (hA : IsIsometry A) (B : Matrix n p 𝕜) :
    opNorm (A * B) ≤ opNorm B :=
  (opNorm_mul_le A B).trans (by
    simpa using mul_le_mul_of_nonneg_right hA.opNorm_le_one (opNorm_nonneg B))

omit [DecidableEq m] in
theorem opNorm_mul_isometry_le (A : Matrix m n 𝕜) {B : Matrix n p 𝕜} (hB : IsIsometry B) :
    opNorm (A * B) ≤ opNorm A :=
  (opNorm_mul_le A B).trans (by
    simpa using mul_le_mul_of_nonneg_left hB.opNorm_le_one (opNorm_nonneg A))

omit [DecidableEq m] in
/-- A scalar Gram identity bounds the operator norm, including an empty
input space. This will apply to insertion of an arbitrary resource velocity. -/
theorem opNorm_le_of_gram_scalar {A : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (hA : Aᴴ * A = (c ^ 2) • (1 : Matrix n n 𝕜)) : opNorm A ≤ c := by
  have h := opNorm_adjoint_mul_self A
  rw [hA, opNorm_smul_real, abs_of_nonneg (sq_nonneg c)] at h
  have h1 := mul_le_mul_of_nonneg_left (opNorm_one_le (n := n) (𝕜 := 𝕜)) (sq_nonneg c)
  have h0 := opNorm_nonneg A
  nlinarith

omit [DecidableEq m] in
/-- Tensoring an operator with an identity does not increase its norm. -/
theorem opNorm_kronecker_one_le (A : Matrix m n 𝕜) :
    opNorm (A ⊗ₖ (1 : Matrix p p 𝕜)) ≤ opNorm A := by
  change ‖toCLM (A ⊗ₖ (1 : Matrix p p 𝕜))‖ ≤ opNorm A
  refine ContinuousLinearMap.opNorm_le_bound _ (opNorm_nonneg A) fun x => ?_
  let slice (j : p) : EuclideanSpace 𝕜 n := WithLp.toLp 2 (fun u => x (u, j))
  have he (i : m) (j : p) :
      toCLM (A ⊗ₖ (1 : Matrix p p 𝕜)) x (i, j) = toCLM A (slice j) i := by
    simp [toCLM_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, slice]
  have hi : ∑ j, ‖slice j‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, slice]
    exact Finset.sum_comm
  have ho : ‖toCLM (A ⊗ₖ (1 : Matrix p p 𝕜)) x‖ ^ 2 =
      ∑ j, ‖toCLM A (slice j)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, he]
    exact Finset.sum_comm
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNorm_nonneg A) (norm_nonneg x))).mp
  calc
    _ = ∑ j, ‖toCLM A (slice j)‖ ^ 2 := ho
    _ ≤ ∑ j, (opNorm A * ‖slice j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNorm_nonneg A) (norm_nonneg _))).mpr
        (norm_toCLM_le A (slice j))
    _ = (opNorm A * ‖x‖) ^ 2 := by simp_rw [mul_pow, ← Finset.mul_sum, hi]

omit [DecidableEq p] in
/-- The other tensor amplification has the same dimension-free estimate. -/
theorem opNorm_one_kronecker_le (B : Matrix p q 𝕜) :
    opNorm ((1 : Matrix n n 𝕜) ⊗ₖ B) ≤ opNorm B := by
  change ‖toCLM ((1 : Matrix n n 𝕜) ⊗ₖ B)‖ ≤ opNorm B
  refine ContinuousLinearMap.opNorm_le_bound _ (opNorm_nonneg B) fun x => ?_
  let slice (i : n) : EuclideanSpace 𝕜 q := WithLp.toLp 2 (fun v => x (i, v))
  have he (i : n) (j : p) :
      toCLM ((1 : Matrix n n 𝕜) ⊗ₖ B) x (i, j) = toCLM B (slice i) j := by
    simp [toCLM_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, slice]
  have hi : ∑ i, ‖slice i‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, slice]
  have ho : ‖toCLM ((1 : Matrix n n 𝕜) ⊗ₖ B) x‖ ^ 2 =
      ∑ i, ‖toCLM B (slice i)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, he]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNorm_nonneg B) (norm_nonneg x))).mp
  calc
    _ = ∑ i, ‖toCLM B (slice i)‖ ^ 2 := ho
    _ ≤ ∑ i, (opNorm B * ‖slice i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNorm_nonneg B) (norm_nonneg _))).mpr
        (norm_toCLM_le B (slice i))
    _ = (opNorm B * ‖x‖) ^ 2 := by simp_rw [mul_pow, ← Finset.mul_sum, hi]

omit [DecidableEq m] in
theorem opNorm_kronecker_le (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    opNorm (A ⊗ₖ B) ≤ opNorm A * opNorm B := by
  have hprod : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix p p 𝕜)) * ((1 : Matrix n n 𝕜) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hprod]
  exact (opNorm_mul_le _ _).trans
    (mul_le_mul (opNorm_kronecker_one_le A) (opNorm_one_kronecker_le B)
      (opNorm_nonneg _) (opNorm_nonneg A))

end NLQCLean
