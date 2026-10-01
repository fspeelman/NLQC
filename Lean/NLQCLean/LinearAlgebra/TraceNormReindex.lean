import NLQCLean.LinearAlgebra.TraceDistance

/-!
# Trace norm under finite basis relabeling

Isometric inclusion and arbitrary row/column basis equivalences
preserve the trace norm. These identify arbitrary finite ancilla types
with the canonical finite dimensions used in the diamond supremum.
-/

namespace NLQCLean

open Matrix

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- An isometry preserves the nuclear norm under left multiplication. -/
theorem IsIsometry.traceNorm_mul_eq {J : Matrix p m ℂ} (hJ : IsIsometry J)
    (A : Matrix m n ℂ) : traceNorm (J * A) = traceNorm A := by
  apply le_antisymm
  · exact (traceNorm_mul_left_le J A).trans (by
      simpa using mul_le_mul_of_nonneg_right hJ.opNorm_le_one (traceNorm_nonneg A))
  · have h := traceNorm_mul_left_le Jᴴ (J * A)
    rw [← Matrix.mul_assoc, hJ.conjTranspose_mul_self, Matrix.one_mul, opNorm_conjTranspose] at h
    exact h.trans (by
      simpa using mul_le_mul_of_nonneg_right hJ.opNorm_le_one (traceNorm_nonneg (J * A)))

/-- The adjoint of an isometry preserves the nuclear norm on the right. -/
theorem IsIsometry.traceNorm_mul_adjoint_eq {J : Matrix p n ℂ} (hJ : IsIsometry J)
    (A : Matrix m n ℂ) : traceNorm (A * Jᴴ) = traceNorm A := by
  rw [← traceNorm_conjTranspose (A * Jᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ.traceNorm_mul_eq, traceNorm_conjTranspose]

omit [DecidableEq p] in
private theorem isIsometry_one_submatrix_equiv (e : p ≃ m) :
    IsIsometry ((1 : Matrix m m ℂ).submatrix e (Equiv.refl m)) := by
  unfold IsIsometry
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_one_equiv]

/-- Relabeling either matrix index by any finite equivalence preserves trace norm. -/
theorem traceNorm_submatrix_equiv (A : Matrix m n ℂ) (r : p ≃ m) (c : q ≃ n) :
    traceNorm (A.submatrix r c) = traceNorm A := by
  let J := (1 : Matrix m m ℂ).submatrix r (Equiv.refl m)
  let K := (1 : Matrix n n ℂ).submatrix c (Equiv.refl n)
  have he : J * A * Kᴴ = A.submatrix r c := by
    dsimp only [J, K]
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      Matrix.one_submatrix_mul r (Equiv.refl m), Matrix.mul_submatrix_one (Equiv.refl n) c]
    rfl
  rw [← he, (isIsometry_one_submatrix_equiv c).traceNorm_mul_adjoint_eq,
    (isIsometry_one_submatrix_equiv r).traceNorm_mul_eq]

end NLQCLean
