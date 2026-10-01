import NLQCLean.LinearAlgebra.Isometry

/-!
# The SWAP target

The permutation matrix that exchanges two equal finite registers and its
basic isometry identities.
-/

namespace NLQCLean

open Matrix

/-- SWAP exchanges the two equally sized logical registers. -/
def swapUnitary (ι : Type*) [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix (Equiv.prodComm ι ι) id

theorem isIsometry_swapUnitary (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsIsometry (swapUnitary ι) := by
  show (swapUnitary ι)ᴴ * swapUnitary ι = 1
  rw [swapUnitary, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]

theorem conjTranspose_swapUnitary (ι : Type*) [DecidableEq ι] :
    (swapUnitary ι)ᴴ = swapUnitary ι := by
  ext p q
  simp [swapUnitary, Matrix.conjTranspose_apply, Matrix.one_apply, Prod.ext_iff,
    and_comm, eq_comm]

theorem swapUnitary_mul_conjTranspose (ι : Type*) [Fintype ι] [DecidableEq ι] :
    swapUnitary ι * (swapUnitary ι)ᴴ = 1 := by
  have h := isIsometry_swapUnitary ι
  simpa only [IsIsometry, conjTranspose_swapUnitary] using h

end NLQCLean
