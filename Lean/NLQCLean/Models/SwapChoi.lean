import NLQCLean.LinearAlgebra.SchmidtRank
import NLQCLean.Models.SwapTarget

/-!
# Choi realignment of SWAP

The laboratory realignment of SWAP is again a permutation matrix; its
normalized Gram matrix therefore has a flat spectrum.
-/

namespace NLQCLean

open Matrix

/-- The laboratory realignment of SWAP is another permutation with all
singular values one. -/
theorem labChoiMatrix_swapUnitary (ι : Type*) [DecidableEq ι] :
    labChoiMatrix (swapUnitary ι) = swapUnitary ι := by
  ext p q
  simp [labChoiMatrix, swapUnitary, Matrix.one_apply, Prod.ext_iff, eq_comm]

/-- SWAP has D equal squared Schmidt coefficients `1/D`. -/
theorem normalizedLabChoiMatrix_swapUnitary_gram (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    normalizedLabChoiMatrix (swapUnitary ι) * (normalizedLabChoiMatrix (swapUnitary ι))ᴴ =
      Matrix.diagonal (fun _ : ι × ι => ((Fintype.card (ι × ι) : ℝ)⁻¹ : ℂ)) := by
  have hs : (Real.sqrt (Fintype.card (ι × ι) : ℝ) : ℂ) ^ 2 =
      (Fintype.card (ι × ι) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (ι × ι)))
  rw [normalizedLabChoiMatrix, labChoiMatrix_swapUnitary, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, swapUnitary_mul_conjTranspose]
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← sq, hs]
  ext p q
  simp [Matrix.diagonal_apply, Matrix.one_apply]

end NLQCLean
