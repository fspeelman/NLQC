import NLQCLean.LinearAlgebra.Bipartite
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Real dimensions of the adjoint matrix spaces


Multiplication by i exchanges the two adjoint spaces, whose direct sum is
the full complex matrix space regarded over the reals.
-/

namespace NLQCLean

open Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Multiplication by i identifies Hermitian and skew-Hermitian matrices
as real vector spaces. -/
noncomputable def selfAdjointEquivSkewAdjoint :
    selfAdjoint (Matrix n n ℂ) ≃ₗ[ℝ] skewAdjoint (Matrix n n ℂ) where
  toFun a := ⟨Complex.I • (a : Matrix n n ℂ),
    Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr a.property⟩
  invFun := skewAdjoint.negISMul
  left_inv a := by
    apply Subtype.ext
    simp [skewAdjoint.negISMul, smul_smul]
  right_inv a := by
    apply Subtype.ext
    exact skewAdjoint.I_smul_neg_I a
  map_add' a b := by apply Subtype.ext; simp [smul_add]
  map_smul' c a := by apply Subtype.ext; simp [smul_comm Complex.I]

omit [DecidableEq n] in
/-- Both adjoint halves have real dimension d². -/
theorem finrank_adjoint_matrix_spaces :
    Module.finrank ℝ (selfAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 ∧
      Module.finrank ℝ (skewAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 := by
  let : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
  let : FiniteDimensional ℝ (skewAdjoint (Matrix n n ℂ)) :=
    inferInstanceAs (FiniteDimensional ℝ (skewAdjoint.submodule ℝ (Matrix n n ℂ)))
  have heq := (selfAdjointEquivSkewAdjoint n).finrank_eq
  have hsum := (StarModule.decomposeProdAdjoint ℝ (Matrix n n ℂ)).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex, Module.finrank_matrix,
    Module.finrank_self] at hsum
  constructor <;> nlinarith

omit [DecidableEq n] in
theorem finrank_skewHermitian : Module.finrank ℝ (skewHermitian n) = Fintype.card n ^ 2 :=
  (finrank_adjoint_matrix_spaces n).2

end NLQCLean
