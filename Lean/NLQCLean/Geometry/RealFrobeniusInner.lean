import NLQCLean.Geometry.UnitaryNormalCoordinates
import NLQCLean.Geometry.CubicProjection

/-!
# The real Frobenius inner product

The matrix space retains its existing Frobenius norm. Its real
inner product is transported from the explicit orthonormal entry coordinates.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- The real inner product inducing the Frobenius norm. -/
@[instance_reducible]
noncomputable def realFrobeniusInnerProductSpace (m n : Type*) [Fintype m] [Fintype n] :
    InnerProductSpace ℝ (Matrix m n ℂ) where
  toNormedSpace := inferInstance
  inner A B := inner ℝ (matrixFrobeniusCoordinates m n A) (matrixFrobeniusCoordinates m n B)
  norm_sq_eq_re_inner A := by
    rw [← (matrixFrobeniusCoordinates m n).norm_map A]
    exact InnerProductSpace.norm_sq_eq_re_inner _
  conj_inner_symm A B := inner_conj_symm _ _
  add_left A B C := by rw [map_add, inner_add_left]
  smul_left A B c := by rw [map_smul, inner_smul_left]

end NLQCLean

namespace Matrix.Norms.Frobenius
attribute [scoped instance] NLQCLean.realFrobeniusInnerProductSpace
end Matrix.Norms.Frobenius

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem realFrobeniusInner_eq_re {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : inner ℝ A B = (frobInner A B).re := by
  have h₁ := norm_sub_sq_real A B
  have h₂ := frobNorm_sub_sq A B
  have h₃ := congrArg Complex.re (frobInner_conj A B)
  simp only [Complex.star_def, Complex.conj_re] at h₃
  linarith

/-- The two adjoint spaces are orthogonal for the real inner product. -/
theorem inner_hermitian_skew_eq_zero {n : Type*} [Fintype n]
    (S K : Matrix n n ℂ) (hS : Sᴴ = S) (hK : Kᴴ = -K) : inner ℝ S K = 0 := by
  rw [realFrobeniusInner_eq_re]
  exact frobInner_hermitian_skew_re_eq_zero S K hS hK

theorem norm_add_hermitian_skew_sq {n : Type*} [Fintype n]
    (S K : Matrix n n ℂ) (hS : Sᴴ = S) (hK : Kᴴ = -K) :
    ‖S + K‖ ^ 2 = ‖S‖ ^ 2 + ‖K‖ ^ 2 := by
  rw [norm_add_sq_real, inner_hermitian_skew_eq_zero S K hS hK, mul_zero, add_zero]

end NLQCLean
