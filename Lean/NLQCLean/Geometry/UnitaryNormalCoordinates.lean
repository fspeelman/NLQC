import NLQCLean.Geometry.UnitaryNormalEmbedding
import NLQCLean.LinearAlgebra.EuclideanCoordinates
import NLQCLean.LinearAlgebra.SchmidtOverlap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean coordinates for unitary normal volume

The ambient measure is real Euclidean volume in the real and imaginary
matrix entries. Unitary left multiplication preserves that volume exactly.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- Real Euclidean matrix-entry coordinates, bundled as a Frobenius isometry. -/
noncomputable def matrixFrobeniusCoordinates (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((m × n) × Fin 2) where
  toLinearEquiv := matrixEuclideanCoordEquiv m n
  norm_map' := norm_matrixEuclideanCoordEquiv

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary multiplication is a real Frobenius isometry on all matrices. -/
noncomputable def unitaryLeftFrobenius (U : Matrix.unitaryGroup n ℂ) :
    Matrix n n ℂ ≃ₗᵢ[ℝ] Matrix n n ℂ where
  toFun X := (U : Matrix n n ℂ) * X
  invFun X := (U : Matrix n n ℂ)ᴴ * X
  left_inv X := by
    change (U : Matrix n n ℂ)ᴴ * ((U : Matrix n n ℂ) * X) = X
    have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := U.property.1
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  right_inv X := by
    change (U : Matrix n n ℂ) * ((U : Matrix n n ℂ)ᴴ * X) = X
    have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := U.property.2
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  map_add' X Y := Matrix.mul_add _ _ _
  map_smul' c X := by simp only [RingHom.id_apply, Matrix.mul_smul]
  norm_map' X := (show IsIsometry (U : Matrix n n ℂ) from U.property.1).frobNorm_mul_eq X

theorem unitaryLeftFrobenius_apply (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    unitaryLeftFrobenius U X = (U : Matrix n n ℂ) * X := rfl

noncomputable def unitaryLeftEuclidean (U : Matrix.unitaryGroup n ℂ) :
    EuclideanSpace ℝ ((n × n) × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) :=
  (matrixFrobeniusCoordinates n n).symm.trans
    ((unitaryLeftFrobenius U).trans (matrixFrobeniusCoordinates n n))

theorem unitaryLeftEuclidean_coordinates (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    unitaryLeftEuclidean U (matrixFrobeniusCoordinates n n X) =
      matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * X) := by
  simp only [unitaryLeftEuclidean, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, unitaryLeftFrobenius_apply]

/-- Ambient normalized Euclidean volume is invariant under every unitary left action. -/
theorem measurePreserving_unitaryLeftEuclidean (U : Matrix.unitaryGroup n ℂ) :
    MeasurePreserving (unitaryLeftEuclidean U) volume volume :=
  (unitaryLeftEuclidean U).measurePreserving

noncomputable def normalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n]
    (z : UnitaryNormalDomain n) : EuclideanSpace ℝ ((n × n) × Fin 2) :=
  matrixFrobeniusCoordinates n n (unitaryNormalMap n z)

theorem continuous_normalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (normalEuclideanMap n) :=
  (matrixFrobeniusCoordinates n n).continuous.comp (continuous_unitaryNormalMap n)

theorem isClosedEmbedding_normalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    Topology.IsClosedEmbedding (normalEuclideanMap n) :=
  (matrixFrobeniusCoordinates n n).toHomeomorph.isClosedEmbedding.comp
    (isClosedEmbedding_unitaryNormalMap n)

theorem measurableEmbedding_normalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (normalEuclideanMap n) :=
  (isClosedEmbedding_normalEuclideanMap n).measurableEmbedding

theorem isCompact_range_normalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact (Set.range (normalEuclideanMap n)) :=
  isCompact_range (continuous_normalEuclideanMap n)

/-- Equivariance supplies the invariance of normal-image volume. -/
theorem normalEuclideanMap_left_mul (U : Matrix.unitaryGroup n ℂ) (z : UnitaryNormalDomain n) :
    normalEuclideanMap n (U * z.1, z.2) = unitaryLeftEuclidean U (normalEuclideanMap n z) := by
  rw [normalEuclideanMap, normalEuclideanMap, unitaryLeftEuclidean_coordinates]
  congr 1
  change ((U : Matrix n n ℂ) * (z.1 : Matrix n n ℂ)) * (1 + z.2.1) =
    (U : Matrix n n ℂ) * ((z.1 : Matrix n n ℂ) * (1 + z.2.1))
  exact Matrix.mul_assoc _ _ _

/-- The normal displacement has exactly the Frobenius length of its normal coordinate. -/
theorem norm_normalEuclideanMap_sub (z : UnitaryNormalDomain n) :
    ‖normalEuclideanMap n z - matrixFrobeniusCoordinates n n (z.1 : Matrix n n ℂ)‖ = ‖z.2.1‖ := by
  rw [normalEuclideanMap, ← map_sub, LinearIsometryEquiv.norm_map]
  have he : unitaryNormalMap n z - (z.1 : Matrix n n ℂ) = (z.1 : Matrix n n ℂ) * z.2.1 := by
    simp only [unitaryNormalMap, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
  rw [he]
  exact (show IsIsometry (z.1 : Matrix n n ℂ) from z.1.property.1).frobNorm_mul_eq _

end NLQCLean
