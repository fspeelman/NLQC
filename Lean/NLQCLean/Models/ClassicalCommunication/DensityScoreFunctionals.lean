import NLQCLean.Models.ClassicalCommunication.JointDensityChannels

/-!
# Continuous scores of finite operation densities

Every genuine real-linear score on complex-linear finite matrix operations
restricts to a continuous real-linear functional on actual continuous
operations. Continuity is a proved finite-dimensional consequence of the
Choi equivalence, not an extra hypothesis on a target score.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance densityScoreMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance densityScoreMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (densityScoreMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance density_score_functionals_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance density_score_functionals_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance density_score_functionals_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance density_score_functionals_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A genuine operation score has an actual continuous functional on
densities, with no added continuity premise. -/
def continuousMatrixOperationRealScore
    (S : (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ) :
    MatrixOperation ι κ →L[ℝ] ℝ := by
  let : FiniteDimensional ℝ (MatrixOperation ι κ) :=
    (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
  exact (S.comp ((ContinuousLinearMap.coeLM ℂ).restrictScalars ℝ)).toContinuousLinearMap

omit [DecidableEq κ] in
/-- The continuous score is the unchanged score of the same operation. -/
@[simp] theorem continuousMatrixOperationRealScore_apply
    (S : (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ)
    (Φ : MatrixOperation ι κ) :
    continuousMatrixOperationRealScore S Φ = S Φ.toLinearMap := rfl

end

end NLQCLean.ClassicalCommunication
