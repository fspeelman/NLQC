import NLQCLean.Models.ClassicalCommunication.ChoiDensityPositivity
import Mathlib.Data.Matrix.Basis

/-!
# The unnormalized Choi equivalence for finite channel operations

Matrix-unit coefficients give a genuine continuous real-linear equivalence
between complex-linear channel operations and unnormalized Choi matrices.
Complete positivity is equivalent to positive Choi matrices, and trace
preservation is equivalent to an identity input marginal.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance channelMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance channelMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (channelMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

/-- The actual complex-linear map reconstructed from unnormalized
output-input Choi coefficients. -/
def linearMapFromUnnormalizedChoi (C : Matrix (κ × ι) (κ × ι) ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun X := Matrix.of fun k l => ∑ i, ∑ j, C (k, i) (l, j) * X i j
  map_add' X Y := by
    ext k l
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r X := by
    ext k l
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem linearMapFromUnnormalizedChoi_apply
    (C : Matrix (κ × ι) (κ × ι) ℂ) (X : Matrix ι ι ℂ) (k l : κ) :
    linearMapFromUnnormalizedChoi C X k l =
      ∑ i, ∑ j, C (k, i) (l, j) * X i j := rfl

/-- Finite-dimensional continuity makes the reconstructed operation an
actual continuous complex-linear map. -/
def channelFromUnnormalizedChoi (C : Matrix (κ × ι) (κ × ι) ℂ) :
    Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ :=
  (linearMapFromUnnormalizedChoi C).toContinuousLinearMap

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem channelFromUnnormalizedChoi_apply
    (C : Matrix (κ × ι) (κ × ι) ℂ) (X : Matrix ι ι ℂ) (k l : κ) :
    channelFromUnnormalizedChoi C X k l =
      ∑ i, ∑ j, C (k, i) (l, j) * X i j := rfl

/-- Choi coefficients depend real-linearly on the actual channel. -/
def unnormalizedChoiRealLinear :
    (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) →ₗ[ℝ]
      Matrix (κ × ι) (κ × ι) ℂ where
  toFun Φ := unnormalizedChoiMatrix Φ.toLinearMap
  map_add' Φ Ψ := by ext p q; rfl
  map_smul' r Φ := by ext p q; rfl

/-- Reconstruction depends real-linearly on the matrix coefficients. -/
def channelFromUnnormalizedChoiRealLinear :
    Matrix (κ × ι) (κ × ι) ℂ →ₗ[ℝ]
      (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) where
  toFun C := channelFromUnnormalizedChoi C
  map_add' C D := by
    apply ContinuousLinearMap.ext
    intro X
    ext k l
    simp only [channelFromUnnormalizedChoi_apply, Matrix.add_apply,
      _root_.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r C := by
    apply ContinuousLinearMap.ext
    intro X
    ext k l
    simp only [channelFromUnnormalizedChoi_apply, _root_.smul_apply,
      Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

omit [DecidableEq κ] in
/-- Matrix-unit coefficients reconstruct every channel on every matrix. -/
theorem channelFromUnnormalizedChoi_unnormalizedChoi
    (Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) :
    channelFromUnnormalizedChoi (unnormalizedChoiMatrix Φ.toLinearMap) = Φ := by
  apply ContinuousLinearMap.ext
  intro X
  ext k l
  exact (linearMap_matrix_apply Φ.toLinearMap X k l).symm

omit [DecidableEq κ] in
/-- The reconstructed channel has exactly the prescribed Choi matrix. -/
theorem unnormalizedChoi_channelFromUnnormalizedChoi
    (C : Matrix (κ × ι) (κ × ι) ℂ) :
    unnormalizedChoiMatrix (channelFromUnnormalizedChoi C).toLinearMap = C := by
  ext p q
  simp [unnormalizedChoiMatrix, channelFromUnnormalizedChoi_apply,
    Matrix.single_apply, ite_and, mul_ite]

/-- The algebraic unnormalized Choi equivalence, with actual matrix-unit
reconstruction as its inverse. -/
def unnormalizedChoiRealLinearEquiv :
    (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) ≃ₗ[ℝ]
      Matrix (κ × ι) (κ × ι) ℂ where
  __ := unnormalizedChoiRealLinear
  invFun := channelFromUnnormalizedChoi
  left_inv := channelFromUnnormalizedChoi_unnormalizedChoi
  right_inv := unnormalizedChoi_channelFromUnnormalizedChoi

/-- Finite-dimensional continuity in both directions gives a genuine
continuous Choi equivalence, suitable for vector-measure transport. -/
def unnormalizedChoiContinuousRealLinearEquiv :
    (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) ≃L[ℝ]
      Matrix (κ × ι) (κ × ι) ℂ := by
  letI : FiniteDimensional ℝ (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) :=
    (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
  exact unnormalizedChoiRealLinearEquiv.toContinuousLinearEquiv

omit [DecidableEq κ] in
@[simp] theorem unnormalizedChoiContinuousRealLinearEquiv_apply
    (Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) :
    unnormalizedChoiContinuousRealLinearEquiv Φ =
      unnormalizedChoiMatrix Φ.toLinearMap := rfl

omit [DecidableEq κ] in
@[simp] theorem unnormalizedChoiContinuousRealLinearEquiv_symm_apply
    (C : Matrix (κ × ι) (κ × ι) ℂ) :
    unnormalizedChoiContinuousRealLinearEquiv.symm C =
      channelFromUnnormalizedChoi C := rfl

/-- Complete positivity in the original finite-ancilla definition is
equivalent to positivity of the unnormalized Choi coefficient matrix. -/
theorem completelyPositive_iff_unnormalizedChoi_posSemidef [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    CompletelyPositive Φ ↔ (unnormalizedChoiMatrix Φ).PosSemidef := by
  constructor
  · intro hΦ
    rw [unnormalizedChoiMatrix_eq_smul]
    exact hΦ.choiMatrix_posSemidef.smul (by positivity)
  · intro hΦ
    apply (completelyPositive_iff_choiMatrix_posSemidef Φ).mpr
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h := hΦ.smul (show 0 ≤ (Fintype.card ι : ℂ)⁻¹ by positivity)
    simpa only [unnormalizedChoiMatrix_eq_smul, smul_smul,
      inv_mul_cancel₀ hcard, one_smul] using h

omit [Fintype ι] [DecidableEq κ] in
/-- An unnormalized Choi input-marginal entry is the trace of the
corresponding actual matrix-unit image. -/
theorem ptraceA_unnormalizedChoi_apply
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (i j : ι) :
    ptraceA κ ι (unnormalizedChoiMatrix Φ) i j =
      (Φ (Matrix.single i j 1)).trace := rfl

omit [DecidableEq κ] in
/-- Trace preservation on all matrices is exactly the identity input
marginal of the actual unnormalized Choi matrix. -/
theorem tracePreserving_iff_ptraceA_unnormalizedChoi
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    (∀ X, (Φ X).trace = X.trace) ↔
      ptraceA κ ι (unnormalizedChoiMatrix Φ) = 1 := by
  constructor
  · intro hΦ
    ext i j
    rw [ptraceA_unnormalizedChoi_apply, hΦ]
    simp [Matrix.trace, Matrix.diag, Matrix.single_apply, Matrix.one_apply, ite_and, eq_comm]
  · intro hΦ X
    have hsingle (i j : ι) :
        (Φ (Matrix.single i j 1)).trace = (Matrix.single i j (1 : ℂ)).trace := by
      have h := congrArg (fun C : Matrix ι ι ℂ => C i j) hΦ
      rw [ptraceA_unnormalizedChoi_apply] at h
      simpa [Matrix.trace, Matrix.diag, Matrix.single_apply, Matrix.one_apply, ite_and, eq_comm]
        using h
    have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
      ext i j
      simp [Matrix.sum_apply, Matrix.single_apply, ite_and, smul_eq_mul]
    rw [hX]
    simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul, hsingle]

end

end NLQCLean.ClassicalCommunication
