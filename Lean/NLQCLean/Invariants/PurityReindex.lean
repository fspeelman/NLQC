import NLQCLean.LinearAlgebra.RealCoordinates
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Operator purity under a finite local basis equivalence

Realignment commutes with applying the same local basis equivalence to both
parties. Matrix multiplication and trace then preserve the original purity
scalar, for every complex bipartite matrix.
-/

namespace NLQCLean

open Matrix

/-- Trace is unchanged by applying a finite basis equivalence to both indices. -/
theorem trace_submatrix_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid α] (M : Matrix κ κ α) (e : ι ≃ κ) :
    Matrix.trace (M.submatrix e e) = Matrix.trace M := by
  unfold Matrix.trace
  exact e.sum_comp (fun i => M i i)

/-- The same local basis equivalence commutes definitionally with realignment. -/
theorem realign_submatrix_prodCongr {ι κ : Type*} (e : ι ≃ κ)
    (H : Matrix (κ × κ) (κ × κ) ℂ) :
    realign (H.submatrix (e.prodCongr e) (e.prodCongr e)) =
      (realign H).submatrix (e.prodCongr e) (e.prodCongr e) := rfl

/-- Operator purity retains any normalization scalar under a finite local
basis equivalence; no unitarity assumption is needed on the matrix. -/
theorem purity_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (H : Matrix (κ × κ) (κ × κ) ℂ) (e : ι ≃ κ) :
    purity c (H.submatrix (e.prodCongr e) (e.prodCongr e)) = purity c H := by
  simp only [purity, realign_submatrix_prodCongr, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

end NLQCLean
