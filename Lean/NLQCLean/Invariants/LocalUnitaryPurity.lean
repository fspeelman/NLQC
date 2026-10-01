import NLQCLean.Invariants.OperatorSchmidtPurity
import NLQCLean.Models.Targets

/-!
# Purity on finite local-unitary orbits

Realignment carries finite local left and right factors to unitary left and
right factors of the realigned matrix. Cancellation under the trace proves
purity invariance directly, for every matrix and every real normalization.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section Trace

variable {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- The squared Gram trace is unchanged by unitary factors on either side,
including for rectangular matrices. -/
theorem trace_gram_sq_mul_unitaries (R : Matrix m n ℂ)
    {L : Matrix m m ℂ} {S : Matrix n n ℂ}
    (hL : L ∈ Matrix.unitaryGroup m ℂ) (hS : S ∈ Matrix.unitaryGroup n ℂ) :
    Matrix.trace (((L * R * S) * (L * R * S)ᴴ) *
      ((L * R * S) * (L * R * S)ᴴ)) =
      Matrix.trace ((R * Rᴴ) * (R * Rᴴ)) := by
  have hLinv : Lᴴ * L = 1 := Matrix.mem_unitaryGroup_iff'.mp hL
  have hSinv : S * Sᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hS
  have hGram : (L * R * S) * (L * R * S)ᴴ = L * (R * Rᴴ) * Lᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc
      _ = L * R * (S * Sᴴ) * Rᴴ * Lᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hSinv]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hGram]
  calc
    _ = Matrix.trace (L * ((R * Rᴴ) * (R * Rᴴ)) * Lᴴ) := by
      congr 1
      calc
        _ = L * (R * Rᴴ) * (Lᴴ * L) * (R * Rᴴ) * Lᴴ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hLinv]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Matrix.trace (Lᴴ * L * ((R * Rᴴ) * (R * Rᴴ))) :=
      Matrix.trace_mul_cycle L ((R * Rᴴ) * (R * Rᴴ)) Lᴴ
    _ = _ := by rw [hLinv, Matrix.one_mul]

end Trace

section LocalFactors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Realignment intertwines the four finite local factors. No unitarity
assumption is needed for this matrix identity. -/
theorem realign_local_factors (H : Matrix (ι × ι) (ι × ι) ℂ)
    (LA LB RA RB : Matrix ι ι ℂ) :
    realign ((LA ⊗ₖ LB) * H * (RA ⊗ₖ RB)) =
      (LA ⊗ₖ RAᵀ) * realign H * (LBᵀ ⊗ₖ RB) := by
  have hLeftFactors : LA ⊗ₖ LB =
      (LA ⊗ₖ (1 : Matrix ι ι ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ LB) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hRightFactors : RA ⊗ₖ RB =
      (RA ⊗ₖ (1 : Matrix ι ι ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ RB) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hLeft (V : Matrix (ι × ι) (ι × ι) ℂ) :
      realign ((LA ⊗ₖ LB) * V) =
        (LA ⊗ₖ (1 : Matrix ι ι ℂ)) * realign V *
          (LBᵀ ⊗ₖ (1 : Matrix ι ι ℂ)) := by
    rw [hLeftFactors, Matrix.mul_assoc, realign_kroneckerLeft_mul,
      realign_kroneckerRight_mul, ← Matrix.mul_assoc]
  have hRight (V : Matrix (ι × ι) (ι × ι) ℂ) :
      realign (V * (RA ⊗ₖ RB)) =
        ((1 : Matrix ι ι ℂ) ⊗ₖ RAᵀ) * realign V *
          ((1 : Matrix ι ι ℂ) ⊗ₖ RB) := by
    rw [hRightFactors, ← Matrix.mul_assoc, realign_mul_kroneckerRight,
      realign_mul_kroneckerLeft]
  rw [hRight, hLeft]
  calc
    _ = (((1 : Matrix ι ι ℂ) ⊗ₖ RAᵀ) * (LA ⊗ₖ (1 : Matrix ι ι ℂ))) *
        realign H * ((LBᵀ ⊗ₖ (1 : Matrix ι ι ℂ)) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ RB)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [Matrix.one_mul, Matrix.mul_one]

/-- Finite local unitaries preserve the original purity predicate for any
normalization, with no assumption that the middle matrix is unitary. -/
theorem purity_local_unitary_mul (c : ℝ) (H : Matrix (ι × ι) (ι × ι) ℂ)
    {LA LB RA RB : Matrix ι ι ℂ}
    (hLA : LA ∈ Matrix.unitaryGroup ι ℂ) (hLB : LB ∈ Matrix.unitaryGroup ι ℂ)
    (hRA : RA ∈ Matrix.unitaryGroup ι ℂ) (hRB : RB ∈ Matrix.unitaryGroup ι ℂ) :
    purity c ((LA ⊗ₖ LB) * H * (RA ⊗ₖ RB)) = purity c H := by
  have hL : LA ⊗ₖ RAᵀ ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
    Matrix.kronecker_mem_unitary hLA (Matrix.transpose_mem_unitaryGroup_iff.mpr hRA)
  have hS : LBᵀ ⊗ₖ RB ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
    Matrix.kronecker_mem_unitary (Matrix.transpose_mem_unitaryGroup_iff.mpr hLB) hRB
  unfold purity
  rw [realign_local_factors, trace_gram_sq_mul_unitaries (realign H) hL hS]

/-- Purity is constant on the actual double local-unitary orbit. -/
theorem purity_eq_of_mem_unitaryDoubleOrbit (c : ℝ)
    {H V : Matrix (ι × ι) (ι × ι) ℂ}
    (hV : V ∈ unitaryDoubleOrbit ι ι H) : purity c V = purity c H := by
  rcases hV with ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩,
    S, ⟨RA, hRA, RB, hRB, rfl⟩, rfl⟩
  exact purity_local_unitary_mul c H hLA hLB hRA hRB

end LocalFactors

end NLQCLean
