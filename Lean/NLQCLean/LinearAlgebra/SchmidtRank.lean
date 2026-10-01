import NLQCLean.LinearAlgebra.SupportFactorization

/-!
# Laboratory-cut rank accounting

Moving a finite register across a bipartite
cut increases coefficient-matrix rank by at most that register's dimension.
The matrices and register dimensions are arbitrary; no support-size assumption
or physical normalization is used in these algebraic bounds.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- Moving a register from the row laboratory to the column laboratory costs
at most its entire dimension in Schmidt rank. -/
theorem rank_move_register {a b μ : Type*} [Fintype a] [Fintype b] [Fintype μ]
    (M : Matrix (a × μ) b ℂ) :
    (Matrix.of fun i (j : μ × b) ↦ M (i, j.1) j.2).rank ≤
      M.rank * Fintype.card μ := by
  classical
  obtain ⟨J, B, _, hM⟩ := exists_isometry_rank_factorization M
  let L : Matrix a (Fin M.rank × μ) ℂ := fun i k ↦ J (i, k.2) k.1
  let R : Matrix (Fin M.rank × μ) (μ × b) ℂ :=
    fun k j ↦ if k.2 = j.1 then B k.1 j.2 else 0
  have hfac : (Matrix.of fun i (j : μ × b) ↦ M (i, j.1) j.2) = L * R := by
    ext i j
    change M (i, j.1) j.2 = ∑ k, L i k * R k j
    simp only [L, R, Fintype.sum_prod_type, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact congrArg (fun N : Matrix (a × μ) b ℂ ↦ N (i, j.1) j.2) hM
  rw [hfac]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa using Matrix.rank_le_card_width L)

/-- The coefficient matrix of an unnormalized Choi vector, with each input
reference retained in its own laboratory. -/
def labChoiMatrix {a b i j : Type*} (F : Matrix (a × b) (i × j) ℂ) :
    Matrix (a × i) (b × j) ℂ := fun x y ↦ F (x.1, y.1) (x.2, y.2)

/-- Multiplying every coefficient by a scalar cannot increase Schmidt rank. -/
theorem rank_smul_le {a b : Type*} [Fintype a] [Fintype b]
    (c : ℂ) (M : Matrix a b ℂ) : (c • M).rank ≤ M.rank := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (Matrix.rank_smul_of_mem_nonZeroDivisors M
      (mem_nonZeroDivisors_of_ne_zero hc)).le

open scoped Matrix.Norms.Frobenius in
/-- Regrouping Choi coefficients preserves the ordinary Frobenius norm. -/
theorem norm_labChoiMatrix {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (F : Matrix (a × b) (i × j) ℂ) : ‖labChoiMatrix F‖ = ‖F‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [frobNorm_sq, Fintype.sum_prod_type, labChoiMatrix]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]

/-- The normalized purified Choi coefficients. The inverse square root
normalizes by the full logical input dimension, independently of the cut. -/
noncomputable def normalizedLabChoiMatrix {a b i j : Type*}
    [Fintype i] [Fintype j] (F : Matrix (a × b) (i × j) ℂ) :
    Matrix (a × i) (b × j) ℂ :=
  ((Real.sqrt (Fintype.card (i × j) : ℝ))⁻¹ : ℂ) • labChoiMatrix F

/-- Choi normalization does not increase laboratory rank, including empty inputs. -/
theorem rank_normalizedLabChoiMatrix_le {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (F : Matrix (a × b) (i × j) ℂ) :
    (normalizedLabChoiMatrix F).rank ≤ (labChoiMatrix F).rank :=
  rank_smul_le _ _

/-- Local output maps act locally on the Choi coefficient matrix, including
the untouched reference registers. The right action uses transpose. -/
theorem labChoiMatrix_local {a b c d i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq i] [DecidableEq j]
    (A : Matrix c a ℂ) (B : Matrix d b ℂ) (F : Matrix (a × b) (i × j) ℂ) :
    labChoiMatrix ((A ⊗ₖ B) * F) =
      (A ⊗ₖ (1 : Matrix i i ℂ)) * labChoiMatrix F *
        (B ⊗ₖ (1 : Matrix j j ℂ))ᵀ := by
  ext x y
  simp [labChoiMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_left_comm (B y.1 _)]

/-- Local maps cannot increase laboratory Schmidt rank. Isometry is not
needed for this inequality. -/
theorem rank_labChoiMatrix_local_le {a b c d i j : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype i] [Fintype j]
    (A : Matrix c a ℂ) (B : Matrix d b ℂ) (F : Matrix (a × b) (i × j) ℂ) :
    (labChoiMatrix ((A ⊗ₖ B) * F)).rank ≤ (labChoiMatrix F).rank := by
  classical
  rw [labChoiMatrix_local]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end NLQCLean
