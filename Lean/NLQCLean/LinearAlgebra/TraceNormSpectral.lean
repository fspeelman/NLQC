import NLQCLean.LinearAlgebra.TraceNorm

/-!
# Spectral characterization of the trace norm

The operator-dual trace norm is the sum of square roots of
Gram eigenvalues, i.e. the ordinary sum of singular values.
-/

namespace NLQCLean

open Matrix WithLp
open scoped Matrix.Norms.Frobenius

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem traceNorm_mul_left_le (L : Matrix p m ℂ) (A : Matrix m n ℂ) :
    traceNorm (L * A) ≤ opNorm L * traceNorm A := by
  have h := traceNorm_mul_mul_le L A (1 : Matrix n n ℂ)
  rw [Matrix.mul_one] at h
  exact h.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (opNorm_one_le (n := n) (𝕜 := ℂ)) (mul_nonneg (opNorm_nonneg L) (traceNorm_nonneg A)))

theorem traceNorm_mul_right_le (A : Matrix m n ℂ) (R : Matrix n p ℂ) :
    traceNorm (A * R) ≤ traceNorm A * opNorm R := by
  have h := traceNorm_mul_mul_le (1 : Matrix m m ℂ) A R
  rw [Matrix.one_mul] at h
  exact h.trans (by
    nlinarith [mul_le_mul_of_nonneg_right
      (opNorm_one_le (n := m) (𝕜 := ℂ)) (mul_nonneg (traceNorm_nonneg A) (opNorm_nonneg R))])

theorem traceNorm_unitary_mul {V : Matrix m m ℂ} (hV : IsIsometry V)
    (hV' : IsIsometry Vᴴ) (A : Matrix m n ℂ) : traceNorm (V * A) = traceNorm A := by
  have hle (W : Matrix m m ℂ) (hW : IsIsometry W) (X : Matrix m n ℂ) :
      traceNorm (W * X) ≤ traceNorm X :=
    (traceNorm_mul_left_le W X).trans (by
      simpa using mul_le_mul_of_nonneg_right hW.opNorm_le_one (traceNorm_nonneg X))
  apply le_antisymm (hle V hV A)
  have h := hle Vᴴ hV' (V * A)
  simpa only [← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul] using h

omit [DecidableEq m] in
/-- Each column has Euclidean norm at most the operator norm. -/
theorem norm_column_le_opNorm (A : Matrix m n ℂ) (j : n) :
    ‖(toLp 2 (fun i => A i j) : EuclideanSpace ℂ m)‖ ≤ opNorm A := by
  have h := norm_toCLM_le A (EuclideanSpace.single j 1)
  simpa [toCLM_apply, EuclideanSpace.single, Matrix.mulVec, dotProduct, Matrix.col_apply'] using h

/-- Each row has the same bound, by adjoint invariance. -/
theorem norm_row_le_opNorm (A : Matrix m n ℂ) (i : m) :
    ‖(toLp 2 (fun j => A i j) : EuclideanSpace ℂ n)‖ ≤ opNorm A := by
  have h := norm_column_le_opNorm Aᴴ i
  rw [opNorm_conjTranspose] at h
  convert h using 1
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Matrix.conjTranspose_apply]

/-- Summing rowwise Cauchy--Schwarz gives a nuclear-norm upper bound. -/
theorem traceNorm_le_sum_row_norms (A : Matrix m n ℂ) :
    traceNorm A ≤ ∑ i, ‖(toLp 2 (fun j => A i j) : EuclideanSpace ℂ n)‖ := by
  apply traceNorm_le
  intro B hB
  have he : frobInner B A = ∑ i, inner ℂ (toLp 2 (fun j => B i j))
      (toLp 2 (fun j => A i j)) := by
    simp [frobInner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact (norm_inner_le_norm _ _).trans (by
    simpa using mul_le_mul_of_nonneg_right ((norm_row_le_opNorm B i).trans hB) (norm_nonneg _))

open scoped Matrix.Norms.L2Operator in
theorem opNorm_diagonal_le_one (w : m → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    opNorm (Matrix.diagonal (fun i => (w i : ℂ))) ≤ 1 := by
  rw [opNorm_eq_l2_opNorm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simpa using hw i)

/-- A diagonal left Gram bounded by one makes a contraction. -/
theorem opNorm_le_one_of_diagonal_row_gram (A : Matrix m n ℂ) (w : m → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hgram : A * Aᴴ = Matrix.diagonal (fun i => (w i : ℂ))) : opNorm A ≤ 1 := by
  have h := opNorm_adjoint_mul_self Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, opNorm_conjTranspose, hgram] at h
  have hle := opNorm_diagonal_le_one w (fun i => by rw [abs_of_nonneg (hw i).1]; exact (hw i).2)
  nlinarith [opNorm_nonneg A]

omit [Fintype m] [DecidableEq n] in
/-- Row norms are square roots of diagonal left-Gram coefficients. -/
theorem norm_row_of_diagonal_gram (A : Matrix m n ℂ) (w : m → ℝ)
    (hgram : A * Aᴴ = Matrix.diagonal (fun i => (w i : ℂ))) (i : m) :
    ‖(toLp 2 (fun j => A i j) : EuclideanSpace ℂ n)‖ = Real.sqrt (w i) := by
  have h := congrArg (fun M : Matrix m m ℂ => (M i i).re) hgram
  have hs : ‖(toLp 2 (fun j => A i j) : EuclideanSpace ℂ n)‖ ^ 2 = w i := by
    simpa [EuclideanSpace.norm_sq_eq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using h
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Row normalization supplies an attaining contraction when the Gram is diagonal. -/
theorem traceNorm_eq_sum_sqrt_of_diagonal_gram (A : Matrix m n ℂ) (w : m → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hgram : A * Aᴴ = Matrix.diagonal (fun i => (w i : ℂ))) :
    traceNorm A = ∑ i, Real.sqrt (w i) := by
  let r : m → ℝ := fun i => (Real.sqrt (w i))⁻¹
  let D : Matrix m m ℂ := Matrix.diagonal (fun i => (r i : ℂ))
  let B : Matrix m n ℂ := D * A
  have hD : Dᴴ = D := by simp [D, Matrix.diagonal_conjTranspose]
  have hnum (i : m) : (r i) ^ 2 * w i = if w i = 0 then 0 else 1 := by
    dsimp only [r]
    by_cases hi : w i = 0
    · simp [hi]
    · rw [if_neg hi]
      calc
        _ = (Real.sqrt (w i))⁻¹ ^ 2 * (Real.sqrt (w i)) ^ 2 := by
          rw [Real.sq_sqrt (hw i)]
        _ = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr
            (lt_of_le_of_ne (hw i) (Ne.symm hi))), one_pow]
  have hgB : B * Bᴴ = Matrix.diagonal (fun i => (((r i) ^ 2 * w i : ℝ) : ℂ)) := by
    calc
      _ = D * (A * Aᴴ) * D := by simp only [B, Matrix.conjTranspose_mul, hD, Matrix.mul_assoc]
      _ = _ := by
        rw [hgram]
        dsimp only [D]
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        push_cast
        ring
  have hB : opNorm B ≤ 1 := opNorm_le_one_of_diagonal_row_gram B _ (fun i => by
    rw [hnum]
    split_ifs <;> norm_num) hgB
  have he : frobInner B A = ∑ i, (Real.sqrt (w i) : ℂ) := by
    rw [frobInner_eq_trace, Matrix.trace_mul_comm]
    have hBA : A * Bᴴ = Matrix.diagonal (fun i => (w i : ℂ) * (r i : ℂ)) := by
      simp only [B, Matrix.conjTranspose_mul, hD, ← Matrix.mul_assoc, hgram, D,
        Matrix.diagonal_mul_diagonal]
    rw [hBA, Matrix.trace_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    have hi : w i * r i = Real.sqrt (w i) := by
      dsimp only [r]
      by_cases hi : w i = 0
      · simp [hi]
      · have hs : Real.sqrt (w i) ≠ 0 := Real.sqrt_ne_zero'.mpr
          (lt_of_le_of_ne (hw i) (Ne.symm hi))
        calc
          w i * (Real.sqrt (w i))⁻¹ =
              (Real.sqrt (w i) * Real.sqrt (w i)) * (Real.sqrt (w i))⁻¹ := by
            rw [← sq, Real.sq_sqrt (hw i)]
          _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
    exact_mod_cast hi
  apply le_antisymm
  · calc
      traceNorm A ≤ ∑ i, ‖(toLp 2 (fun j => A i j) : EuclideanSpace ℂ n)‖ :=
        traceNorm_le_sum_row_norms A
      _ = _ := Finset.sum_congr rfl (fun i _ => norm_row_of_diagonal_gram A w hgram i)
  · have h := norm_frobInner_le_traceNorm A B hB
    rw [he, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _))] at h
    exact h

/-- The dual norm is exactly the sum of singular values: the square roots
of all left-Gram eigenvalues, including their zero multiplicities. -/
theorem traceNorm_eq_sum_sqrt_schmidtWeights (A : Matrix m n ℂ) :
    traceNorm A = ∑ i, Real.sqrt (schmidtWeights A i) := by
  obtain ⟨V, hV, hV', hg⟩ := exists_schmidt_coordinates A
  rw [← traceNorm_unitary_mul hV' (by simpa using hV) A]
  exact traceNorm_eq_sum_sqrt_of_diagonal_gram _ _ (schmidtWeights_nonneg A) hg

end NLQCLean
