import NLQCLean.LinearAlgebra.TraceNormSpectral

/-!
# Positive matrices and trace-distance tests

Positive matrices have trace norm equal to their real trace.
A projection tests a trace-zero difference with the sharp factor one half.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem traceNorm_conjTranspose_le (A : Matrix m n ℂ) : traceNorm Aᴴ ≤ traceNorm A := by
  apply traceNorm_le
  intro B hB
  have he : frobInner B Aᴴ = star (frobInner Bᴴ A) := by
    simp only [frobInner, Matrix.conjTranspose_apply, star_sum, star_mul,
      star_star, mul_comm]
    exact Finset.sum_comm
  rw [he, norm_star]
  exact norm_frobInner_le_traceNorm A Bᴴ (by simpa only [opNorm_conjTranspose] using hB)

@[simp] theorem traceNorm_conjTranspose (A : Matrix m n ℂ) : traceNorm Aᴴ = traceNorm A := by
  exact le_antisymm (traceNorm_conjTranspose_le A)
    (by simpa only [Matrix.conjTranspose_conjTranspose] using traceNorm_conjTranspose_le Aᴴ)

theorem traceNorm_mul_unitary {V : Matrix n n ℂ} (hV : IsIsometry V)
    (hV' : IsIsometry Vᴴ) (A : Matrix m n ℂ) : traceNorm (A * V) = traceNorm A := by
  rw [← traceNorm_conjTranspose (A * V), Matrix.conjTranspose_mul,
    traceNorm_unitary_mul hV' (by simpa only [Matrix.conjTranspose_conjTranspose] using hV),
    traceNorm_conjTranspose]

/-- The diagonal trace norm is the sum of absolute values of its entries. -/
theorem traceNorm_diagonal_real (w : n → ℝ) :
    traceNorm (Matrix.diagonal (fun i => (w i : ℂ))) = ∑ i, |w i| := by
  have hg : (Matrix.diagonal (fun i => (w i : ℂ))) *
      (Matrix.diagonal (fun i => (w i : ℂ)))ᴴ =
      Matrix.diagonal (fun i => ((w i ^ 2 : ℝ) : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, pow_two]
  simpa only [Real.sqrt_sq_eq_abs] using
    traceNorm_eq_sum_sqrt_of_diagonal_gram _ (fun i => w i ^ 2) (fun i => sq_nonneg _) hg

/-- For a Hermitian matrix the trace norm is the sum of absolute eigenvalues. -/
theorem IsHermitian.traceNorm_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  let U := hA.eigenvectorUnitary
  have hU : IsIsometry (U : Matrix n n ℂ) := Unitary.coe_star_mul_self U
  have hU' : IsIsometry (U : Matrix n n ℂ)ᴴ := by
    simpa only [IsIsometry, Matrix.conjTranspose_conjTranspose, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change traceNorm ((U : Matrix n n ℂ) * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
    (U : Matrix n n ℂ)ᴴ) = _
  rw [traceNorm_mul_unitary hU' (by simpa only [Matrix.conjTranspose_conjTranspose] using hU),
    traceNorm_unitary_mul hU hU', traceNorm_diagonal_real]

/-- Density matrices therefore have trace norm one, with no dimension factor. -/
theorem PosSemidef.traceNorm_eq_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  rw [IsHermitian.traceNorm_eq A hA.1]
  simp only [abs_of_nonneg (hA.eigenvalues_nonneg _)]
  have h := congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
  simpa [Complex.re_sum] using h.symm

/-- The reflection about an orthogonal projection is an isometry. -/
theorem isIsometry_projection_reflection {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : IsIsometry (P + P - 1) := by
  unfold IsIsometry
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, hP.eq, Matrix.conjTranspose_one]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, hPP]
  abel

/-- The sharp trace-distance test. Trace zero is essential for the one-half factor. -/
theorem norm_trace_projection_mul_le_half_traceNorm {P A : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hA : A.trace = 0) :
    ‖(P * A).trace‖ ≤ traceNorm A / 2 := by
  have hR := isIsometry_projection_reflection hP hPP
  have h := norm_frobInner_le_traceNorm A (P + P - 1) hR.opNorm_le_one
  have he : frobInner (P + P - 1) A = (2 : ℂ) * (P * A).trace := by
    rw [frobInner_eq_trace, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      hP.eq, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add, hA]
    ring
  rw [he, norm_mul] at h
  norm_num at h
  linarith

/-- Real expectation differences obey the same test bound. -/
theorem re_trace_projection_mul_le_half_traceNorm {P A : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hA : A.trace = 0) :
    (P * A).trace.re ≤ traceNorm A / 2 :=
  (Complex.re_le_norm _).trans (norm_trace_projection_mul_le_half_traceNorm hP hPP hA)

end NLQCLean
