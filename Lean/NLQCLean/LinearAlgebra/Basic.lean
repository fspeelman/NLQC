/-
Norm conventions for the NLQC formalization.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix norm conventions

The paper uses two matrix norms (see the snapshot, L1163-1170 and L713):

* the Frobenius norm `‖·‖_F`, which is the norm of essentially every estimate;
* the operator norm `‖·‖_op`, used for principal-angle defects, velocity
  estimates and unitary normal coordinates.

Both live on `Matrix m n 𝕜`, and Mathlib supplies each as a *scoped instance*
(`Matrix.Norms.Frobenius` and `Matrix.Norms.L2Operator`).  Opening both at once
makes the `‖·‖` notation ambiguous, so this project fixes the convention:

* the Frobenius norm is **the** `NormedAddCommGroup`/`NormedSpace` instance on
  `Matrix m n 𝕜`, obtained by `open Matrix
open scoped Matrix.Norms.Frobenius`.  It is the
  instance that gives `Matrix m n 𝕜` its metric and hence its derivatives, so
  every `HasDerivAt` in this development is Frobenius-differentiability;
* the operator norm is the plain function `NLQCLean.opNorm`, defined through
  the identification with continuous linear maps on `EuclideanSpace`.  It is
  *not* an instance, so it can be mentioned freely alongside `‖·‖`.

These conventions allow both norms to appear in the same estimate without
changing the ambient metric or derivative.
-/

namespace NLQCLean

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The matrix `A` viewed as a continuous linear map of Euclidean spaces. -/
noncomputable def toCLM (A : Matrix m n 𝕜) :
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

/-- The operator (spectral) norm `‖A‖_op`, written `‖·‖_op` in the paper. -/
noncomputable def opNorm (A : Matrix m n 𝕜) : ℝ := ‖toCLM A‖

omit [DecidableEq m] in
@[simp]
theorem toCLM_apply (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    toCLM A x = (WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) : EuclideanSpace 𝕜 m) := rfl

omit [DecidableEq m] in
theorem opNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ opNorm A := norm_nonneg _

omit [DecidableEq m] in
/-- The defining property of the operator norm. -/
theorem norm_toCLM_le (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖toCLM A x‖ ≤ opNorm A * ‖x‖ :=
  (toCLM A).le_opNorm x

omit [DecidableEq m] in
/-- `NLQCLean.opNorm` is Mathlib's scoped `l2` operator norm, so every lemma in
`Mathlib.Analysis.CStarAlgebra.Matrix` transfers.  It is kept as a function
rather than an instance so that it can be mentioned in the same statement as
the Frobenius norm. -/
theorem opNorm_eq_l2_opNorm (A : Matrix m n 𝕜) : opNorm A = ‖A‖ := rfl

/-- `‖Aᴴ‖_op = ‖A‖_op`.  Used for the second half of the residual bound in
`lem:cross-gram-rigidity` (snapshot L759-766), where `‖B†(I - AA†)‖_op` has to
be recognised as the defect `α = ‖(I - AA†)B‖_op`. -/
theorem opNorm_conjTranspose (A : Matrix m n 𝕜) : opNorm Aᴴ = opNorm A := by
  simpa only [opNorm_eq_l2_opNorm] using Matrix.l2_opNorm_conjTranspose A

omit [DecidableEq l] in
/-- Submultiplicativity of the operator norm. -/
theorem opNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [opNorm_eq_l2_opNorm] using Matrix.l2_opNorm_mul A B

end OperatorNorm

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

omit [DecidableEq m] [DecidableEq n] in
/-- The square of the Frobenius norm is the sum of the squared entry norms.
Mathlib states `Matrix.frobenius_norm_def` with real powers; this is the
natural-power form actually used below. -/
theorem frobNorm_sq (M : Matrix m n 𝕜) : ‖M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hS : (0:ℝ) ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2:ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have h1 : ‖M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ (2:ℝ) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hS
  rw [h1]
  simp

omit [DecidableEq m] [DecidableEq n] in
/-- Column form of the squared Frobenius norm. -/
theorem frobNorm_sq_eq_sum_col (M : Matrix m n 𝕜) :
    ‖M‖ ^ 2 = ∑ j, ‖(WithLp.toLp 2 (fun i => M i j) : EuclideanSpace 𝕜 m)‖ ^ 2 := by
  rw [frobNorm_sq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simp [EuclideanSpace.norm_sq_eq]

omit [DecidableEq l] [DecidableEq n] in
/-- The mixed Frobenius/operator bound `‖A * B‖_F ≤ ‖A‖_op ‖B‖_F`.

This is the inequality that `lem:cross-gram-rigidity` uses twice to bound the
residual `E` (snapshot L759-766), and it is the one fact about the two norms
that Mathlib does not supply: it has `Matrix.frobenius_norm_mul`
(`‖A * B‖_F ≤ ‖A‖_F ‖B‖_F`) and `Matrix.l2_opNorm_mul`, but not the mixed
form, which is strictly stronger than the first since `‖·‖_op ≤ ‖·‖_F`. -/
theorem frobNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    ‖A * B‖ ≤ opNorm A * ‖B‖ := by
  have hsq : ‖A * B‖ ^ 2 ≤ (opNorm A * ‖B‖) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col, mul_pow, frobNorm_sq_eq_sum_col, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcol : (WithLp.toLp 2 (fun i => (A * B) i j) : EuclideanSpace 𝕜 l)
        = toCLM A (WithLp.toLp 2 (fun i => B i j)) := by
      ext i
      simp [toCLM, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [hcol, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_toCLM_le _ _) 2
  have h1 : ‖A * B‖ = √(‖A * B‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  have h2 : opNorm A * ‖B‖ = √((opNorm A * ‖B‖) ^ 2) :=
    (Real.sqrt_sq (mul_nonneg (opNorm_nonneg A) (norm_nonneg B))).symm
  rw [h1, h2]
  exact Real.sqrt_le_sqrt hsq

omit [DecidableEq l] in
/-- The mirror bound `‖A * B‖_F ≤ ‖A‖_F ‖B‖_op`, obtained from
`NLQCLean.frobNorm_mul_le` by conjugate transposition.  Both sides of the
residual estimate in `lem:cross-gram-rigidity` are needed: one contracts the
defect against `Ȧ`, the other against `Ḃ`. -/
theorem frobNorm_mul_le' (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    ‖A * B‖ ≤ ‖A‖ * opNorm B := by
  have h := frobNorm_mul_le Bᴴ Aᴴ
  rw [← Matrix.conjTranspose_mul, Matrix.frobenius_norm_conjTranspose,
    Matrix.frobenius_norm_conjTranspose, opNorm_conjTranspose] at h
  linarith

omit [DecidableEq n] in
/-- Frobenius norm of a one-column matrix.

Mathlib's `Matrix.frobenius_norm_replicateCol` is stated against the *local*
`Matrix.frobeniusSeminormedAddCommGroup` instance of its own section rather
than the `Matrix.Norms.Frobenius` scoped instance, so it does not apply here
and is reproved. -/
theorem frobNorm_replicateCol (v : n → 𝕜) :
    ‖(Matrix.replicateCol (Fin 1) v : Matrix n (Fin 1) 𝕜)‖
      = ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ := by
  have h : ‖(Matrix.replicateCol (Fin 1) v : Matrix n (Fin 1) 𝕜)‖ ^ 2
      = ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ ^ 2 := by
    rw [frobNorm_sq, EuclideanSpace.norm_sq_eq]
    simp
  have h1 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

omit [DecidableEq m] in
/-- `‖A‖_op ≤ ‖A‖_F`.  This is what lets `prop:protocol-cross-gram` replace the
paper's operator-norm defect `α` by the Frobenius quantity
`√h = ‖(I - BB†)A‖_F` (snapshot L1536-1537). -/
theorem opNorm_le_frobNorm (A : Matrix m n 𝕜) : opNorm A ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hmul : A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)
      = Matrix.replicateCol (Fin 1) (A *ᵥ WithLp.ofLp x) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc ‖toCLM A x‖
      = ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ := by
        rw [hmul, frobNorm_replicateCol]; rfl
    _ ≤ ‖A‖ * ‖(Matrix.replicateCol (Fin 1) (WithLp.ofLp x) : Matrix n (Fin 1) 𝕜)‖ :=
        Matrix.frobenius_norm_mul _ _
    _ = ‖A‖ * ‖x‖ := by rw [frobNorm_replicateCol]

end FrobeniusNorm

end NLQCLean
