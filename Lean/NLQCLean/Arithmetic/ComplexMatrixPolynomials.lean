import NLQCLean.Arithmetic.PhysicalScorePolynomial
import NLQCLean.LinearAlgebra.RealCoordinates

/-!
# Integer polynomial operations on complex matrices

Pairs of integer polynomials retain the real and imaginary parts of every
entry. These operations evaluate to the existing complex matrix operations,
including the production realignment and purity definitions. Matrix equality
and isometry are encoded by sums of squared entry differences.
-/

noncomputable section

namespace NLQCLean.PhysicalPolynomial.ComplexPair

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped BigOperators

variable {σ : Type*}

/-- An integer complex constant, with zero imaginary part. -/
def constant (n : ℤ) : ComplexPair σ := (C n, 0)

/-- Subtraction of real and imaginary polynomial parts. -/
def subtract (p q : ComplexPair σ) : ComplexPair σ := (p.1 - q.1, p.2 - q.2)

@[simp] theorem evaluate_constant (x : σ → ℝ) (n : ℤ) :
    evaluate x (constant n) = (n : ℂ) := by
  apply Complex.ext <;> simp [evaluate, constant, PhysicalPolynomial.eval]

@[simp] theorem evaluate_subtract (x : σ → ℝ) (p q : ComplexPair σ) :
    evaluate x (subtract p q) = evaluate x p - evaluate x q := by
  apply Complex.ext <;> simp [evaluate, subtract]

theorem eval_realPart (x : σ → ℝ) (p : ComplexPair σ) :
    PhysicalPolynomial.eval x p.1 = (evaluate x p).re := rfl

theorem eval_imagPart (x : σ → ℝ) (p : ComplexPair σ) :
    PhysicalPolynomial.eval x p.2 = (evaluate x p).im := rfl

/-- The identity matrix represented by integer constant pairs. -/
def matrixIdentity (ι : Type*) [DecidableEq ι] : Matrix ι ι (ComplexPair σ) :=
  Matrix.of fun i j => if i = j then constant 1 else constant 0

/-- Conjugate transpose exchanges indices and conjugates the pair. -/
def matrixConjTranspose {m n : Type*} (P : Matrix m n (ComplexPair σ)) :
    Matrix n m (ComplexPair σ) :=
  Matrix.of fun i j => conjugate (P j i)

/-- The same entry permutation as production realignment. -/
def matrixRealign {ι : Type*} (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) :
    Matrix (ι × ι) (ι × ι) (ComplexPair σ) :=
  Matrix.of fun p q => P (p.1, q.1) (p.2, q.2)

/-- Trace of a matrix of complex polynomial pairs. -/
def matrixTrace {ι : Type*} [Fintype ι] (P : Matrix ι ι (ComplexPair σ)) :
    ComplexPair σ := sum (fun i => P i i)

@[simp] theorem evaluateMatrix_matrixIdentity {ι : Type*} [DecidableEq ι]
    (x : σ → ℝ) : evaluateMatrix x (matrixIdentity ι) = (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j <;>
    simp [evaluateMatrix, matrixIdentity, Matrix.one_apply, hij]

@[simp] theorem evaluateMatrix_matrixConjTranspose {m n : Type*}
    (x : σ → ℝ) (P : Matrix m n (ComplexPair σ)) :
    evaluateMatrix x (matrixConjTranspose P) = (evaluateMatrix x P)ᴴ := by
  ext i j
  exact evaluate_conjugate x (P j i)

@[simp] theorem evaluateMatrix_matrixRealign {ι : Type*}
    (x : σ → ℝ) (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) :
    evaluateMatrix x (matrixRealign P) = NLQCLean.realign (evaluateMatrix x P) := rfl

@[simp] theorem evaluate_matrixTrace {ι : Type*} [Fintype ι]
    (x : σ → ℝ) (P : Matrix ι ι (ComplexPair σ)) :
    evaluate x (matrixTrace P) = Matrix.trace (evaluateMatrix x P) := by
  simp only [matrixTrace, evaluate_sum, Matrix.trace, Matrix.diag, evaluateMatrix,
    Matrix.of_apply]

/-- Integer polynomial for the unnormalized realignment-purity numerator. -/
def purityNumerator {ι : Type*} [Fintype ι]
    (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) : MvPolynomial σ ℤ :=
  let R := matrixRealign P
  let G := matrixMultiply R (matrixConjTranspose R)
  (matrixTrace (matrixMultiply G G)).1

/-- Evaluation is the exact real trace in the production purity definition. -/
theorem eval_purityNumerator {ι : Type*} [Fintype ι]
    (x : σ → ℝ) (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) :
    PhysicalPolynomial.eval x (purityNumerator P) =
      (Matrix.trace ((NLQCLean.realign (evaluateMatrix x P) *
        (NLQCLean.realign (evaluateMatrix x P))ᴴ) *
          (NLQCLean.realign (evaluateMatrix x P) *
            (NLQCLean.realign (evaluateMatrix x P))ᴴ))).re := by
  simp only [purityNumerator, eval_realPart, evaluate_matrixTrace,
    evaluateMatrix_matrixMultiply, evaluateMatrix_matrixConjTranspose,
    evaluateMatrix_matrixRealign]

/-- The real normalization remains explicit; the numerator has integer coefficients. -/
theorem purity_evaluateMatrix {ι : Type*} [Fintype ι]
    (c : ℝ) (x : σ → ℝ) (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) :
    NLQCLean.purity c (evaluateMatrix x P) = c * PhysicalPolynomial.eval x (purityNumerator P) := by
  rw [eval_purityNumerator]
  rfl

/-- A single integer equation for equality of two matrices of complex pairs. -/
def matrixEqualityConstraint {m n : Type*} [Fintype m] [Fintype n]
    (P Q : Matrix m n (ComplexPair σ)) : MvPolynomial σ ℤ :=
  ∑ p : m × n, normSquare (subtract (P p.1 p.2) (Q p.1 p.2))

theorem eval_matrixEqualityConstraint {m n : Type*} [Fintype m] [Fintype n]
    (x : σ → ℝ) (P Q : Matrix m n (ComplexPair σ)) :
    PhysicalPolynomial.eval x (matrixEqualityConstraint P Q) =
      ∑ p : m × n, Complex.normSq
        (evaluateMatrix x P p.1 p.2 - evaluateMatrix x Q p.1 p.2) := by
  simp only [matrixEqualityConstraint, map_sum, eval_normSquare, evaluate_subtract,
    evaluateMatrix, Matrix.of_apply]

/-- The equality equation loses no real or imaginary entry condition. -/
theorem matrixEqualityConstraint_eval_eq_zero_iff {m n : Type*}
    [Fintype m] [Fintype n] (x : σ → ℝ) (P Q : Matrix m n (ComplexPair σ)) :
    PhysicalPolynomial.eval x (matrixEqualityConstraint P Q) = 0 ↔
      evaluateMatrix x P = evaluateMatrix x Q := by
  classical
  rw [eval_matrixEqualityConstraint,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, Complex.normSq_eq_zero, sub_eq_zero]
  constructor
  · intro h
    ext i j
    exact h (i, j)
  · intro h p
    rw [h]

/-- The actual `Vᴴ V = I` equation, without assuming isometry of a polynomial matrix. -/
def matrixIsometryConstraint {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m n (ComplexPair σ)) : MvPolynomial σ ℤ :=
  matrixEqualityConstraint (matrixMultiply (matrixConjTranspose P) P) (matrixIdentity n)

theorem matrixIsometryConstraint_eval_eq_zero_iff {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (x : σ → ℝ) (P : Matrix m n (ComplexPair σ)) :
    PhysicalPolynomial.eval x (matrixIsometryConstraint P) = 0 ↔
      NLQCLean.IsIsometry (evaluateMatrix x P) := by
  simp only [matrixIsometryConstraint, matrixEqualityConstraint_eval_eq_zero_iff,
    evaluateMatrix_matrixMultiply, evaluateMatrix_matrixConjTranspose,
    evaluateMatrix_matrixIdentity, NLQCLean.IsIsometry]

end NLQCLean.PhysicalPolynomial.ComplexPair
