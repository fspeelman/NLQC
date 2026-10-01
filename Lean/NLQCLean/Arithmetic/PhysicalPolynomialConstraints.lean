import NLQCLean.Arithmetic.ChargedPhysicalCoordinates
import NLQCLean.LinearAlgebra.EuclideanCoordinates
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Integer-polynomial equations for physical constraints

Complex entries are split into raw real and imaginary coordinates. Resource
normalization and rectangular isometry constraints have integer coefficients
and total degree at most two; a sum of their squares has degree at most four.
The equations encode the five physical blocks. No coefficient-height, elimination,
transcendence or named-target arithmetic result is claimed.
-/

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped BigOperators

/-- An integer polynomial evaluated in raw real coordinates. -/
noncomputable def eval {σ : Type*} (x : σ → ℝ) : MvPolynomial σ ℤ →+* ℝ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x

/-- Assemble a complex vector from its two raw coordinates per entry. -/
def coordinateVector {σ ε : Type*} (entry : ε × Fin 2 → σ) (x : σ → ℝ) : ε → ℂ :=
  fun e => ⟨x (entry (e, 0)), x (entry (e, 1))⟩

/-- Assemble a rectangular complex matrix without changing its index types. -/
def coordinateMatrix {σ m n : Type*} (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ) :
    Matrix m n ℂ :=
  Matrix.of fun i j => coordinateVector entry x (i, j)

/-- The unit-resource equation in integer coefficients. -/
noncomputable def unitResourceConstraint {σ ε : Type*} [Fintype ε]
    (entry : ε × Fin 2 → σ) : MvPolynomial σ ℤ :=
  (∑ e, ((X (entry (e, 0))) ^ 2 + (X (entry (e, 1))) ^ 2)) - 1

theorem unitResourceConstraint_eval_eq_zero_iff {σ ε : Type*} [Fintype ε]
    (entry : ε × Fin 2 → σ) (x : σ → ℝ) :
    eval x (unitResourceConstraint entry) = 0 ↔ IsUnitVector (coordinateVector entry x) := by
  classical
  simp [eval, unitResourceConstraint, IsUnitVector, coordinateVector,
    Complex.normSq_apply, pow_two, sub_eq_zero]

theorem unitResourceConstraint_degree_le {σ ε : Type*} [Fintype ε]
    (entry : ε × Fin 2 → σ) : (unitResourceConstraint entry).totalDegree ≤ 2 := by
  classical
  unfold unitResourceConstraint
  apply (MvPolynomial.totalDegree_sub _ _).trans
  refine max_le ?_ (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

/-- Real part of `Vᴴ V - I`, with no rational or square-root rescaling. -/
noncomputable def isometryRealConstraint {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (i j : n) : MvPolynomial σ ℤ :=
  (∑ k, (X (entry ((k, i), 0)) * X (entry ((k, j), 0)) +
    X (entry ((k, i), 1)) * X (entry ((k, j), 1)))) - if i = j then 1 else 0

/-- Imaginary part of `Vᴴ V`; the identity has zero imaginary entries. -/
noncomputable def isometryImagConstraint {σ m n : Type*} [Fintype m]
    (entry : (m × n) × Fin 2 → σ) (i j : n) : MvPolynomial σ ℤ :=
  ∑ k, (X (entry ((k, i), 0)) * X (entry ((k, j), 1)) -
    X (entry ((k, i), 1)) * X (entry ((k, j), 0)))

theorem isometryRealConstraint_eval {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ) (i j : n) :
    eval x (isometryRealConstraint entry i j) =
      (((coordinateMatrix entry x)ᴴ * coordinateMatrix entry x) i j).re -
        ((1 : Matrix n n ℂ) i j).re := by
  classical
  by_cases h : i = j <;>
    simp [eval, isometryRealConstraint, coordinateMatrix, coordinateVector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re, Matrix.one_apply, h]

theorem isometryImagConstraint_eval {σ m n : Type*} [Fintype m]
    (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ) (i j : n) :
    eval x (isometryImagConstraint entry i j) =
      (((coordinateMatrix entry x)ᴴ * coordinateMatrix entry x) i j).im := by
  classical
  simp [eval, isometryImagConstraint, coordinateMatrix, coordinateVector,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_im,
    sub_eq_add_neg]

theorem isometryConstraints_eval_eq_zero_iff {σ m n : Type*}
    [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ) :
    (∀ i j, eval x (isometryRealConstraint entry i j) = 0 ∧
      eval x (isometryImagConstraint entry i j) = 0) ↔
        IsIsometry (coordinateMatrix entry x) := by
  classical
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    apply Complex.ext
    · have hr := (h i j).1
      rw [isometryRealConstraint_eval] at hr
      exact sub_eq_zero.mp hr
    · have hi := (h i j).2
      rw [isometryImagConstraint_eval] at hi
      by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hi
  · intro h i j
    have hij := congrArg (fun V : Matrix n n ℂ => V i j) h
    constructor
    · rw [isometryRealConstraint_eval]
      exact sub_eq_zero.mpr (congrArg Complex.re hij)
    · rw [isometryImagConstraint_eval, hij]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem variableProduct_degree_le {σ : Type*} (i j : σ) :
    (X i * X j : MvPolynomial σ ℤ).totalDegree ≤ 2 :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem isometryRealConstraint_degree_le {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (i j : n) :
    (isometryRealConstraint entry i j).totalDegree ≤ 2 := by
  classical
  unfold isometryRealConstraint
  apply (MvPolynomial.totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (variableProduct_degree_le _ _) (variableProduct_degree_le _ _))
  · split <;> simp

theorem isometryImagConstraint_degree_le {σ m n : Type*} [Fintype m]
    (entry : (m × n) × Fin 2 → σ) (i j : n) :
    (isometryImagConstraint entry i j).totalDegree ≤ 2 := by
  classical
  unfold isometryImagConstraint
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (variableProduct_degree_le _ _) (variableProduct_degree_le _ _))

/-- A finite family of integer equations bundled into one sum of squares. -/
noncomputable def constraintSumSquares {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℤ) : MvPolynomial σ ℤ := ∑ i, (p i) ^ 2

theorem constraintSumSquares_eval_eq_zero_iff {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℤ) (x : σ → ℝ) :
    eval x (constraintSumSquares p) = 0 ↔ ∀ i, eval x (p i) = 0 := by
  classical
  simp only [constraintSumSquares, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff]

theorem constraintSumSquares_degree_le {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℤ) (hp : ∀ i, (p i).totalDegree ≤ 2) :
    (constraintSumSquares p).totalDegree ≤ 4 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (hp i))

end NLQCLean.PhysicalPolynomial
