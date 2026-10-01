import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Finite isometric completion of contractions

A matrix whose Gram defect is positive
semidefinite is the top block of an isometry. The extra block has as many
rows as the domain, so a contraction with at most dK rows and dK columns
requires at most 2dK rows. Completion is only an existence statement.
-/

namespace NLQCLean

open Matrix
open scoped MatrixOrder ComplexOrder

/-- The orthogonal complement of an isometry's range projection is positive
semidefinite; this follows from its own Gram factorization. -/
theorem IsIsometry.posSemidef_one_sub_mul_adjoint {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {W : Matrix m n ℂ} (hW : IsIsometry W) : (1 - W * Wᴴ).PosSemidef := by
  have hproj : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW.conjTranspose_mul_self,
      Matrix.one_mul]
  have hgram : (1 - W * Wᴴ)ᴴ * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hproj]
    abel
  exact hgram ▸ Matrix.posSemidef_conjTranspose_mul_self (1 - W * Wᴴ)

/-- Running an isometry backwards on another isometry gives a contraction.
Its Gram defect is the compression of the orthogonal range complement. -/
theorem IsIsometry.posSemidef_adjoint_mul_defect {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    {W : Matrix m n ℂ} {J : Matrix m p ℂ} (hW : IsIsometry W) (hJ : IsIsometry J) :
    (1 - (Wᴴ * J)ᴴ * (Wᴴ * J)).PosSemidef := by
  have h := hW.posSemidef_one_sub_mul_adjoint.conjTranspose_mul_mul_same J
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJ.conjTranspose_mul_self,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

/-- W:complete. The positive Gram defect has a square-root factor. Stacking
that factor below C yields an isometry with C as its exact top block. -/
theorem exists_isometric_completion {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (C : Matrix m n ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (m ⊕ n) n ℂ, IsIsometry T ∧ T.submatrix Sum.inl id = C := by
  classical
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  change 1 - Cᴴ * C = Sᴴ * S at hS
  refine ⟨Matrix.fromRows C S, ?_, rfl⟩
  change (Matrix.fromRows C S)ᴴ * Matrix.fromRows C S = 1
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows, ← hS]
  abel

/-- The physical reverse contraction needs no additional contraction premise. -/
theorem exists_isometric_completion_adjoint_mul {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (W : Matrix m n ℂ) (J : Matrix m p ℂ) (hW : IsIsometry W) (hJ : IsIsometry J) :
    ∃ T : Matrix (n ⊕ p) p ℂ, IsIsometry T ∧ T.submatrix Sum.inl id = Wᴴ * J :=
  exists_isometric_completion (Wᴴ * J) (hW.posSemidef_adjoint_mul_defect hJ)

/-- Positive Gram defects compose, including rectangular matrices. -/
theorem posSemidef_gram_defect_mul {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ)
    (hA : (1 - Aᴴ * A).PosSemidef) (hB : (1 - Bᴴ * B).PosSemidef) :
    (1 - (A * B)ᴴ * (A * B)).PosSemidef := by
  have h := hB.add (hA.conjTranspose_mul_mul_same B)
  convert h using 1
  simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

/-- An isometry is in particular a contraction in the Gram order. -/
theorem IsIsometry.posSemidef_gram_defect {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : IsIsometry A) : (1 - Aᴴ * A).PosSemidef := by
  rw [show Aᴴ * A = 1 from hA, sub_self]
  exact Matrix.PosSemidef.zero

/-- Coordinate inclusion for a finite injection. It only adds zero rows. -/
def coordinateInclusion {m n : Type*} [DecidableEq n] (e : m ↪ n) : Matrix n m ℂ :=
  fun i j => if i = e j then 1 else 0

theorem coordinateInclusion_adjoint_mul {m n p : Type*}
    [Fintype n] [DecidableEq n] (e : m ↪ n) (A : Matrix n p ℂ) :
    (coordinateInclusion e)ᴴ * A = A.submatrix e id := by
  ext i j
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem isIsometry_coordinateInclusion {m n : Type*}
    [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ↪ n) :
    IsIsometry (coordinateInclusion e) := by
  rw [IsIsometry, coordinateInclusion_adjoint_mul]
  ext i j
  simp [coordinateInclusion, Matrix.one_apply, e.injective.eq_iff]

/-- Every cardinality inclusion admits an isometric coordinate inclusion. -/
theorem exists_isometry_of_card_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (h : Fintype.card m ≤ Fintype.card n) :
    ∃ J : Matrix n m ℂ, IsIsometry J := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨coordinateInclusion e, isIsometry_coordinateInclusion e⟩

/-- Fix the original row inclusion using only the dimensions, before choosing
the contraction. This keeps the inclusion out of the six witness variables. -/
theorem exists_uniform_isometric_completion_with_rows (m n : Type*)
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (q : ℕ)
    (hsize : Fintype.card m + Fintype.card n ≤ q) :
    ∃ E : Matrix (Fin q) m ℂ, IsIsometry E ∧
      ∀ C : Matrix m n ℂ, (1 - Cᴴ * C).PosSemidef →
        ∃ T : Matrix (Fin q) n ℂ, IsIsometry T ∧ Eᴴ * T = C := by
  classical
  obtain ⟨J, hJ⟩ := exists_isometry_of_card_le (m := m ⊕ n) (n := Fin q)
    (by simpa using hsize)
  let E := coordinateInclusion (Function.Embedding.inl : m ↪ m ⊕ n)
  have hE : IsIsometry E := isIsometry_coordinateInclusion _
  refine ⟨J * E, hJ.mul hE, ?_⟩
  intro C hC
  obtain ⟨T, hT, htop⟩ := exists_isometric_completion C hC
  refine ⟨J * T, hJ.mul hT, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J,
    hJ.conjTranspose_mul_self, Matrix.one_mul, coordinateInclusion_adjoint_mul]
  exact htop

/-- Pad the completion to a prescribed row dimension. The included original
row space recovers C by adjoint compression, preserving subsequent overlaps. -/
theorem exists_isometric_completion_with_rows {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (C : Matrix m n ℂ) (hC : (1 - Cᴴ * C).PosSemidef) (q : ℕ)
    (hsize : Fintype.card m + Fintype.card n ≤ q) :
    ∃ E : Matrix (Fin q) m ℂ, ∃ T : Matrix (Fin q) n ℂ,
      IsIsometry E ∧ IsIsometry T ∧ Eᴴ * T = C := by
  obtain ⟨E, hE, hcomplete⟩ := exists_uniform_isometric_completion_with_rows m n q hsize
  obtain ⟨T, hT, hCT⟩ := hcomplete C hC
  exact ⟨E, T, hE, hT, hCT⟩

/-- W:complete's sharp row bound: at most as many original rows as columns
gives exactly twice the column dimension after padding. -/
theorem exists_isometric_completion_twice_columns {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (C : Matrix m n ℂ) (hC : (1 - Cᴴ * C).PosSemidef)
    (hsize : Fintype.card m ≤ Fintype.card n) :
    ∃ E : Matrix (Fin (2 * Fintype.card n)) m ℂ,
      ∃ T : Matrix (Fin (2 * Fintype.card n)) n ℂ,
        IsIsometry E ∧ IsIsometry T ∧ Eᴴ * T = C :=
  exists_isometric_completion_with_rows C hC _ (by omega)

end NLQCLean
