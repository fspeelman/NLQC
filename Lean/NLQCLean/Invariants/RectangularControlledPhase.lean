import NLQCLean.Invariants.ControlledPhase
import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Data.Fin.Embedding

/-!
# Two-level restriction of arbitrary rectangular diagonal phases

Explicit local basis embeddings select the first two levels in each of two
arbitrary finite dimensions at least two. The compressed matrix is the
two-qubit diagonal phase. Explicit local diagonal unitaries and one global
phase remove three entries, leaving their alternating angle at `(1,1)`.
These are matrix identities only: no trace-preserving output decoder,
protocol restriction or diamond-error contractivity is asserted here.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- A diagonal phase matrix in any finite computational basis. -/
noncomputable def diagonalPhaseMatrix {ι : Type*} [DecidableEq ι] (θ : ι → ℝ) :
    Matrix ι ι ℂ := Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I))

theorem complex_exp_angle_mul (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) =
      Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Unitarity holds for all phase entries and does not constrain dimensions. -/
theorem diagonalPhaseMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    (diagonalPhaseMatrix θ)ᴴ * diagonalPhaseMatrix θ = 1 ∧
      diagonalPhaseMatrix θ * (diagonalPhaseMatrix θ)ᴴ = 1 := by
  have hs (i : ι) : star (Complex.exp ((θ i : ℂ) * Complex.I)) *
      Complex.exp ((θ i : ℂ) * Complex.I) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, normSq_exp_angle]
    norm_num
  constructor <;> ext i j <;>
    simp only [diagonalPhaseMatrix, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all [mul_comm]

theorem diagonalPhaseMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ φ : ι → ℝ) :
    diagonalPhaseMatrix θ * diagonalPhaseMatrix φ = diagonalPhaseMatrix (fun i => θ i + φ i) := by
  simp only [diagonalPhaseMatrix, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  exact complex_exp_angle_mul (θ i) (φ i)

theorem diagonalPhaseMatrix_kronecker {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (θ : ι → ℝ) (φ : κ → ℝ) :
    diagonalPhaseMatrix θ ⊗ₖ diagonalPhaseMatrix φ =
      diagonalPhaseMatrix (fun p : ι × κ => θ p.1 + φ p.2) := by
  simp only [diagonalPhaseMatrix, Matrix.diagonal_kronecker_diagonal]
  apply congrArg Matrix.diagonal
  funext p
  exact complex_exp_angle_mul (θ p.1) (φ p.2)

theorem diagonalPhaseMatrix_exp_smul {ι : Type*} [DecidableEq ι]
    (t : ℝ) (θ : ι → ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) • diagonalPhaseMatrix θ =
      diagonalPhaseMatrix (fun i => t + θ i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagonalPhaseMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq]
    exact complex_exp_angle_mul t (θ i)
  · simp [diagonalPhaseMatrix, hij]

/-- Identity columns selected by a basis embedding. -/
def coordinateInclusionMatrix {m n : Type*} [DecidableEq m] (e : n ↪ m) : Matrix m n ℂ :=
  (1 : Matrix m m ℂ).submatrix id e

/-- Matrix multiplication with the inclusion selects the indicated rows and columns. -/
theorem coordinateInclusionMatrix_adjoint_mul {m n : Type*}
    [Fintype m] [DecidableEq m] (e : n ↪ m) (A : Matrix m m ℂ) :
    (coordinateInclusionMatrix e)ᴴ * A * coordinateInclusionMatrix e = A.submatrix e e := by
  unfold coordinateInclusionMatrix
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix m m ℂ).submatrix e (Equiv.refl m) * A *
    (1 : Matrix m m ℂ).submatrix (Equiv.refl m) e = A.submatrix e e
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
  rfl

theorem coordinateInclusionMatrix_isometry {m n : Type*}
    [Fintype m] [DecidableEq m] [DecidableEq n] (e : n ↪ m) :
    IsIsometry (coordinateInclusionMatrix e) := by
  have h := coordinateInclusionMatrix_adjoint_mul e (1 : Matrix m m ℂ)
  rw [Matrix.mul_one] at h
  exact h.trans (Matrix.submatrix_one e e.injective)

/-- Product basis inclusion is the tensor product of the two local inclusions. -/
theorem coordinateInclusionMatrix_prod {m n p q : Type*}
    [DecidableEq m] [DecidableEq p] (eA : n ↪ m) (eB : q ↪ p) :
    coordinateInclusionMatrix (eA.prodMap eB) =
      coordinateInclusionMatrix eA ⊗ₖ coordinateInclusionMatrix eB := by
  ext ⟨a, b⟩ ⟨i, j⟩
  by_cases ha : a = eA i <;> by_cases hb : b = eB j <;>
    simp [coordinateInclusionMatrix, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.kroneckerMap_apply, Function.Embedding.prodMap, ha, hb]

/-- A diagonal phase preserves the selected two-level subspace. -/
theorem diagonalPhaseMatrix_intertwines_coordinateInclusion {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : n ↪ m) (θ : m → ℝ) :
    diagonalPhaseMatrix θ * coordinateInclusionMatrix e =
      coordinateInclusionMatrix e * diagonalPhaseMatrix (θ ∘ e) := by
  ext i j
  simp only [diagonalPhaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    coordinateInclusionMatrix, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
  by_cases hij : i = e j
  · subst i
    simp
  · simp [hij]

/-- The first two basis levels exist in every dimension at least two. -/
def twoLevelEmbedding {d : ℕ} (hd : 2 ≤ d) : Fin 2 ↪ Fin d := Fin.castLEEmb hd

def twoLevelIsometry {d : ℕ} (hd : 2 ≤ d) : Matrix (Fin d) (Fin 2) ℂ :=
  coordinateInclusionMatrix (twoLevelEmbedding hd)

theorem twoLevelIsometry_isometry {d : ℕ} (hd : 2 ≤ d) :
    IsIsometry (twoLevelIsometry hd) := coordinateInclusionMatrix_isometry _

/-- The bipartite input embedding is a tensor product of the two local isometries. -/
noncomputable def rectangularTwoLevelIsometry {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    Matrix (Fin dA × Fin dB) (Fin 2 × Fin 2) ℂ :=
  twoLevelIsometry hA ⊗ₖ twoLevelIsometry hB

theorem rectangularTwoLevelIsometry_isometry {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    IsIsometry (rectangularTwoLevelIsometry hA hB) :=
  (twoLevelIsometry_isometry hA).kronecker (twoLevelIsometry_isometry hB)

/-- An arbitrary rectangular diagonal phase, with independent real entries. -/
noncomputable def rectangularDiagonalPhase {dA dB : ℕ} (θ : Fin dA × Fin dB → ℝ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := diagonalPhaseMatrix θ

theorem rectangularDiagonalPhase_unitary {dA dB : ℕ} (θ : Fin dA × Fin dB → ℝ) :
    (rectangularDiagonalPhase θ)ᴴ * rectangularDiagonalPhase θ = 1 ∧
      rectangularDiagonalPhase θ * (rectangularDiagonalPhase θ)ᴴ = 1 :=
  diagonalPhaseMatrix_unitary θ

noncomputable def rectangularDiagonalPhaseUnitary {dA dB : ℕ}
    (θ : Fin dA × Fin dB → ℝ) : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ :=
  ⟨rectangularDiagonalPhase θ, rectangularDiagonalPhase_unitary θ⟩

/-- The four phases selected by the local input embeddings. -/
def restrictedRectangularAngles {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) : Fin 2 × Fin 2 → ℝ :=
  θ ∘ (twoLevelEmbedding hA).prodMap (twoLevelEmbedding hB)

/-- The adjoint compression equals the restricted two-qubit diagonal phase. -/
theorem rectangularDiagonalPhase_restriction {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) :
    (rectangularTwoLevelIsometry hA hB)ᴴ * rectangularDiagonalPhase θ *
      rectangularTwoLevelIsometry hA hB = diagonalPhaseMatrix (restrictedRectangularAngles hA hB θ) := by
  unfold rectangularTwoLevelIsometry twoLevelIsometry
  rw [← coordinateInclusionMatrix_prod, coordinateInclusionMatrix_adjoint_mul]
  unfold rectangularDiagonalPhase
  rw [diagonalPhaseMatrix, Matrix.submatrix_diagonal_embedding]
  rfl

theorem rectangularDiagonalPhase_intertwines {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) :
    rectangularDiagonalPhase θ * rectangularTwoLevelIsometry hA hB =
      rectangularTwoLevelIsometry hA hB * diagonalPhaseMatrix (restrictedRectangularAngles hA hB θ) := by
  unfold rectangularTwoLevelIsometry twoLevelIsometry
  rw [← coordinateInclusionMatrix_prod]
  exact diagonalPhaseMatrix_intertwines_coordinateInclusion _ θ

/-- The unique surviving nonlocal angle after removing the other three phases. -/
def qubitAlternatingAngle (φ : Fin 2 × Fin 2 → ℝ) : ℝ :=
  φ (1, 1) - φ (1, 0) - φ (0, 1) + φ (0, 0)

noncomputable def qubitPhaseCorrectionA (φ : Fin 2 × Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalPhaseMatrix (fun i => if i = 0 then 0 else φ (0, 0) - φ (1, 0))

noncomputable def qubitPhaseCorrectionB (φ : Fin 2 × Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalPhaseMatrix (fun i => if i = 0 then 0 else φ (0, 0) - φ (0, 1))

noncomputable def qubitGlobalPhaseCorrection (φ : Fin 2 × Fin 2 → ℝ) : ℂ :=
  Complex.exp (((-φ (0, 0) : ℝ) : ℂ) * Complex.I)

theorem qubitPhaseCorrectionA_unitary (φ : Fin 2 × Fin 2 → ℝ) :
    (qubitPhaseCorrectionA φ)ᴴ * qubitPhaseCorrectionA φ = 1 ∧
      qubitPhaseCorrectionA φ * (qubitPhaseCorrectionA φ)ᴴ = 1 :=
  diagonalPhaseMatrix_unitary _

theorem qubitPhaseCorrectionB_unitary (φ : Fin 2 × Fin 2 → ℝ) :
    (qubitPhaseCorrectionB φ)ᴴ * qubitPhaseCorrectionB φ = 1 ∧
      qubitPhaseCorrectionB φ * (qubitPhaseCorrectionB φ)ᴴ = 1 :=
  diagonalPhaseMatrix_unitary _

theorem normSq_qubitGlobalPhaseCorrection (φ : Fin 2 × Fin 2 → ℝ) :
    Complex.normSq (qubitGlobalPhaseCorrection φ) = 1 := normSq_exp_angle _

theorem diagonalPhaseMatrix_corner (θ : ℝ) :
    diagonalPhaseMatrix (fun p : Fin 2 × Fin 2 => if p = (1, 1) then θ else 0) =
      controlledPhase θ := by
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases hp : p = (1, 1) <;>
      simp [diagonalPhaseMatrix, controlledPhase, qubitCornerPhase, hp]
  · simp [diagonalPhaseMatrix, controlledPhase, qubitCornerPhase, hpq]

/-- Explicit local diagonal unitary corrections and a unit global scalar
turn the four-entry phase matrix into the full-angle controlled phase. -/
theorem qubitDiagonalPhase_local_reduction (φ : Fin 2 × Fin 2 → ℝ) :
    qubitGlobalPhaseCorrection φ •
      ((qubitPhaseCorrectionA φ ⊗ₖ qubitPhaseCorrectionB φ) * diagonalPhaseMatrix φ) =
      controlledPhase (qubitAlternatingAngle φ) := by
  unfold qubitGlobalPhaseCorrection qubitPhaseCorrectionA qubitPhaseCorrectionB
  rw [diagonalPhaseMatrix_kronecker, diagonalPhaseMatrix_mul, diagonalPhaseMatrix_exp_smul]
  have hangle :
      (fun p : Fin 2 × Fin 2 => -φ (0, 0) +
        ((if p.1 = 0 then 0 else φ (0, 0) - φ (1, 0)) +
          (if p.2 = 0 then 0 else φ (0, 0) - φ (0, 1)) + φ p)) =
      (fun p : Fin 2 × Fin 2 => if p = (1, 1) then qubitAlternatingAngle φ else 0) := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j
    all_goals norm_num [qubitAlternatingAngle]
    ring
  rw [hangle, diagonalPhaseMatrix_corner]

/-- This is explicitly `theta11 - theta10 - theta01 + theta00` at the
selected levels, with no restriction on the rectangular dimensions except two levels. -/
def rectangularAlternatingAngle {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) : ℝ := qubitAlternatingAngle (restrictedRectangularAngles hA hB θ)

/-- The complete rectangular restriction/local-phase matrix identity. This
does not assert a trace-preserving decoder or an operational restriction theorem. -/
theorem rectangularDiagonalPhase_local_reduction {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) :
    qubitGlobalPhaseCorrection (restrictedRectangularAngles hA hB θ) •
      ((qubitPhaseCorrectionA (restrictedRectangularAngles hA hB θ) ⊗ₖ
          qubitPhaseCorrectionB (restrictedRectangularAngles hA hB θ)) *
        ((rectangularTwoLevelIsometry hA hB)ᴴ * rectangularDiagonalPhase θ *
          rectangularTwoLevelIsometry hA hB)) =
      controlledPhase (rectangularAlternatingAngle hA hB θ) := by
  rw [rectangularDiagonalPhase_restriction]
  exact qubitDiagonalPhase_local_reduction _

end NLQCLean
