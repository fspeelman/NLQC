import NLQCLean.Invariants.ControlledPhase
import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder

/-!
# Controlled phases with identity spectators

The first qubit in each laboratory carries the phase. Every spectator basis
state is retained. Fixing one spectator input in each laboratory, then
discarding both spectators by genuine local Stinespring channels, gives the
actual two-qubit controlled-phase channel.
-/

noncomputable section

namespace NLQCLean

universe u v

open Matrix
open ClassicalCommunication
open scoped Kronecker

variable {σA : Type u} {σB : Type v}

/-- The source first-qubit controlled phase, with identity on both spectator registers. -/
def spectatorControlledPhase [DecidableEq σA] [DecidableEq σB] (θ : ℝ) :
    Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ :=
  Matrix.diagonal (fun p => if p.1.1 = 1 ∧ p.2.1 = 1 then
    Complex.exp ((θ : ℂ) * Complex.I) else 1)

@[simp] theorem spectatorControlledPhase_apply [DecidableEq σA] [DecidableEq σB]
    (θ : ℝ) (p q : (Fin 2 × σA) × (Fin 2 × σB)) :
    spectatorControlledPhase θ p q =
      if p = q then (if p.1.1 = 1 ∧ p.2.1 = 1 then
        Complex.exp ((θ : ℂ) * Complex.I) else 1) else 0 := rfl

theorem spectatorControlledPhase_unitary [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (θ : ℝ) :
    (spectatorControlledPhase (σA := σA) (σB := σB) θ)ᴴ * spectatorControlledPhase θ = 1 ∧
      spectatorControlledPhase (σA := σA) (σB := σB) θ * (spectatorControlledPhase θ)ᴴ = 1 := by
  have hz : star (Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, normSq_exp_angle]
    norm_num
  let f : ((Fin 2 × σA) × (Fin 2 × σB)) → ℂ := fun p =>
    if p.1.1 = 1 ∧ p.2.1 = 1 then Complex.exp ((θ : ℂ) * Complex.I) else 1
  have hstar : ∀ p, star (f p) * f p = 1 := by
    intro p
    dsimp only [f]
    split_ifs
    · exact hz
    · simp
  have hother : ∀ p, f p * star (f p) = 1 := by
    intro p
    rw [mul_comm]
    exact hstar p
  change (Matrix.diagonal f)ᴴ * Matrix.diagonal f = 1 ∧
    Matrix.diagonal f * (Matrix.diagonal f)ᴴ = 1
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i => star (f i) * f i) = 1
    rw [show (fun i => star (f i) * f i) = (fun _ => 1) from funext hstar,
      Matrix.diagonal_one]
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i => f i * star (f i)) = 1
    rw [show (fun i => f i * star (f i)) = (fun _ => 1) from funext hother,
      Matrix.diagonal_one]

/-- Fix a spectator basis state while retaining the input qubit label. -/
def spectatorInputEmbedding {σ : Type*} (a0 : σ) : Fin 2 ↪ Fin 2 × σ :=
  ⟨fun i => (i, a0), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem spectatorInputEmbedding_apply {σ : Type*} (a0 : σ) (i : Fin 2) :
    spectatorInputEmbedding a0 i = (i, a0) := rfl

def spectatorInputIsometry {σ : Type*} [DecidableEq σ] (a0 : σ) :
    Matrix (Fin 2 × σ) (Fin 2) ℂ := coordinateInclusionMatrix (spectatorInputEmbedding a0)

theorem spectatorInputIsometry_isometry {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a0 : σ) : IsIsometry (spectatorInputIsometry a0) :=
  coordinateInclusionMatrix_isometry _

/-- The identity local matrix, read as qubit output together with spectator environment. -/
def spectatorOutputStinespring (σ : Type*) [DecidableEq σ] :
    Matrix (Fin 2 × σ) (Fin 2 × σ) ℂ := 1

theorem spectatorOutputStinespring_isometry (σ : Type*) [Fintype σ] [DecidableEq σ] :
    IsIsometry (spectatorOutputStinespring σ) := isIsometry_one

/-- Joint output dilation with qubits before the two actual spectator environments. -/
def spectatorOutputRegrouped [DecidableEq σA] [DecidableEq σB] :
    Matrix ((Fin 2 × Fin 2) × (σA × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ :=
  (spectatorOutputStinespring σA ⊗ₖ spectatorOutputStinespring σB).submatrix
    (outputRegroup (Fin 2) (Fin 2) σA σB) id

/-- The fixed spectator state is a genuine unit vector. -/
def spectatorEnvironment [DecidableEq σA] [DecidableEq σB] (a0 : σA) (b0 : σB) :
    σA × σB → ℂ := fun e => if e = (a0, b0) then 1 else 0

theorem spectatorEnvironment_unit [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (a0 : σA) (b0 : σB) :
    IsUnitVector (spectatorEnvironment a0 b0) := by
  simp [IsUnitVector, spectatorEnvironment]

/-- The spectator gate preserves the selected qubit input subspace exactly. -/
theorem spectatorControlledPhase_intertwines [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (θ : ℝ) (a0 : σA) (b0 : σB) :
    spectatorControlledPhase θ * (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0) =
      (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0) * controlledPhase θ := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩ ⟨k, l⟩
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    by_cases ha : a = a0 <;> by_cases hb : b = b0 <;>
    simp [spectatorControlledPhase, Matrix.diagonal_mul, controlledPhase, qubitCornerPhase,
      Matrix.mul_diagonal, Matrix.kroneckerMap_apply, spectatorInputIsometry,
      coordinateInclusionMatrix, Matrix.submatrix_apply, Matrix.one_apply,
      spectatorInputEmbedding_apply, Prod.mk.injEq, hi, hj, ha, hb]

/-- The actual output dilation sends the selected input to a fixed spectator environment. -/
theorem spectatorOutputRegrouped_mul_input [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (a0 : σA) (b0 : σB) :
    spectatorOutputRegrouped * (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0) =
      insertVector (Fin 2 × Fin 2) (spectatorEnvironment a0 b0) := by
  unfold spectatorOutputRegrouped spectatorOutputStinespring
  rw [Matrix.one_kronecker_one]
  have hrow := Matrix.submatrix_mul (1 : Matrix ((Fin 2 × σA) × (Fin 2 × σB))
      ((Fin 2 × σA) × (Fin 2 × σB)) ℂ)
    (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0)
    (outputRegroup (Fin 2) (Fin 2) σA σB) id id Function.bijective_id
  rw [Matrix.submatrix_id_id, Matrix.one_mul] at hrow
  rw [← hrow]
  ext ⟨⟨i, j⟩, ⟨a, b⟩⟩ ⟨k, l⟩
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    by_cases ha : a = a0 <;> by_cases hb : b = b0 <;>
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, outputRegroup_apply,
      spectatorInputIsometry, coordinateInclusionMatrix, spectatorInputEmbedding_apply,
      Matrix.one_apply, insertVector_apply, spectatorEnvironment, Prod.mk.injEq, hi, hj, ha, hb]

/-- The restricted ideal dilation is exactly a controlled phase with a fixed unit environment. -/
theorem spectatorControlledPhase_frozen_restriction [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (θ : ℝ) (a0 : σA) (b0 : σB) :
    spectatorOutputRegrouped *
        (spectatorControlledPhase θ * (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0)) =
      insertVector (Fin 2 × Fin 2) (spectatorEnvironment a0 b0) * controlledPhase θ := by
  rw [spectatorControlledPhase_intertwines, ← Matrix.mul_assoc,
    spectatorOutputRegrouped_mul_input]

/-- Genuine local output channels after the ideal gate and fixed spectator inputs
give the actual two-qubit controlled-phase channel on every input matrix. -/
theorem spectatorControlledPhase_restrictedChannel_eq [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (θ : ℝ) (a0 : σA) (b0 : σB) :
    (tensorChannels (channelOf (spectatorOutputStinespring σA))
      (channelOf (spectatorOutputStinespring σB))).comp
        ((adConj (spectatorControlledPhase θ)).comp
          (adConj (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0))) =
      adConj (controlledPhase θ) := by
  rw [tensorChannels_channelOf_regrouped, ← adConj_mul_eq_comp, ← channelOf_mul_eq_comp]
  change channelOf (spectatorOutputRegrouped *
    (spectatorControlledPhase θ * (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0))) = _
  rw [spectatorControlledPhase_frozen_restriction]
  exact channelOf_insertVector_mul (spectatorEnvironment_unit a0 b0) _

end NLQCLean
