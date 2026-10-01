import NLQCLean.Invariants.RectangularControlledPhase
import NLQCLean.Models.ClassicalCommunication.BranchChannels
import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Models.ForwardReindex
import NLQCLean.Models.UnitaryScore

/-!
# Actual trace-preserving decoding of selected two-level systems

An explicit injective basis map sends the selected levels to their original
qubit labels with a fixed environment, and sends all other levels to qubit
zero with distinct environment labels. Its inclusion matrix is an actual
Stinespring isometry. The resulting local channels are completely positive
and trace-preserving, and their tensor product exactly decodes an ideally
restricted rectangular diagonal gate. No protocol resource/error transfer
or diamond contractivity is asserted.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

/-- Selected input levels retain their label and share environment zero;
all other basis states go to qubit zero with their original environment label. -/
def twoLevelDecoderBasisMap {d : ℕ} (hd : 2 ≤ d) (j : Fin d) : Fin 2 × Fin d :=
  if hj : j.val < 2 then (⟨j.val, hj⟩, twoLevelEmbedding hd 0) else (0, j)

theorem twoLevelDecoderBasisMap_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (twoLevelDecoderBasisMap hd) := by
  intro j k h
  by_cases hj : j.val < 2 <;> by_cases hk : k.val < 2
  · have hfst := congrArg (fun p : Fin 2 × Fin d => p.1.val) h
    simp only [twoLevelDecoderBasisMap, dif_pos hj, dif_pos hk] at hfst
    exact Fin.ext hfst
  · have hsnd := congrArg (fun p : Fin 2 × Fin d => p.2.val) h
    simp only [twoLevelDecoderBasisMap, dif_pos hj, dif_neg hk] at hsnd
    have hzero : (twoLevelEmbedding hd (0 : Fin 2)).val = 0 := rfl
    rw [hzero] at hsnd
    omega
  · have hsnd := congrArg (fun p : Fin 2 × Fin d => p.2.val) h
    simp only [twoLevelDecoderBasisMap, dif_neg hj, dif_pos hk] at hsnd
    have hzero : (twoLevelEmbedding hd (0 : Fin 2)).val = 0 := rfl
    rw [hzero] at hsnd
    omega
  · have hsnd := congrArg Prod.snd h
    simpa only [twoLevelDecoderBasisMap, dif_neg hj, dif_neg hk] using hsnd

def twoLevelDecoderEmbedding {d : ℕ} (hd : 2 ≤ d) : Fin d ↪ Fin 2 × Fin d :=
  ⟨twoLevelDecoderBasisMap hd, twoLevelDecoderBasisMap_injective hd⟩

@[simp] theorem twoLevelDecoderBasisMap_twoLevel {d : ℕ} (hd : 2 ≤ d) (i : Fin 2) :
    twoLevelDecoderBasisMap hd (twoLevelEmbedding hd i) = (i, twoLevelEmbedding hd 0) := by
  unfold twoLevelDecoderBasisMap
  rw [dif_pos (show (twoLevelEmbedding hd i).val < 2 from i.isLt)]
  rfl

/-- The actual finite local Stinespring decoder, of the same output/environment
matrix form as a finite protocol's final local decoder. -/
def twoLevelDecoderStinespring {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin 2 × Fin d) (Fin d) ℂ := coordinateInclusionMatrix (twoLevelDecoderEmbedding hd)

theorem twoLevelDecoderStinespring_isometry {d : ℕ} (hd : 2 ≤ d) :
    IsIsometry (twoLevelDecoderStinespring hd) := coordinateInclusionMatrix_isometry _

def twoLevelDecoderChannel {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  channelOf (twoLevelDecoderStinespring hd)

/-- One actual finite Kraus instrument, not an assumed TP adjoint restriction. -/
def twoLevelDecoderInstrument {d : ℕ} (hd : 2 ≤ d) :
    FiniteKrausInstrument (Fin d) (Fin 2) Unit (Fin d) :=
  FiniteKrausInstrument.ofStinespring (twoLevelDecoderStinespring hd)
    (twoLevelDecoderStinespring_isometry hd)

theorem twoLevelDecoderChannel_completelyPositive {d : ℕ} (hd : 2 ≤ d) :
    CompletelyPositive (twoLevelDecoderChannel hd) := by
  simpa only [twoLevelDecoderInstrument, FiniteKrausInstrument.channel_ofStinespring,
    twoLevelDecoderChannel] using (twoLevelDecoderInstrument hd).channel_completelyPositive

/-- The actual local decoder preserves the trace of every original input matrix. -/
theorem twoLevelDecoderChannel_trace {d : ℕ} (hd : 2 ≤ d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (twoLevelDecoderChannel hd X).trace = X.trace := by
  simpa only [twoLevelDecoderInstrument, FiniteKrausInstrument.channel_ofStinespring,
    twoLevelDecoderChannel] using (twoLevelDecoderInstrument hd).trace_channel X

def twoLevelDecoderEnvironment {d : ℕ} (hd : 2 ≤ d) : Fin d → ℂ :=
  fun e => if e = twoLevelEmbedding hd 0 then 1 else 0

theorem twoLevelDecoderEnvironment_unit {d : ℕ} (hd : 2 ≤ d) :
    IsUnitVector (twoLevelDecoderEnvironment hd) := by
  simp [IsUnitVector, twoLevelDecoderEnvironment]

/-- On the selected input levels, the actual decoder is identity on the
qubit and inserts only its fixed unit environment. -/
theorem twoLevelDecoderStinespring_mul_embedding {d : ℕ} (hd : 2 ≤ d) :
    twoLevelDecoderStinespring hd * twoLevelIsometry hd =
      insertVector (Fin 2) (twoLevelDecoderEnvironment hd) := by
  change twoLevelDecoderStinespring hd *
    (1 : Matrix (Fin d) (Fin d) ℂ).submatrix (Equiv.refl (Fin d)) (twoLevelEmbedding hd) = _
  rw [Matrix.mul_submatrix_one]
  ext ⟨k, e⟩ i
  by_cases hk : k = i <;> by_cases he : e = twoLevelEmbedding hd 0 <;>
    simp [twoLevelDecoderStinespring, coordinateInclusionMatrix, twoLevelDecoderEmbedding,
      Matrix.submatrix_apply, Matrix.one_apply, insertVector_apply,
      twoLevelDecoderEnvironment, Prod.mk.injEq, hk, he]

/-- Applying a channel to an isometrically embedded input corresponds to
the actual product of its Stinespring matrices. No error estimate is involved. -/
theorem channelOf_mul_eq_comp {ι κ ε τ : Type*}
    [Fintype ι] [Fintype ε] [Fintype τ]
    (F : Matrix (κ × ε) ι ℂ) (A : Matrix ι τ ℂ) :
    channelOf (F * A) = (channelOf F).comp (adConj A) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, channelOf_apply, adConj_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem twoLevelDecoderChannel_comp_embedding {d : ℕ} (hd : 2 ≤ d) :
    (twoLevelDecoderChannel hd).comp (adConj (twoLevelIsometry hd)) =
      adConj (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [twoLevelDecoderChannel, ← channelOf_mul_eq_comp,
    twoLevelDecoderStinespring_mul_embedding]
  simpa only [Matrix.mul_one] using
    channelOf_insertVector_mul (twoLevelDecoderEnvironment_unit hd)
      (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Tensoring actual local Stinespring channels discards both actual private
environments after the explicit system/environment regrouping. -/
theorem tensorChannels_channelOf_regrouped
    {ιA ιB κA κB εA εB : Type*}
    [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB]
    [DecidableEq ιA] [DecidableEq ιB]
    (FA : Matrix (κA × εA) ιA ℂ) (FB : Matrix (κB × εB) ιB ℂ) :
    tensorChannels (channelOf FA) (channelOf FB) =
      channelOf ((FA ⊗ₖ FB).submatrix (outputRegroup κA κB εA εB) id) := by
  simp only [channelOf_eq_sum_adConj, tensorChannels_sum_left, tensorChannels_sum_right,
    tensorChannels_adConj, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eA _
  apply Finset.sum_congr rfl
  intro eB _
  apply congrArg adConj
  ext i j
  rfl

def rectangularTwoLevelDecoderStinespring {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    Matrix ((Fin 2 × Fin 2) × (Fin dA × Fin dB)) (Fin dA × Fin dB) ℂ :=
  (twoLevelDecoderStinespring hA ⊗ₖ twoLevelDecoderStinespring hB).submatrix
    (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB)) id

theorem rectangularTwoLevelDecoderStinespring_isometry {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    IsIsometry (rectangularTwoLevelDecoderStinespring hA hB) :=
  ((twoLevelDecoderStinespring_isometry hA).kronecker
    (twoLevelDecoderStinespring_isometry hB)).submatrix_equiv
      (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB)) (Equiv.refl (Fin dA × Fin dB))

def rectangularTwoLevelDecoderChannel {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensorChannels (twoLevelDecoderChannel hA) (twoLevelDecoderChannel hB)

theorem rectangularTwoLevelDecoderChannel_eq_channelOf {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    rectangularTwoLevelDecoderChannel hA hB =
      channelOf (rectangularTwoLevelDecoderStinespring hA hB) :=
  tensorChannels_channelOf_regrouped _ _

theorem rectangularTwoLevelDecoderChannel_completelyPositive {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    CompletelyPositive (rectangularTwoLevelDecoderChannel hA hB) := by
  rw [rectangularTwoLevelDecoderChannel_eq_channelOf]
  simpa only [FiniteKrausInstrument.channel_ofStinespring] using
    (FiniteKrausInstrument.ofStinespring (rectangularTwoLevelDecoderStinespring hA hB)
      (rectangularTwoLevelDecoderStinespring_isometry hA hB)).channel_completelyPositive

theorem rectangularTwoLevelDecoderChannel_trace {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    (rectangularTwoLevelDecoderChannel hA hB X).trace = X.trace := by
  rw [rectangularTwoLevelDecoderChannel_eq_channelOf]
  simpa only [FiniteKrausInstrument.channel_ofStinespring] using
    (FiniteKrausInstrument.ofStinespring (rectangularTwoLevelDecoderStinespring hA hB)
      (rectangularTwoLevelDecoderStinespring_isometry hA hB)).trace_channel X

def rectangularTwoLevelDecoderEnvironment {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    Fin dA × Fin dB → ℂ :=
  fun e => if e = (twoLevelEmbedding hA 0, twoLevelEmbedding hB 0) then 1 else 0

theorem rectangularTwoLevelDecoderEnvironment_unit {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    IsUnitVector (rectangularTwoLevelDecoderEnvironment hA hB) := by
  simp [IsUnitVector, rectangularTwoLevelDecoderEnvironment]

theorem rectangularTwoLevelDecoderStinespring_mul_embedding {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    rectangularTwoLevelDecoderStinespring hA hB * rectangularTwoLevelIsometry hA hB =
      insertVector (Fin 2 × Fin 2) (rectangularTwoLevelDecoderEnvironment hA hB) := by
  unfold rectangularTwoLevelDecoderStinespring rectangularTwoLevelIsometry
  have hrow := Matrix.submatrix_mul
    (twoLevelDecoderStinespring hA ⊗ₖ twoLevelDecoderStinespring hB)
    (twoLevelIsometry hA ⊗ₖ twoLevelIsometry hB)
    (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB)) id id Function.bijective_id
  rw [Matrix.submatrix_id_id] at hrow
  rw [← hrow]
  rw [← Matrix.mul_kronecker_mul, twoLevelDecoderStinespring_mul_embedding,
    twoLevelDecoderStinespring_mul_embedding]
  ext p i
  by_cases hAq : p.1.1 = i.1 <;> by_cases hBq : p.1.2 = i.2 <;>
    by_cases hAe : p.2.1 = twoLevelEmbedding hA 0 <;>
    by_cases hBe : p.2.2 = twoLevelEmbedding hB 0 <;>
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, outputRegroup_apply,
      insertVector_apply, twoLevelDecoderEnvironment, rectangularTwoLevelDecoderEnvironment,
      Prod.ext_iff, hAq, hBq, hAe, hBe]

/-- Actual local TP decoding after the ideal rectangular gate and the actual
local input embeddings gives exactly its selected two-qubit diagonal channel. -/
theorem rectangularTwoLevelDecoderChannel_ideal_restriction {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    (rectangularTwoLevelDecoderChannel hA hB).comp
      ((adConj (rectangularDiagonalPhase θ)).comp (adConj (rectangularTwoLevelIsometry hA hB))) =
      adConj (diagonalPhaseMatrix (restrictedRectangularAngles hA hB θ)) := by
  rw [rectangularTwoLevelDecoderChannel_eq_channelOf, ← adConj_mul_eq_comp,
    ← channelOf_mul_eq_comp, rectangularDiagonalPhase_intertwines]
  rw [← Matrix.mul_assoc, rectangularTwoLevelDecoderStinespring_mul_embedding]
  exact channelOf_insertVector_mul (rectangularTwoLevelDecoderEnvironment_unit hA hB) _

end NLQCLean.ClassicalCommunication
