import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder
import NLQCLean.Models.StinespringDiamondContractivity

/-!
# Physical restriction of rectangular diagonal channels

The selected two-level input embeddings and the actual trace-preserving
output decoders are followed by explicit local diagonal corrections.
Their ideal action is exactly the controlled phase at the alternating
four-entry angle. Normalized diamond error contracts under these genuine
physical maps, on arbitrary original linear channels. No preservation of
protocol resource or message registers is asserted by this channel theorem.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

/-- A norm-one scalar does not change the conjugation channel. -/
theorem adConj_smul_of_normSq_eq_one {ι κ : Type*} [Fintype ι]
    (c : ℂ) (hc : Complex.normSq c = 1) (A : Matrix κ ι ℂ) :
    adConj (c • A) = adConj A := by
  have hc' : star c * c = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, hc]
    norm_num
  apply LinearMap.ext
  intro X
  simp only [adConj_apply, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hc', one_smul]

/-- The environment slices after a genuine output matrix are actual products. -/
theorem sliceAt_tensor_output_mul {ι κ ν ε : Type*}
    [Fintype κ] [Fintype ε] [DecidableEq ε]
    (L : Matrix ν κ ℂ) (F : Matrix (κ × ε) ι ℂ) (e : ε) :
    sliceAt ((L ⊗ₖ (1 : Matrix ε ε ℂ)) * F) e = L * sliceAt F e := by
  ext k i
  simp [sliceAt_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Output conjugation is implemented by multiplying the actual Stinespring
matrix, with identity on its original private environment. -/
theorem channelOf_tensor_output_mul {ι κ ν ε : Type*}
    [Fintype ι] [Fintype κ] [Fintype ε] [DecidableEq ε]
    (L : Matrix ν κ ℂ) (F : Matrix (κ × ε) ι ℂ) :
    channelOf ((L ⊗ₖ (1 : Matrix ε ε ℂ)) * F) =
      (adConj L).comp (channelOf F) := by
  rw [channelOf_eq_sum_adConj, channelOf_eq_sum_adConj]
  apply LinearMap.ext
  intro X
  simp only [LinearMap.sum_apply, sliceAt_tensor_output_mul,
    adConj_mul_eq_comp, LinearMap.comp_apply, map_sum]

/-- Regrouping the two laboratories turns their local output matrices and
environment identities into the genuine joint output matrix and identity. -/
theorem outputRegroup_local_tensor_identity {κA κB εA εB : Type*}
    [DecidableEq εA] [DecidableEq εB]
    (LA : Matrix κA κA ℂ) (LB : Matrix κB κB ℂ) :
    ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) ⊗ₖ (LB ⊗ₖ (1 : Matrix εB εB ℂ))).submatrix
        (outputRegroup κA κB εA εB) (outputRegroup κA κB εA εB) =
      (LA ⊗ₖ LB) ⊗ₖ (1 : Matrix (εA × εB) (εA × εB) ℂ) := by
  ext p q
  by_cases hA : p.2.1 = q.2.1 <;> by_cases hB : p.2.2 = q.2.2 <;>
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, outputRegroup_apply,
      Matrix.one_apply, Prod.ext_iff, hA, hB, mul_comm]

/-- A local correction is applied to the decoded qubit, not to the environment. -/
def correctedTwoLevelDecoderStinespring {d : ℕ} (hd : 2 ≤ d)
    (L : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin d) (Fin d) ℂ :=
  (L ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * twoLevelDecoderStinespring hd

theorem correctedTwoLevelDecoderStinespring_isometry {d : ℕ} (hd : 2 ≤ d)
    {L : Matrix (Fin 2) (Fin 2) ℂ} (hL : IsIsometry L) :
    IsIsometry (correctedTwoLevelDecoderStinespring hd L) :=
  (hL.kronecker isIsometry_one).mul (twoLevelDecoderStinespring_isometry hd)

def correctedTwoLevelDecoderChannel {d : ℕ} (hd : 2 ≤ d)
    (L : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  channelOf (correctedTwoLevelDecoderStinespring hd L)

theorem correctedTwoLevelDecoderChannel_completelyPositive {d : ℕ} (hd : 2 ≤ d)
    {L : Matrix (Fin 2) (Fin 2) ℂ} (hL : IsIsometry L) :
    CompletelyPositive (correctedTwoLevelDecoderChannel hd L) := by
  simpa only [FiniteKrausInstrument.channel_ofStinespring, correctedTwoLevelDecoderChannel]
    using (FiniteKrausInstrument.ofStinespring (correctedTwoLevelDecoderStinespring hd L)
      (correctedTwoLevelDecoderStinespring_isometry hd hL)).channel_completelyPositive

theorem correctedTwoLevelDecoderChannel_trace {d : ℕ} (hd : 2 ≤ d)
    {L : Matrix (Fin 2) (Fin 2) ℂ} (hL : IsIsometry L)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (correctedTwoLevelDecoderChannel hd L X).trace = X.trace := by
  simpa only [FiniteKrausInstrument.channel_ofStinespring, correctedTwoLevelDecoderChannel]
    using (FiniteKrausInstrument.ofStinespring (correctedTwoLevelDecoderStinespring hd L)
      (correctedTwoLevelDecoderStinespring_isometry hd hL)).trace_channel X

noncomputable def rectangularDiagonalDecoderA {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    Matrix (Fin 2 × Fin dA) (Fin dA) ℂ :=
  correctedTwoLevelDecoderStinespring hA
    (qubitPhaseCorrectionA (restrictedRectangularAngles hA hB θ))

noncomputable def rectangularDiagonalDecoderB {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    Matrix (Fin 2 × Fin dB) (Fin dB) ℂ :=
  correctedTwoLevelDecoderStinespring hB
    (qubitPhaseCorrectionB (restrictedRectangularAngles hA hB θ))

theorem rectangularDiagonalDecoderA_isometry {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    IsIsometry (rectangularDiagonalDecoderA hA hB θ) :=
  correctedTwoLevelDecoderStinespring_isometry hA (qubitPhaseCorrectionA_unitary _).1

theorem rectangularDiagonalDecoderB_isometry {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    IsIsometry (rectangularDiagonalDecoderB hA hB θ) :=
  correctedTwoLevelDecoderStinespring_isometry hB (qubitPhaseCorrectionB_unitary _).1

/-- The corrected joint decoder retains both original private environments. -/
noncomputable def rectangularDiagonalDecoderStinespring {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    Matrix ((Fin 2 × Fin 2) × (Fin dA × Fin dB)) (Fin dA × Fin dB) ℂ :=
  ((qubitPhaseCorrectionA (restrictedRectangularAngles hA hB θ) ⊗ₖ
      qubitPhaseCorrectionB (restrictedRectangularAngles hA hB θ)) ⊗ₖ
    (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)) *
      rectangularTwoLevelDecoderStinespring hA hB

theorem rectangularDiagonalDecoderStinespring_isometry {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    IsIsometry (rectangularDiagonalDecoderStinespring hA hB θ) := by
  have hLA : IsIsometry (qubitPhaseCorrectionA (restrictedRectangularAngles hA hB θ)) :=
    (qubitPhaseCorrectionA_unitary _).1
  have hLB : IsIsometry (qubitPhaseCorrectionB (restrictedRectangularAngles hA hB θ)) :=
    (qubitPhaseCorrectionB_unitary _).1
  exact ((hLA.kronecker hLB).kronecker isIsometry_one).mul
    (rectangularTwoLevelDecoderStinespring_isometry hA hB)

/-- This joint dilation is exactly the tensor product of the two genuine local
corrected decoders, with only the system/environment order changed. -/
theorem rectangularDiagonalDecoderStinespring_eq_local_tensor {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    (rectangularDiagonalDecoderA hA hB θ ⊗ₖ rectangularDiagonalDecoderB hA hB θ).submatrix
        (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB)) id =
      rectangularDiagonalDecoderStinespring hA hB θ := by
  unfold rectangularDiagonalDecoderA rectangularDiagonalDecoderB
    correctedTwoLevelDecoderStinespring rectangularDiagonalDecoderStinespring
    rectangularTwoLevelDecoderStinespring
  rw [Matrix.mul_kronecker_mul]
  rw [← Matrix.submatrix_mul_equiv _ _
    (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB))
    (outputRegroup (Fin 2) (Fin 2) (Fin dA) (Fin dB)) id]
  rw [outputRegroup_local_tensor_identity]

noncomputable def rectangularDiagonalDecoderChannel {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  channelOf (rectangularDiagonalDecoderStinespring hA hB θ)

theorem rectangularDiagonalDecoderChannel_eq_local_tensor {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    rectangularDiagonalDecoderChannel hA hB θ =
      tensorChannels (channelOf (rectangularDiagonalDecoderA hA hB θ))
        (channelOf (rectangularDiagonalDecoderB hA hB θ)) := by
  rw [tensorChannels_channelOf_regrouped,
    rectangularDiagonalDecoderStinespring_eq_local_tensor]
  rfl

theorem rectangularDiagonalDecoderChannel_completelyPositive {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    CompletelyPositive (rectangularDiagonalDecoderChannel hA hB θ) := by
  simpa only [FiniteKrausInstrument.channel_ofStinespring, rectangularDiagonalDecoderChannel]
    using (FiniteKrausInstrument.ofStinespring (rectangularDiagonalDecoderStinespring hA hB θ)
      (rectangularDiagonalDecoderStinespring_isometry hA hB θ)).channel_completelyPositive

theorem rectangularDiagonalDecoderChannel_trace {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    (rectangularDiagonalDecoderChannel hA hB θ X).trace = X.trace := by
  simpa only [FiniteKrausInstrument.channel_ofStinespring, rectangularDiagonalDecoderChannel]
    using (FiniteKrausInstrument.ofStinespring (rectangularDiagonalDecoderStinespring hA hB θ)
      (rectangularDiagonalDecoderStinespring_isometry hA hB θ)).trace_channel X

theorem rectangularDiagonalDecoderChannel_eq_comp {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    rectangularDiagonalDecoderChannel hA hB θ =
      (adConj (qubitPhaseCorrectionA (restrictedRectangularAngles hA hB θ) ⊗ₖ
        qubitPhaseCorrectionB (restrictedRectangularAngles hA hB θ))).comp
          (rectangularTwoLevelDecoderChannel hA hB) := by
  rw [rectangularDiagonalDecoderChannel, rectangularDiagonalDecoderStinespring,
    channelOf_tensor_output_mul, rectangularTwoLevelDecoderChannel_eq_channelOf]

/-- A global unit scalar leaves the conjugation channel unchanged. -/
theorem qubitDiagonalPhase_corrected_channel (φ : Fin 2 × Fin 2 → ℝ) :
    (adConj (qubitPhaseCorrectionA φ ⊗ₖ qubitPhaseCorrectionB φ)).comp
        (adConj (diagonalPhaseMatrix φ)) = adConj (controlledPhase (qubitAlternatingAngle φ)) := by
  rw [← adConj_mul_eq_comp, ← qubitDiagonalPhase_local_reduction]
  exact (adConj_smul_of_normSq_eq_one _ (normSq_qubitGlobalPhaseCorrection φ) _).symm

/-- Restrict an arbitrary original channel by genuine local input and output maps. -/
noncomputable def rectangularDiagonalRestrictedChannel {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)
    (Φ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (rectangularDiagonalDecoderChannel hA hB θ).comp
    (Φ.comp (adConj (rectangularTwoLevelIsometry hA hB)))

/-- The corrected physical restriction of the ideal rectangular diagonal
channel is the controlled phase at its exact alternating four-entry angle. -/
theorem rectangularDiagonalRestrictedChannel_ideal {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    rectangularDiagonalRestrictedChannel hA hB θ (adConj (rectangularDiagonalPhase θ)) =
      adConj (controlledPhase (rectangularAlternatingAngle hA hB θ)) := by
  rw [rectangularDiagonalRestrictedChannel, rectangularDiagonalDecoderChannel_eq_comp,
    LinearMap.comp_assoc, rectangularTwoLevelDecoderChannel_ideal_restriction]
  exact qubitDiagonalPhase_corrected_channel _

/-- Genuine local restriction contracts the original normalized diamond error
for arbitrary original linear maps, including differences of physical channels. -/
theorem diamondError_rectangularDiagonalRestrictedChannel_le {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)
    (Φ Ψ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    diamondError (rectangularDiagonalRestrictedChannel hA hB θ Φ)
        (rectangularDiagonalRestrictedChannel hA hB θ Ψ) ≤ diamondError Φ Ψ :=
  diamondError_stinespring_isometry_sandwich_le Φ Ψ
    (rectangularTwoLevelIsometry_isometry hA hB)
    (rectangularDiagonalDecoderStinespring_isometry hA hB θ)

/-- In particular, approximation to the original rectangular target transfers
to approximation to the controlled phase with unchanged normalized error. -/
theorem diamondError_rectangularDiagonalRestrictedChannel_target_le {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)
    (Φ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    diamondError (rectangularDiagonalRestrictedChannel hA hB θ Φ)
      (adConj (controlledPhase (rectangularAlternatingAngle hA hB θ))) ≤
        diamondError Φ (adConj (rectangularDiagonalPhase θ)) := by
  rw [← rectangularDiagonalRestrictedChannel_ideal hA hB θ]
  exact diamondError_rectangularDiagonalRestrictedChannel_le hA hB θ Φ _

end NLQCLean.ClassicalCommunication
