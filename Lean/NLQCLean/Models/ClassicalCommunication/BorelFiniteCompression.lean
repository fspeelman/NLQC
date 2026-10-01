import NLQCLean.Models.ClassicalCommunication.BorelOperationalChannel
import NLQCLean.Models.ClassicalCommunication.SequentialDensityCompression
import NLQCLean.Models.ClassicalCommunication.BranchChannels
import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder

/-!
# Actual finite protocols from original Borel instruments

Sequential selection is instantiated on the original CP-valued instruments.
Only finitely many final CP/TP operations are given Kraus realizations, at
their original selected outcome pairs. The resulting finite protocol keeps
the actual resource and both quantum messages and preserves a genuine target
score. The alphabet caps here use the original input dimensions; replacing
ambient resource dimensions by rank needs a separate input-support bridge.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Matrix.Norms.Elementwise Kronecker

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance finiteBorelMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance finiteBorelMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (finiteBorelMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance borel_finite_compression_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance borel_finite_compression_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

section ActualDilation

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [Nonempty ι]
variable (Γ : MatrixOperation ι κ) (hCP : CompletelyPositive Γ.toLinearMap)
variable (hTP : ∀ X, (Γ X).trace = X.trace)

/-- A final actual CP/TP operation has a genuine one-outcome Kraus instrument. -/
def operationInstrument : FiniteKrausInstrument ι κ Unit (κ × ι) :=
  (exists_instrument_of_completelyPositive_branches (fun _ : Unit => Γ.toLinearMap)
    (fun _ => hCP) (fun X => by simpa using hTP X)).choose

theorem operationInstrument_branch (u : Unit) :
    (operationInstrument Γ hCP hTP).branch u = Γ.toLinearMap :=
  (exists_instrument_of_completelyPositive_branches (fun _ : Unit => Γ.toLinearMap)
    (fun _ => hCP) (fun X => by simpa using hTP X)).choose_spec u

/-- Actual finite Stinespring dilation; it is used only at selected points. -/
def operationStinespring : Matrix (κ × (Unit × (κ × ι))) ι ℂ :=
  (operationInstrument Γ hCP hTP).dilation

theorem operationStinespring_isometry : IsIsometry (operationStinespring Γ hCP hTP) :=
  (operationInstrument Γ hCP hTP).dilation_isometry

theorem channelOf_operationStinespring :
    channelOf (operationStinespring Γ hCP hTP) = Γ.toLinearMap := by
  rw [operationStinespring, ← FiniteKrausInstrument.channel_eq_channelOf_dilation]
  simp only [FiniteKrausInstrument.channel, Fintype.sum_unique, operationInstrument_branch]

end ActualDilation

section BranchDecoderSemantics

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

omit [Fintype ιA'] [Fintype ιB'] in
/-- The existing finite Kraus branch channel has exactly the genuine
tensor final-channel, exchange, tensor operation and resource semantics. -/
theorem branchChannel_eq_decoder_composition
    (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    branchChannel γ DA DB Φ Ψ =
      ((tensorChannels (channelOf DA) (channelOf DB)).comp
        (adConj (exchangeMatrix κA μA κB μB))).comp
          ((tensorChannels Φ Ψ).comp (adConj (insertResource ιA ιB γ))) := by
  have hrow : exchangedDecoder DA DB =
      (DA ⊗ₖ DB).submatrix (outputRegroup ιA' ιB' εA εB) id *
        exchangeMatrix κA μA κB μB := by
    rw [exchangedDecoder, Matrix.submatrix_mul _ _ _ id id Function.bijective_id,
      Matrix.submatrix_id_id]
  have hdec : (ptraceB (ιA' × ιB') (εA × εB)).comp
      (adConj (exchangedDecoder DA DB)) =
        (tensorChannels (channelOf DA) (channelOf DB)).comp
          (adConj (exchangeMatrix κA μA κB μB)) := by
    change channelOf (exchangedDecoder DA DB) = _
    rw [hrow, channelOf_mul_eq_comp, ← tensorChannels_channelOf_regrouped]
  rw [branchChannel, branchChannelSandwich, channelSandwichLinear_apply, hdec]

end BranchDecoderSemantics

namespace StandardBorelClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable [Nonempty ιA] [Nonempty ιB]
variable (P : StandardBorelClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')

/-- Sequential compression yields an actual finite protocol on the same
quantum systems with exactly the original resource and target score.
Only classical outcomes and private dilation labels change. -/
theorem exists_finite_protocol_preserving_linearScore
    (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ) :
    ∃ nA : ℕ, nA ≤ Fintype.card (ιA × ρA) ^ 2 + 1 ∧
      ∃ nB : ℕ, nB ≤ Fintype.card (ιB × ρB) ^ 2 + 1 ∧
        ∃ Q : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB (Fin nA) (Fin nB)
          ((κA × μA) × (ιA × ρA)) ((κB × μB) × (ιB × ρB))
          ιA' ιB' (Unit × (ιA' × (κA × μB))) (Unit × (ιB' × (κB × μA))),
          Q.resource = P.resource ∧
          (∀ K, Q.HasQuantumFootprint K ↔ P.HasQuantumFootprint K) ∧
          S Q.operationalChannel = S P.operationalChannel.toLinearMap := by
  classical
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  have hout := P.instrument_outputs_nonempty
  let : Nonempty κA := hout.1.map Prod.fst
  let : Nonempty μA := hout.1.map Prod.snd
  let : Nonempty κB := hout.2.map Prod.fst
  let : Nonempty μB := hout.2.map Prod.snd
  obtain ⟨nA, hnA, nB, hnB, selectA, selectB, weightA, weightB,
      _, _, _, _, JA, JB, hJA, hJB, hscore⟩ :=
    exists_sequential_score_preserving_density_instruments
      P.instrumentA P.instrumentB P.densityA P.densityB
      P.densityA_spec.1 P.densityB_spec.1 P.densityA_spec.2.1 P.densityB_spec.2.1
      P.densityA_spec.2.2.1 P.densityB_spec.2.2.1
      (continuousMatrixOperationRealScore S) P.resourceInsertion P.jointDecoder
      P.measurable_jointDecoder P.jointDecoder_completelyPositive P.jointDecoder_tracePreserving
  let Q : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB (Fin nA) (Fin nB)
      ((κA × μA) × (ιA × ρA)) ((κB × μB) × (ιB × ρB))
      ιA' ιB' (Unit × (ιA' × (κA × μB))) (Unit × (ιB' × (κB × μA))) := {
    resource := P.resource
    resource_unit := P.resource_unit
    instrumentA := JA
    instrumentB := JB
    decA := fun j k => operationStinespring (P.decA (selectA j, selectB k))
      (P.decA_completelyPositive _) (P.decA_tracePreserving _)
    decB := fun j k => operationStinespring (P.decB (selectA j, selectB k))
      (P.decB_completelyPositive _) (P.decB_tracePreserving _)
    decA_isometry := fun j k => operationStinespring_isometry _ _ _
    decB_isometry := fun j k => operationStinespring_isometry _ _ _ }
  refine ⟨nA, hnA, nB, hnB, Q, rfl, (fun _ => Iff.rfl), ?_⟩
  have hscore' : (∫ z, P.jointScore (continuousMatrixOperationRealScore S) z
      ∂P.probabilityA.prod P.probabilityB) =
      ∑ j, ∑ k, continuousMatrixOperationRealScore S
        (decodedTensorChannel (P.jointDecoder (selectA j, selectB k)) P.resourceInsertion
          (weightA j • P.densityA (selectA j)) (weightB k • P.densityB (selectB k))) :=
    hscore
  rw [P.linearScore_operationalChannel S, hscore']
  rw [Q.operationalChannel_eq_sum_outcomeChannel]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [continuousMatrixOperationRealScore_apply]
  unfold FiniteClassicalProtocol.outcomeChannel
  rw [branchChannel_eq_decoder_composition]
  change S (((tensorChannels
    (channelOf (operationStinespring (P.decA (selectA j, selectB k))
      (P.decA_completelyPositive _) (P.decA_tracePreserving _)))
    (channelOf (operationStinespring (P.decB (selectA j, selectB k))
      (P.decB_completelyPositive _) (P.decB_tracePreserving _)))).comp
      (adConj (exchangeMatrix κA μA κB μB))).comp
        ((tensorChannels (JA.branch j) (JB.branch k)).comp
          (adConj (insertResource ιA ιB P.resource)))) = _
  rw [channelOf_operationStinespring, channelOf_operationStinespring, hJA, hJB]
  rfl

end StandardBorelClassicalProtocol

end

end NLQCLean.ClassicalCommunication
