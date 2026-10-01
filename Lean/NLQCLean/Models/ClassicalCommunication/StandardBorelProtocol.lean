import NLQCLean.Models.ClassicalCommunication.JointDensityChannels
import NLQCLean.Models.ClassicalCommunication.FiniteProtocol
import NLQCLean.Models.StinespringDiamondContractivity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Actual standard-Borel simultaneous classical protocols

Local instruments are original countably additive CP-operation vector
measures, not assumed densities. Final local CP/TP channel families have
jointly Borel unnormalized Choi matrices. Measurability of the actual channel
families follows from the proved continuous Choi inverse. Original resource,
kept systems and both finite quantum messages remain explicit.
No score integrability, compression theorem or shared-randomness bridge is
a field of this model.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Kronecker Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance borelProtocolMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := jointMatrixNormedAddCommGroup

noncomputable local instance borelProtocolMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  jointMatrixTopologicalSpace

noncomputable local instance standard_borel_protocol_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance standard_borel_protocol_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

local instance standard_borel_protocol_instance_3 {ν : Type*} [Fintype ν] : MeasurableSpace (Matrix ν ν ℂ) :=
  borel (Matrix ν ν ℂ)

local instance standard_borel_protocol_instance_4 {ν : Type*} [Fintype ν] : BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance standard_borel_protocol_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance standard_borel_protocol_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

private theorem borel_matrix_eq_pi (ν : Type*) [Fintype ν] :
    borel (Matrix ν ν ℂ) =
      @MeasurableSpace.pi ν (fun _ => ν → ℂ) (fun _ => MeasurableSpace.pi) :=
  (Pi.borelSpace (ι := ν) (X := fun _ => ν → ℂ)).measurable_eq.symm

/-- Genuine finite-matrix Borel measurability is equivalent to entrywise
measurability; this explicitly bridges the matrix and finite-Pi presentations. -/
theorem measurable_matrix_iff_entry {α ν : Type*}
    [MeasurableSpace α] [Fintype ν] (f : α → Matrix ν ν ℂ) :
    Measurable f ↔ ∀ i j, Measurable (fun a => f a i j) := by
  change @Measurable α (Matrix ν ν ℂ) _ (borel (Matrix ν ν ℂ)) f ↔ _
  rw [borel_matrix_eq_pi]
  exact measurable_pi_iff.trans (forall_congr' fun _ => measurable_pi_iff)

/-- Joint Choi measurability is equivalent to genuine operation
measurability, by the actual continuous coefficient inverse. -/
theorem measurable_unnormalizedChoi_iff {α ι κ : Type*}
    [MeasurableSpace α] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Φ : α → MatrixOperation ι κ) :
    Measurable (fun a => unnormalizedChoiMatrix (Φ a).toLinearMap) ↔ Measurable Φ := by
  let L := unnormalizedChoiContinuousRealLinearEquiv (ι := ι) (κ := κ)
  constructor
  · intro hC
    have h := L.symm.continuous.measurable.comp hC
    change Measurable (fun a => L.symm (unnormalizedChoiMatrix (Φ a).toLinearMap)) at h
    have heq : (fun a => L.symm (unnormalizedChoiMatrix (Φ a).toLinearMap)) = Φ := by
      funext a
      exact channelFromUnnormalizedChoi_unnormalizedChoi (Φ a)
    rw [heq] at h
    exact h
  · intro hΦ
    exact L.continuous.measurable.comp hΦ

/-- Actual finite-ancilla complete positivity is preserved by composition. -/
theorem CompletelyPositive.comp {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    {Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ν ν ℂ}
    (hΨ : CompletelyPositive Ψ) (hΦ : CompletelyPositive Φ) :
    CompletelyPositive (Ψ.comp Φ) := by
  intro n X hX
  rw [amplify_comp]
  exact hΨ n _ (hΦ n _ hX)

/-- The actual tensor operation preserves trace when both local operations do. -/
theorem tensorContinuousChannels_tracePreserving {ι κ τ υ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
    [DecidableEq ι] [DecidableEq τ]
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ)
    (hΦ : ∀ X, (Φ X).trace = X.trace) (hΨ : ∀ X, (Ψ X).trace = X.trace)
    (X : Matrix (ι × τ) (ι × τ) ℂ) :
    (tensorContinuousChannels Φ Ψ X).trace = X.trace := by
  change (tensorChannels Φ.toLinearMap Ψ.toLinearMap X).trace = _
  simp only [tensorChannels_apply, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.trace_kronecker]
  change (∑ i, ∑ j, ∑ p, ∑ q, X (i, p) (j, q) *
    ((Φ (Matrix.single i j 1)).trace * (Ψ (Matrix.single p q 1)).trace)) = _
  simp only [hΦ, hΨ]
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Fintype.sum_prod_type]

/-- An actual trace-preserving operation from a nonzero input cannot have
an empty output system. -/
theorem tracePreserving_output_nonempty {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (Φ : MatrixOperation ι κ) (hΦ : ∀ X, (Φ X).trace = X.trace) :
    Nonempty κ := by
  classical
  by_contra h
  let : IsEmpty κ := not_nonempty_iff.mp h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have ht := hΦ (Matrix.single i i 1)
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply] at ht

/-- An instrument's trace-preserving total operation already forces a
nonempty output whenever its original input is nonempty. -/
theorem CPVectorInstrument.output_nonempty {α ι κ : Type*}
    [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (I : CPVectorInstrument α ι κ) : Nonempty κ :=
  tracePreserving_output_nonempty (I.operationMeasure univ) I.tracePreserving_total

/-- Rectangular isometric conjugation preserves the trace of every matrix. -/
theorem trace_adConj_isometry {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    {E : Matrix κ ι ℂ} (hE : IsIsometry E) (X : Matrix ι ι ℂ) :
    (adConj E X).trace = X.trace := by
  rw [adConj_apply, Matrix.trace_mul_cycle, hE.conjTranspose_mul_self, Matrix.one_mul]

/-- Tensoring actual operations is continuous in both operation slots. -/
theorem continuous_tensorContinuousChannels {ι κ τ υ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
    [DecidableEq ι] [DecidableEq τ]
    : Continuous (fun p : MatrixOperation ι κ × MatrixOperation τ υ =>
      tensorContinuousChannels p.1 p.2) :=
  ((tensorContinuousChannelsBilinear (ι := ι) (κ := κ) (τ := τ) (υ := υ)).continuous.comp
    continuous_fst).clm_apply continuous_snd

/-- Fixed input precomposition is continuous on actual operations. -/
theorem continuous_operation_precomposition {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (R : MatrixOperation ν ι) :
    Continuous (fun T : MatrixOperation ι κ => T.comp R) :=
  continuous_id.clm_comp_const R

/-- Genuine measurable tensor channels remain measurable after fixed
continuous input precomposition. -/
theorem measurable_tensorContinuousChannels_precompose {α ι κ τ υ ν : Type*}
    [MeasurableSpace α] [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ] [Fintype ν]
    [DecidableEq ι] [DecidableEq τ]
    (Φ : α → MatrixOperation ι κ) (Ψ : α → MatrixOperation τ υ)
    (R : MatrixOperation ν (ι × τ)) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    Measurable (fun a => (tensorContinuousChannels (Φ a) (Ψ a)).comp R) := by
  classical
  have hCΦ := (measurable_unnormalizedChoi_iff Φ).mpr hΦ
  have hCΨ := (measurable_unnormalizedChoi_iff Ψ).mpr hΨ
  apply (measurable_unnormalizedChoi_iff _).mp
  apply (measurable_matrix_iff_entry _).mpr
  intro p q
  change Measurable (fun a => tensorChannels (Φ a).toLinearMap (Ψ a).toLinearMap
    (R (Matrix.single p.2 q.2 1)) p.1 q.1)
  simp only [tensorChannels_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  have hF : Measurable (fun a => Φ a (Matrix.single i j 1) p.1.1 q.1.1) :=
    (measurable_matrix_iff_entry _).mp hCΦ (p.1.1, i) (q.1.1, j)
  have hG : Measurable (fun a => Ψ a (Matrix.single k l 1) p.1.2 q.1.2) :=
    (measurable_matrix_iff_entry _).mp hCΨ (p.1.2, k) (q.1.2, l)
  exact measurable_const.mul (hF.mul hG)

/-- The manuscript's standard-Borel local instruments and jointly Borel
final local channels on their actual original finite quantum systems. -/
structure StandardBorelClassicalProtocol
    (ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*)
    [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
    [Fintype ιA'] [Fintype ιB']
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
    [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
    [DecidableEq ιA'] [DecidableEq ιB']
    [MeasurableSpace σA] [MeasurableSpace σB]
    [StandardBorelSpace σA] [StandardBorelSpace σB] where
  resource : ρA × ρB → ℂ
  resource_unit : IsUnitVector resource
  instrumentA : CPVectorInstrument σA (ιA × ρA) (κA × μA)
  instrumentB : CPVectorInstrument σB (ιB × ρB) (κB × μB)
  decA : σA × σB → MatrixOperation (κA × μB) ιA'
  decB : σA × σB → MatrixOperation (κB × μA) ιB'
  decA_choiMeasurable : Measurable (fun z => unnormalizedChoiMatrix (decA z).toLinearMap)
  decB_choiMeasurable : Measurable (fun z => unnormalizedChoiMatrix (decB z).toLinearMap)
  decA_completelyPositive : ∀ z, CompletelyPositive (decA z).toLinearMap
  decB_completelyPositive : ∀ z, CompletelyPositive (decB z).toLinearMap
  decA_tracePreserving : ∀ z X, (decA z X).trace = X.trace
  decB_tracePreserving : ∀ z X, (decB z X).trace = X.trace

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
variable (P : StandardBorelClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')

/-- Classical outcomes and their label cardinalities are not charged. -/
def HasQuantumFootprint (K : ℕ) : Prop := HasFootprint K P.resource μA μB

include P in
/-- The actual unit resource, including empty-register endpoints, determines
nonempty resource systems. -/
theorem resource_nonempty : Nonempty (ρA × ρB) :=
  Fintype.card_pos_iff.mp P.resource_unit.card_pos

include P in
/-- Nonempty logical inputs and actual normalized instruments determine
nonempty kept/message output systems; this is not an extra protocol assumption. -/
theorem instrument_outputs_nonempty [Nonempty ιA] [Nonempty ιB] :
    Nonempty (κA × μA) ∧ Nonempty (κB × μB) := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  exact ⟨P.instrumentA.output_nonempty, P.instrumentB.output_nonempty⟩

/-- Alice's probability is normalized trace of her original operation measure. -/
def probabilityA [Nonempty ιA] : Measure σA := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  exact P.instrumentA.traceProbability

/-- Bob's probability is normalized trace of his original operation measure. -/
def probabilityB [Nonempty ιB] : Measure σB := by
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  exact P.instrumentB.traceProbability

instance probabilityA_isProbabilityMeasure [Nonempty ιA] :
    IsProbabilityMeasure P.probabilityA := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  change IsProbabilityMeasure P.instrumentA.traceProbability
  infer_instance

instance probabilityB_isProbabilityMeasure [Nonempty ιB] :
    IsProbabilityMeasure P.probabilityB := by
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  change IsProbabilityMeasure P.instrumentB.traceProbability
  infer_instance

/-- A measurable RN density of the original Alice instrument. -/
def densityA [Nonempty ιA] : σA → MatrixOperation (ιA × ρA) (κA × μA) := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  exact P.instrumentA.exists_positive_normalized_density.choose

/-- One actual measurable RN density of the original Bob instrument. -/
def densityB [Nonempty ιB] : σB → MatrixOperation (ιB × ρB) (κB × μB) := by
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  exact P.instrumentB.exists_positive_normalized_density.choose

/-- Alice's chosen density exactly reconstructs the actual instrument;
its Choi marginal is integrated identity, not pointwise trace preservation. -/
theorem densityA_spec [Nonempty ιA] :
    Measurable P.densityA ∧ Integrable P.densityA P.probabilityA ∧
      P.probabilityA.withDensityᵥ P.densityA = P.instrumentA.operationMeasure ∧
      (∀ᵐ x ∂P.probabilityA, CompletelyPositive (P.densityA x).toLinearMap ∧
        (unnormalizedChoiMatrix (P.densityA x).toLinearMap).trace =
          (Fintype.card (ιA × ρA) : ℂ)) ∧
      (∫ x, ptraceA (κA × μA) (ιA × ρA)
        (unnormalizedChoiMatrix (P.densityA x).toLinearMap) ∂P.probabilityA) = 1 := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  exact P.instrumentA.exists_positive_normalized_density.choose_spec

/-- Bob's chosen density has the same exact representation and integrated
normalization on his original input system. -/
theorem densityB_spec [Nonempty ιB] :
    Measurable P.densityB ∧ Integrable P.densityB P.probabilityB ∧
      P.probabilityB.withDensityᵥ P.densityB = P.instrumentB.operationMeasure ∧
      (∀ᵐ y ∂P.probabilityB, CompletelyPositive (P.densityB y).toLinearMap ∧
        (unnormalizedChoiMatrix (P.densityB y).toLinearMap).trace =
          (Fintype.card (ιB × ρB) : ℂ)) ∧
      (∫ y, ptraceA (κB × μB) (ιB × ρB)
        (unnormalizedChoiMatrix (P.densityB y).toLinearMap) ∂P.probabilityB) = 1 := by
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  exact P.instrumentB.exists_positive_normalized_density.choose_spec

theorem measurable_decA : Measurable P.decA :=
  (measurable_unnormalizedChoi_iff _).mp P.decA_choiMeasurable

theorem measurable_decB : Measurable P.decB :=
  (measurable_unnormalizedChoi_iff _).mp P.decB_choiMeasurable

/-- The actual fixed resource insertion operation before both local instruments. -/
def resourceInsertion : MatrixOperation (ιA × ιB) ((ιA × ρA) × (ιB × ρB)) :=
  (adConj (insertResource ιA ιB P.resource)).toContinuousLinearMap

/-- The actual final operation performs the canonical quantum-message
exchange and the two original outcome-dependent local channels. -/
def jointDecoder (z : σA × σB) :
    MatrixOperation ((κA × μA) × (κB × μB)) (ιA' × ιB') :=
  (tensorContinuousChannels (P.decA z) (P.decB z)).comp
    (adConj (exchangeMatrix κA μA κB μB)).toContinuousLinearMap

/-- Joint decoder measurability follows from the original two Choi-Borel
families and genuine continuous tensor/composition operations. -/
theorem measurable_jointDecoder : Measurable P.jointDecoder := by
  exact measurable_tensorContinuousChannels_precompose P.decA P.decB
    (adConj (exchangeMatrix κA μA κB μB)).toContinuousLinearMap
    P.measurable_decA P.measurable_decB

/-- The actual joint decoder is completely positive, including its fixed
message-exchange operation. Nonempty outputs are derived from the instruments. -/
theorem jointDecoder_completelyPositive [Nonempty ιA] [Nonempty ιB]
    (z : σA × σB) : CompletelyPositive (P.jointDecoder z).toLinearMap := by
  have hout := P.instrument_outputs_nonempty
  let : Nonempty κA := hout.1.map Prod.fst
  let : Nonempty μA := hout.1.map Prod.snd
  let : Nonempty κB := hout.2.map Prod.fst
  let : Nonempty μB := hout.2.map Prod.snd
  exact (tensorContinuousChannels_completelyPositive _ _
    (P.decA_completelyPositive z) (P.decB_completelyPositive z)).comp
      (completelyPositive_adConj _)

/-- The actual joint decoder preserves trace on all complex matrices,
not merely on positive or Hermitian inputs. -/
theorem jointDecoder_tracePreserving (z : σA × σB)
    (X : Matrix ((κA × μA) × (κB × μB)) ((κA × μA) × (κB × μB)) ℂ) :
    (P.jointDecoder z X).trace = X.trace := by
  change (tensorContinuousChannels (P.decA z) (P.decB z)
    (adConj (exchangeMatrix κA μA κB μB) X)).trace = X.trace
  rw [tensorContinuousChannels_tracePreserving _ _
    (P.decA_tracePreserving z) (P.decB_tracePreserving z)]
  exact trace_adConj_isometry (isIsometry_exchangeMatrix κA μA κB μB) X

/-- Unnormalized actual branch operation on arbitrary local CP-density maps. -/
def branchOperation (z : σA × σB)
    (Φ : MatrixOperation (ιA × ρA) (κA × μA))
    (Ψ : MatrixOperation (ιB × ρB) (κB × μB)) :
    MatrixOperation (ιA × ιB) (ιA' × ιB') :=
  decodedTensorChannel (P.jointDecoder z) P.resourceInsertion Φ Ψ

/-- The genuine joint density score of the original protocol and chosen
actual instrument representations. -/
def jointScore [Nonempty ιA] [Nonempty ιB]
    (S : MatrixOperation (ιA × ιB) (ιA' × ιB') →L[ℝ] ℝ) : σA × σB → ℝ :=
  jointDensityChannelScore S P.resourceInsertion P.jointDecoder P.densityA P.densityB

/-- Joint score integrability is derived from actual RN representations
and final-channel CP/TP, not supplied as a protocol field. -/
theorem integrable_jointScore [Nonempty ιA] [Nonempty ιB]
    (S : MatrixOperation (ιA × ιB) (ιA' × ιB') →L[ℝ] ℝ) :
    Integrable (P.jointScore S) (P.probabilityA.prod P.probabilityB) := by
  have hout := P.instrument_outputs_nonempty
  let : Nonempty (κA × μA) := hout.1
  let : Nonempty (κB × μB) := hout.2
  exact integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving
    P.probabilityA P.probabilityB S P.resourceInsertion P.jointDecoder P.densityA P.densityB
    P.measurable_jointDecoder P.densityA_spec.1 P.densityB_spec.1
    P.densityA_spec.2.1 P.densityB_spec.2.1
    P.jointDecoder_completelyPositive P.jointDecoder_tracePreserving

end StandardBorelClassicalProtocol

end

end NLQCLean.ClassicalCommunication
