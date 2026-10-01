import NLQCLean.Models.ClassicalCommunication.StandardBorelProtocol
import NLQCLean.Models.ClassicalCommunication.DensityScoreFunctionals

/-!
# Operational integrals of original Borel instruments

The actual joint operation density is Bochner integrable by a derived
finite-system CP/TP bound. Its integral is independent of the choice of
reconstructing RN densities of the original instruments. Real-linear target
scores commute with this operation integral.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance operationalMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance operationalMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (operationalMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance borel_operational_channel_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance borel_operational_channel_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance operationalChannelNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance operationalChannelComplexNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℂ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance operationalChannelRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

local instance borel_operational_channel_instance_3 {ν : Type*} [Fintype ν] : MeasurableSpace (Matrix ν ν ℂ) :=
  borel (Matrix ν ν ℂ)

local instance borel_operational_channel_instance_4 {ν : Type*} [Fintype ν] : BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance borel_operational_channel_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance borel_operational_channel_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

local instance borel_operational_channel_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional

local instance borel_operational_channel_instance_8 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    CompleteSpace (MatrixOperation ι κ) := FiniteDimensional.complete ℝ _

section JointOperations

variable {ι κ τ υ ν χ α β : Type*}
variable [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ] [Fintype ν] [Fintype χ]
variable [DecidableEq ι] [DecidableEq τ]
variable [MeasurableSpace α] [MeasurableSpace β]

/-- The actual joint branch operation, before taking any scalar score. -/
def jointDensityChannel (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ) :
    α × β → MatrixOperation ν χ :=
  fun z => decodedTensorChannel (D z) R (Φ z.1) (Ψ z.2)

/-- Joint operation measurability is genuine tensor/composition continuity. -/
theorem measurable_jointDensityChannel
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hD : Measurable D) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    Measurable (jointDensityChannel R D Φ Ψ) := by
  have hT : Continuous (fun p : MatrixOperation (κ × υ) χ ×
      (MatrixOperation ι κ × MatrixOperation τ υ) =>
        tensorContinuousChannels p.2.1 p.2.2) :=
    ((tensorContinuousChannelsBilinear (ι := ι) (κ := κ) (τ := τ) (υ := υ)).continuous.comp
      (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)
  have hcont : Continuous (fun p : MatrixOperation (κ × υ) χ ×
      (MatrixOperation ι κ × MatrixOperation τ υ) =>
        decodedTensorChannel p.1 R p.2.1 p.2.2) :=
    continuous_fst.clm_comp (hT.clm_comp_const R)
  exact hcont.measurable.comp
    (hD.prodMk ((hΦ.comp measurable_fst).prodMk (hΨ.comp measurable_snd)))

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- A genuine operation-norm bound dominates the joint operation by the
product of the two local density norms. -/
theorem norm_jointDensityChannel_le
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z, ‖D z‖ ≤ B) (z : α × β) :
    ‖jointDensityChannel R D Φ Ψ z‖ ≤
      (B * ‖R‖ * ‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
        (τ := τ) (υ := υ)‖) * ‖Φ z.1‖ * ‖Ψ z.2‖ := by
  have hT := (tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
    (τ := τ) (υ := υ)).le_opNorm₂ (Φ z.1) (Ψ z.2)
  have hcomp := (tensorContinuousChannels (Φ z.1) (Ψ z.2)).opNorm_comp_le R
  have hpost := (D z).opNorm_comp_le
    ((tensorContinuousChannels (Φ z.1) (Ψ z.2)).comp R)
  calc
    ‖jointDensityChannel R D Φ Ψ z‖ ≤
        B * ((‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
          (τ := τ) (υ := υ)‖ * ‖Φ z.1‖ * ‖Ψ z.2‖) * ‖R‖) :=
      hpost.trans (mul_le_mul (hD z) (hcomp.trans (mul_le_mul_of_nonneg_right hT
        (norm_nonneg R))) (norm_nonneg _) hB)
    _ = _ := by ring

/-- The whole original operation density is integrable, not merely a
chosen target score. Boundedness is derived from actual final CP/TP maps. -/
theorem integrable_jointDensityChannel
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (μ : Measure α) (νB : Measure β) [SFinite μ] [SFinite νB]
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z X, (D z X).trace = X.trace) :
    Integrable (jointDensityChannel R D Φ Ψ) (μ.prod νB) := by
  obtain ⟨B, hB, hnorm⟩ := exists_completelyPositive_tracePreserving_norm_bound (κ × υ) χ
  let A := B * ‖R‖ * ‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
    (τ := τ) (υ := υ)‖
  have hmajorant : Integrable (fun z : α × β => A * (‖Φ z.1‖ * ‖Ψ z.2‖))
      (μ.prod νB) := (hΦ.norm.mul_prod hΨ.norm).const_mul A
  apply hmajorant.mono'
    (measurable_jointDensityChannel R D Φ Ψ hDmeas hΦmeas hΨmeas).aestronglyMeasurable
  filter_upwards with z
  simpa only [A, mul_assoc] using norm_jointDensityChannel_le R D Φ Ψ hB
    (fun z => hnorm (D z) (hDCP z) (hDTP z)) z

end JointOperations

namespace CPVectorInstrument

variable {α ι κ : Type*} [MeasurableSpace α]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]

/-- Two actual integrable densities reconstructing the same instrument
agree almost everywhere in its derived trace probability. -/
theorem reconstructed_density_ae_eq (I : CPVectorInstrument α ι κ)
    (Φ Ψ : α → MatrixOperation ι κ)
    (hΦ : Integrable Φ I.traceProbability) (hΨ : Integrable Ψ I.traceProbability)
    (hrepΦ : I.traceProbability.withDensityᵥ Φ = I.operationMeasure)
    (hrepΨ : I.traceProbability.withDensityᵥ Ψ = I.operationMeasure) :
    Φ =ᵐ[I.traceProbability] Ψ :=
  hΦ.ae_eq_of_withDensityᵥ_eq hΨ (hrepΦ.trans hrepΨ.symm)

end CPVectorInstrument

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

/-- The actual Bochner integral operation of the original CP instruments. -/
def operationalChannel : MatrixOperation (ιA × ιB) (ιA' × ιB') :=
  ∫ z, jointDensityChannel P.resourceInsertion P.jointDecoder P.densityA P.densityB z
    ∂P.probabilityA.prod P.probabilityB

/-- The original branch-operation integral is genuinely integrable. -/
theorem integrable_operationDensity :
    Integrable (jointDensityChannel P.resourceInsertion P.jointDecoder P.densityA P.densityB)
      (P.probabilityA.prod P.probabilityB) := by
  have hout := P.instrument_outputs_nonempty
  let : Nonempty (κA × μA) := hout.1
  let : Nonempty (κB × μB) := hout.2
  exact integrable_jointDensityChannel P.probabilityA P.probabilityB
    P.resourceInsertion P.jointDecoder P.densityA P.densityB
    P.measurable_jointDecoder P.densityA_spec.1 P.densityB_spec.1
    P.densityA_spec.2.1 P.densityB_spec.2.1
    P.jointDecoder_completelyPositive P.jointDecoder_tracePreserving

/-- Continuous target scores commute with the operational integral. -/
theorem score_operationalChannel
    (S : MatrixOperation (ιA × ιB) (ιA' × ιB') →L[ℝ] ℝ) :
    S P.operationalChannel = ∫ z, P.jointScore S z ∂P.probabilityA.prod P.probabilityB :=
  (S.integral_comp_comm P.integrable_operationDensity).symm

/-- Existing real-linear target scores use the identical operation, with
continuity supplied by the actual Choi equivalence. -/
theorem linearScore_operationalChannel
    (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ) :
    S P.operationalChannel.toLinearMap =
      ∫ z, P.jointScore (continuousMatrixOperationRealScore S) z
        ∂P.probabilityA.prod P.probabilityB :=
  P.score_operationalChannel (continuousMatrixOperationRealScore S)

/-- Any actual reconstructing densities give the same whole operational
channel. Arbitrary versions cannot change a score or normalized error. -/
theorem operationalChannel_eq_of_reconstructed_densities
    (Φ : σA → MatrixOperation (ιA × ρA) (κA × μA))
    (Ψ : σB → MatrixOperation (ιB × ρB) (κB × μB))
    (hΦ : Integrable Φ P.probabilityA) (hΨ : Integrable Ψ P.probabilityB)
    (hrepA : P.probabilityA.withDensityᵥ Φ = P.instrumentA.operationMeasure)
    (hrepB : P.probabilityB.withDensityᵥ Ψ = P.instrumentB.operationMeasure) :
    P.operationalChannel = ∫ z, jointDensityChannel P.resourceInsertion P.jointDecoder Φ Ψ z
      ∂P.probabilityA.prod P.probabilityB := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  have hA := P.instrumentA.reconstructed_density_ae_eq P.densityA Φ
    P.densityA_spec.2.1 hΦ P.densityA_spec.2.2.1 hrepA
  have hB := P.instrumentB.reconstructed_density_ae_eq P.densityB Ψ
    P.densityB_spec.2.1 hΨ P.densityB_spec.2.2.1 hrepB
  have hAprod := (Measure.quasiMeasurePreserving_fst (μ := P.probabilityA)
    (ν := P.probabilityB)).ae_eq hA
  have hBprod := (Measure.quasiMeasurePreserving_snd (μ := P.probabilityA)
    (ν := P.probabilityB)).ae_eq hB
  apply integral_congr_ae
  filter_upwards [hAprod, hBprod] with z hzA hzB
  change P.densityA z.1 = Φ z.1 at hzA
  change P.densityB z.2 = Ψ z.2 at hzB
  simp only [jointDensityChannel, hzA, hzB]

end StandardBorelClassicalProtocol

end

end NLQCLean.ClassicalCommunication
