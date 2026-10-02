import NLQCLean.Models.ClassicalCommunication.BorelOperationalChannel
import Mathlib.Analysis.Convex.Integral

/-!
# Normalization of actual Borel operational channels

The Bochner integral of the original joint operation densities is completely
positive and trace preserving. Positivity follows from the genuine continuous
Choi representation and the closed convex positive-matrix cone. Trace
preservation follows from the integrated instrument totals and Fubini, after
discarding the actual trace-preserving final operations. The densities are
not asserted to preserve trace individually. All complex input matrices are
covered, without a Hermitian or positivity restriction.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance normalizationMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance normalizationMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (normalizationMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance borel_channel_normalization_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance borel_channel_normalization_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance normalizationChannelNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance normalizationChannelComplexNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℂ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance normalizationChannelRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

local instance borel_channel_normalization_instance_3 {ν : Type*} [Fintype ν] : MeasurableSpace (Matrix ν ν ℂ) :=
  borel (Matrix ν ν ℂ)

local instance borel_channel_normalization_instance_4 {ν : Type*} [Fintype ν] : BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance borel_channel_normalization_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional

local instance borel_channel_normalization_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    CompleteSpace (MatrixOperation ι κ) := FiniteDimensional.complete ℝ _

private def matrixConjugateTransposeRealLinear {ν : Type*} :
    Matrix ν ν ℂ →ₗ[ℝ] Matrix ν ν ℂ where
  toFun C := Cᴴ
  map_add' C D := Matrix.conjTranspose_add C D
  map_smul' r C := by simp

private def matrixQuadraticRealLinear {ν : Type*} [Fintype ν] (v : ν → ℂ) :
    Matrix ν ν ℂ →ₗ[ℝ] ℂ where
  toFun C := star v ⬝ᵥ (C *ᵥ v)
  map_add' C D := by simp only [Matrix.add_mulVec, dotProduct_add]
  map_smul' r C := by simp only [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

private theorem matrixHermitian_quadratic_im_zero {ν : Type*} [Fintype ν]
    {C : Matrix ν ν ℂ} (hC : C.IsHermitian) (v : ν → ℂ) :
    (star v ⬝ᵥ (C *ᵥ v)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (star v ⬝ᵥ (C *ᵥ v)) = star v ⬝ᵥ (C *ᵥ v)
  rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hC.eq]

/-- The finite positive-matrix cone is genuinely closed in the matrix topology. -/
theorem isClosed_posSemidef_set (ν : Type*) [Fintype ν] :
    IsClosed {C : Matrix ν ν ℂ | C.PosSemidef} := by
  have hset : {C : Matrix ν ν ℂ | C.PosSemidef} =
      {C | C.IsHermitian} ∩ ⋂ v : ν → ℂ, {C | 0 ≤ (star v ⬝ᵥ (C *ᵥ v)).re} := by
    ext C
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro hC
      exact ⟨hC.isHermitian, hC.re_dotProduct_nonneg⟩
    · rintro ⟨hC, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hC
      intro v
      exact Complex.nonneg_iff.mpr ⟨hq v, (matrixHermitian_quadratic_im_zero hC v).symm⟩
  rw [hset]
  have hH : IsClosed {C : Matrix ν ν ℂ | C.IsHermitian} :=
    isClosed_eq (matrixConjugateTransposeRealLinear.toContinuousLinearMap).continuous continuous_id
  apply hH.inter
  apply isClosed_iInter
  intro v
  exact isClosed_le continuous_const
    (Complex.reCLM.comp (matrixQuadraticRealLinear v).toContinuousLinearMap).continuous

/-- Nonnegative real combinations preserve the actual positive-matrix cone. -/
theorem convex_posSemidef_set (ν : Type*) [Fintype ν] :
    Convex ℝ {C : Matrix ν ν ℂ | C.PosSemidef} := by
  intro A hA B hB a b ha hb _
  have hAP : A.PosSemidef := hA
  have hBP : B.PosSemidef := hB
  exact (hAP.smul ha).add (hBP.smul hb)

/-- The probability integral of almost-everywhere positive matrices is positive. -/
theorem posSemidef_integral {α ν : Type*} [MeasurableSpace α] [Fintype ν]
    {μ : Measure α} [IsProbabilityMeasure μ] {C : α → Matrix ν ν ℂ}
    (hC : Integrable C μ) (hpositive : ∀ᵐ a ∂μ, (C a).PosSemidef) :
    (∫ a, C a ∂μ).PosSemidef :=
  (convex_posSemidef_set ν).integral_mem (isClosed_posSemidef_set ν) hpositive hC

/-- Complete positivity is preserved by a genuine operation-valued probability
integral, using the proved continuous Choi correspondence. -/
theorem completelyPositive_integral {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    {μ : Measure α} [IsProbabilityMeasure μ] {Φ : α → MatrixOperation ι κ}
    (hΦ : Integrable Φ μ) (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap) :
    CompletelyPositive (∫ a, Φ a ∂μ).toLinearMap := by
  apply (completelyPositive_iff_unnormalizedChoi_posSemidef _).mpr
  let L := (unnormalizedChoiContinuousRealLinearEquiv (ι := ι) (κ := κ)).toContinuousLinearMap
  change (L (∫ a, Φ a ∂μ)).PosSemidef
  rw [← L.integral_comp_comm hΦ]
  apply posSemidef_integral (L.integrable_comp hΦ)
  filter_upwards [hCP] with a ha
  exact (completelyPositive_iff_unnormalizedChoi_posSemidef _).mp ha

section TensorIntegrals

variable {α β ι κ τ υ : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq υ]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
variable {Φ : α → MatrixOperation ι κ} {Ψ : β → MatrixOperation τ υ}

omit [DecidableEq κ] [DecidableEq υ] [SFinite μ] in
/-- Product integrability of the genuine tensor of independent operation densities. -/
theorem integrable_tensorContinuousChannels_prod (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ ν) :
    Integrable (fun z : α × β => tensorContinuousChannels (Φ z.1) (Ψ z.2)) (μ.prod ν) := by
  let B := tensorContinuousChannelsRealBilinear (ι := ι) (κ := κ) (τ := τ) (υ := υ)
  exact hΦ.op_fst_snd (by
    change Continuous (fun p : MatrixOperation ι κ × MatrixOperation τ υ => B p.1 p.2)
    exact (B.continuous.comp continuous_fst).clm_apply continuous_snd)
    ⟨‖B‖, B.le_opNorm₂⟩ hΨ

/-- Fubini and continuous bilinearity identify the actual tensor-density integral. -/
theorem integral_tensorContinuousChannels_prod (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ ν) :
    (∫ z : α × β, tensorContinuousChannels (Φ z.1) (Ψ z.2) ∂μ.prod ν) =
      tensorContinuousChannels (∫ x, Φ x ∂μ) (∫ y, Ψ y ∂ν) :=
  integral_prod_bilin
    (tensorContinuousChannelsRealBilinear (ι := ι) (κ := κ) (τ := τ) (υ := υ)) hΦ hΨ

end TensorIntegrals

/-- Trace after applying an operation to one arbitrary complex matrix is a
genuine continuous real-linear functional on the operation space. -/
def operationTraceAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (X : Matrix ι ι ℂ) : MatrixOperation ι κ →L[ℝ] ℂ :=
  (show MatrixOperation ι κ →ₗ[ℝ] ℂ from
    { toFun := fun Φ => (Φ X).trace
      map_add' := fun Φ Ψ => by simp
      map_smul' := fun r Φ => by simp }).toContinuousLinearMap

@[simp] theorem operationTraceAt_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (X : Matrix ι ι ℂ) (Φ : MatrixOperation ι κ) :
    operationTraceAt X Φ = (Φ X).trace := rfl

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

omit [Nonempty ιB] in
/-- Reconstruction identifies Alice's density integral with her actual total operation. -/
theorem integral_densityA :
    (∫ x, P.densityA x ∂P.probabilityA) = P.instrumentA.operationMeasure univ := by
  have h := congrArg (fun v => v univ) P.densityA_spec.2.2.1
  simpa only [withDensityᵥ_apply P.densityA_spec.2.1 MeasurableSet.univ,
    Measure.restrict_univ] using h

omit [Nonempty ιA] in
/-- Reconstruction identifies Bob's density integral with his actual total operation. -/
theorem integral_densityB :
    (∫ y, P.densityB y ∂P.probabilityB) = P.instrumentB.operationMeasure univ := by
  have h := congrArg (fun v => v univ) P.densityB_spec.2.2.1
  simpa only [withDensityᵥ_apply P.densityB_spec.2.1 MeasurableSet.univ,
    Measure.restrict_univ] using h

/-- Almost every actual joint density operation is completely positive. -/
theorem operationDensity_ae_completelyPositive :
    ∀ᵐ z ∂P.probabilityA.prod P.probabilityB,
      CompletelyPositive
        (jointDensityChannel P.resourceInsertion P.jointDecoder P.densityA P.densityB z).toLinearMap := by
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  have hA := (Measure.quasiMeasurePreserving_fst (μ := P.probabilityA)
    (ν := P.probabilityB)).ae P.densityA_spec.2.2.2.1
  have hB := (Measure.quasiMeasurePreserving_snd (μ := P.probabilityA)
    (ν := P.probabilityB)).ae P.densityB_spec.2.2.2.1
  filter_upwards [hA, hB] with z hzA hzB
  have hR : CompletelyPositive P.resourceInsertion.toLinearMap := completelyPositive_adConj _
  exact (P.jointDecoder_completelyPositive z).comp
    ((tensorContinuousChannels_completelyPositive _ _ hzA.1 hzB.1).comp hR)

/-- The defined original Borel operational channel is completely positive;
this is derived from the instrument densities, not a protocol field. -/
theorem operationalChannel_completelyPositive :
    CompletelyPositive P.operationalChannel.toLinearMap :=
  completelyPositive_integral P.integrable_operationDensity P.operationDensity_ae_completelyPositive

/-- The defined original operational channel preserves the trace of every
complex matrix. Only the integrated instrument totals are normalized. -/
theorem operationalChannel_tracePreserving (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    (P.operationalChannel X).trace = X.trace := by
  let S := operationTraceAt (κ := ιA' × ιB') X
  let T := operationTraceAt (κ := (κA × μA) × (κB × μB)) (P.resourceInsertion X)
  have hT := integrable_tensorContinuousChannels_prod P.densityA_spec.2.1 P.densityB_spec.2.1
  calc
    (P.operationalChannel X).trace =
        ∫ z, S (jointDensityChannel P.resourceInsertion P.jointDecoder P.densityA P.densityB z)
          ∂P.probabilityA.prod P.probabilityB :=
      (S.integral_comp_comm P.integrable_operationDensity).symm
    _ = ∫ z, T (tensorContinuousChannels (P.densityA z.1) (P.densityB z.2))
          ∂P.probabilityA.prod P.probabilityB := by
      apply integral_congr_ae
      filter_upwards with z
      exact P.jointDecoder_tracePreserving z _
    _ = T (∫ z, tensorContinuousChannels (P.densityA z.1) (P.densityB z.2)
          ∂P.probabilityA.prod P.probabilityB) := T.integral_comp_comm hT
    _ = T (tensorContinuousChannels (P.instrumentA.operationMeasure univ)
          (P.instrumentB.operationMeasure univ)) := by
      rw [integral_tensorContinuousChannels_prod P.densityA_spec.2.1 P.densityB_spec.2.1,
        P.integral_densityA, P.integral_densityB]
    _ = (P.resourceInsertion X).trace :=
      tensorContinuousChannels_tracePreserving _ _ P.instrumentA.tracePreserving_total
        P.instrumentB.tracePreserving_total _
    _ = X.trace := trace_adConj_isometry (isIsometry_insertResource P.resource P.resource_unit) X

end StandardBorelClassicalProtocol

end

end NLQCLean.ClassicalCommunication
