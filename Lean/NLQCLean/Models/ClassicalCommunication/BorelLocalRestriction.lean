import NLQCLean.Models.ClassicalCommunication.InstrumentPrecomposition
import NLQCLean.Models.ClassicalCommunication.BorelMixed
import NLQCLean.Models.ClassicalCommunication.FiniteLogicalRestriction

/-!
# Local restriction of actual standard-Borel protocols

Isometric input embeddings are absorbed into the original Borel instruments
and fixed local CP/TP output channels are composed with the original final
channel families. The resource, both quantum messages, the classical outcome
spaces and all kept systems are unchanged. The operational channel of the
restricted protocol is exactly the original operational channel sandwiched
between the input embedding and the tensor product of the output channels,
also for a common-map finite mixed resource.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Kronecker Matrix.Norms.Elementwise NNReal ENNReal

attribute [local implicit_reducible] Matrix

/-- Tensor products of channels are functorial. -/
theorem tensorChannels_comp {ι κ τ υ ν χ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq υ]
    (F : Matrix κ κ ℂ →ₗ[ℂ] Matrix ν ν ℂ) (G : Matrix υ υ ℂ →ₗ[ℂ] Matrix χ χ ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels (F.comp Φ) (G.comp Ψ) = (tensorChannels F G).comp (tensorChannels Φ Ψ) := by
  have hs (u v : ι × τ) :
      tensorChannels (F.comp Φ) (G.comp Ψ) (Matrix.single u v 1) =
        (tensorChannels F G).comp (tensorChannels Φ Ψ) (Matrix.single u v 1) := by
    rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    rw [LinearMap.comp_apply, tensorChannels_single, tensorChannels_single,
      tensorChannels_kronecker]
    rfl
  apply LinearMap.ext
  intro Z
  ext k l
  rw [linearMap_matrix_apply (tensorChannels (F.comp Φ) (G.comp Ψ)) Z k l,
    linearMap_matrix_apply ((tensorChannels F G).comp (tensorChannels Φ Ψ)) Z k l]
  simp only [hs]

noncomputable section

noncomputable local instance restrictionMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance restrictionMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (restrictionMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance borel_local_restriction_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance borel_local_restriction_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance restrictionOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restrictionOperationComplexNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℂ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance restrictionOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

local instance borel_local_restriction_instance_3 {ν : Type*} [Fintype ν] :
    MeasurableSpace (Matrix ν ν ℂ) := borel (Matrix ν ν ℂ)

local instance borel_local_restriction_instance_4 {ν : Type*} [Fintype ν] :
    BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance borel_local_restriction_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance borel_local_restriction_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

local instance borel_local_restriction_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional

local instance borel_local_restriction_instance_8 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : CompleteSpace (MatrixOperation ι κ) :=
  FiniteDimensional.complete ℝ _

section Sandwich

variable {ι κ τ ν : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq ν]

/-- Fixed pre- and postcomposition, as a real-linear map of operations. -/
def operationSandwichRealLinear (F : MatrixOperation κ ν) (E : MatrixOperation τ ι) :
    MatrixOperation ι κ →ₗ[ℝ] MatrixOperation τ ν where
  toFun Φ := F.comp (Φ.comp E)
  map_add' Φ Ψ := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' r Φ := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

/-- Finite-dimensional continuity of the fixed sandwich. -/
def operationSandwich (F : MatrixOperation κ ν) (E : MatrixOperation τ ι) :
    MatrixOperation ι κ →L[ℝ] MatrixOperation τ ν :=
  (operationSandwichRealLinear F E).toContinuousLinearMap

omit [DecidableEq τ] [DecidableEq ν] in
@[simp] theorem operationSandwich_apply (F : MatrixOperation κ ν) (E : MatrixOperation τ ι)
    (Φ : MatrixOperation ι κ) : operationSandwich F E Φ = F.comp (Φ.comp E) := rfl

end Sandwich

namespace StandardBorelClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' τA τB νA νB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype τA] [Fintype τB] [Fintype νA] [Fintype νB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq τA] [DecidableEq τB]
variable [DecidableEq νA] [DecidableEq νB]
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable (P : StandardBorelClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')

/-- Restrict the logical inputs by local isometries and post-process both
outputs by fixed local CP/TP channels. Resource, messages and outcome
spaces are unchanged. -/
def restrictLocal (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (hEA : IsIsometry EA) (hEB : IsIsometry EB)
    (FA : MatrixOperation ιA' νA) (FB : MatrixOperation ιB' νB)
    (hFA : CompletelyPositive FA.toLinearMap) (hFB : CompletelyPositive FB.toLinearMap)
    (hFAt : ∀ X, (FA X).trace = X.trace) (hFBt : ∀ X, (FB X).trace = X.trace) :
    StandardBorelClassicalProtocol τA τB ρA ρB κA κB μA μB σA σB νA νB where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := P.instrumentA.precomposeIsometry (EA ⊗ₖ (1 : Matrix ρA ρA ℂ))
    (hEA.kronecker isIsometry_one)
  instrumentB := P.instrumentB.precomposeIsometry (EB ⊗ₖ (1 : Matrix ρB ρB ℂ))
    (hEB.kronecker isIsometry_one)
  decA z := FA.comp (P.decA z)
  decB z := FB.comp (P.decB z)
  decA_choiMeasurable := (measurable_unnormalizedChoi_iff _).mpr
    ((continuous_const.clm_comp continuous_id).measurable.comp P.measurable_decA)
  decB_choiMeasurable := (measurable_unnormalizedChoi_iff _).mpr
    ((continuous_const.clm_comp continuous_id).measurable.comp P.measurable_decB)
  decA_completelyPositive z := hFA.comp (P.decA_completelyPositive z)
  decB_completelyPositive z := hFB.comp (P.decB_completelyPositive z)
  decA_tracePreserving z X := by
    change (FA (P.decA z X)).trace = X.trace
    rw [hFAt, P.decA_tracePreserving]
  decB_tracePreserving z X := by
    change (FB (P.decB z X)).trace = X.trace
    rw [hFBt, P.decB_tracePreserving]

section Restricted

variable (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (hEA : IsIsometry EA) (hEB : IsIsometry EB)
    (FA : MatrixOperation ιA' νA) (FB : MatrixOperation ιB' νB)
    (hFA : CompletelyPositive FA.toLinearMap) (hFB : CompletelyPositive FB.toLinearMap)
    (hFAt : ∀ X, (FA X).trace = X.trace) (hFBt : ∀ X, (FB X).trace = X.trace)

/-- The quantum footprint is unchanged: resource and messages are retained. -/
theorem restrictLocal_hasQuantumFootprint_iff (K : ℕ) :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).HasQuantumFootprint K ↔
      P.HasQuantumFootprint K := Iff.rfl

/-- Restriction commutes with replacing the resource. -/
theorem restrictLocal_withResource (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).withResource γ hγ =
      (P.withResource γ hγ).restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt := rfl

/-- The common-map mixed quantum footprint is unchanged. -/
theorem restrictLocal_hasMixedQuantumFootprint_iff {n : ℕ} (m : MixedResource ρA ρB n)
    (K : ℕ) :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).HasMixedQuantumFootprint m K ↔
      P.HasMixedQuantumFootprint m K := Iff.rfl

/-- The restricted joint decoder is the original one followed by the output channels. -/
theorem restrictLocal_jointDecoder (z : σA × σB) :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).jointDecoder z =
      (tensorContinuousChannels FA FB).comp (P.jointDecoder z) := by
  apply ContinuousLinearMap.coe_injective
  change (tensorChannels (FA.toLinearMap.comp (P.decA z).toLinearMap)
      (FB.toLinearMap.comp (P.decB z).toLinearMap)).comp
        (adConj (exchangeMatrix κA μA κB μB)) =
    (tensorChannels FA.toLinearMap FB.toLinearMap).comp
      ((tensorChannels (P.decA z).toLinearMap (P.decB z).toLinearMap).comp
        (adConj (exchangeMatrix κA μA κB μB)))
  rw [tensorChannels_comp, LinearMap.comp_assoc]

/-- Precomposed local operations after the restricted resource insertion are the
original local operations after the original insertion and the joint embedding. -/
theorem restrictLocal_resourceInsertion
    (ΦA : MatrixOperation (ιA × ρA) (κA × μA)) (ΦB : MatrixOperation (ιB × ρB) (κB × μB)) :
    (tensorContinuousChannels
        (operationPrecompositionContinuousRealLinear (EA ⊗ₖ (1 : Matrix ρA ρA ℂ)) ΦA)
        (operationPrecompositionContinuousRealLinear (EB ⊗ₖ (1 : Matrix ρB ρB ℂ)) ΦB)).comp
        (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).resourceInsertion =
      (tensorContinuousChannels ΦA ΦB).comp
        (P.resourceInsertion.comp (adConj (EA ⊗ₖ EB)).toContinuousLinearMap) := by
  apply ContinuousLinearMap.coe_injective
  change (tensorChannels (ΦA.toLinearMap.comp (adConj (EA ⊗ₖ (1 : Matrix ρA ρA ℂ))))
      (ΦB.toLinearMap.comp (adConj (EB ⊗ₖ (1 : Matrix ρB ρB ℂ))))).comp
        (adConj (insertResource τA τB P.resource)) =
    (tensorChannels ΦA.toLinearMap ΦB.toLinearMap).comp
      ((adConj (insertResource ιA ιB P.resource)).comp (adConj (EA ⊗ₖ EB)))
  rw [tensorChannels_comp, tensorChannels_adConj, LinearMap.comp_assoc,
    ← adConj_mul_eq_comp, ← adConj_mul_eq_comp, insertResource_logical_precompose]

variable [Nonempty ιA] [Nonempty ιB] [Nonempty τA] [Nonempty τB]

/-- **Operational restriction.** The restricted protocol implements exactly the
sandwiched original operational channel. -/
theorem restrictLocal_operationalChannel :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).operationalChannel =
      operationSandwich (tensorContinuousChannels FA FB)
        (adConj (EA ⊗ₖ EB)).toContinuousLinearMap P.operationalChannel := by
  let Q := P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt
  let : Nonempty ρA := P.resource_nonempty.map Prod.fst
  let : Nonempty ρB := P.resource_nonempty.map Prod.snd
  let EA' := EA ⊗ₖ (1 : Matrix ρA ρA ℂ)
  let EB' := EB ⊗ₖ (1 : Matrix ρB ρB ℂ)
  have hEA' : IsIsometry EA' := hEA.kronecker isIsometry_one
  have hEB' : IsIsometry EB' := hEB.kronecker isIsometry_one
  obtain ⟨hAm, hAi, hAr, -, -⟩ := P.densityA_spec
  obtain ⟨hBm, hBi, hBr, -, -⟩ := P.densityB_spec
  let gA := normalizedPrecompositionDensity EA' P.densityA
  let gB := normalizedPrecompositionDensity EB' P.densityB
  let qA := precompositionTraceWeight EA' P.densityA
  let qB := precompositionTraceWeight EB' P.densityB
  have hspecA := P.instrumentA.normalizedPrecompositionDensity_spec EA' hEA'
    P.densityA hAm hAi hAr
  have hspecB := P.instrumentB.normalizedPrecompositionDensity_spec EB' hEB'
    P.densityB hBm hBi hBr
  have hprobA : Q.probabilityA = P.probabilityA.withDensity (fun x => (qA x : ℝ≥0∞)) :=
    P.instrumentA.traceProbability_precomposeIsometry EA' hEA' P.densityA hAi hAr
  have hprobB : Q.probabilityB = P.probabilityB.withDensity (fun x => (qB x : ℝ≥0∞)) :=
    P.instrumentB.traceProbability_precomposeIsometry EB' hEB' P.densityB hBi hBr
  have hqA : Measurable qA := measurable_precompositionTraceWeight EA' P.densityA hAm
  have hqB : Measurable qB := measurable_precompositionTraceWeight EB' P.densityB hBm
  rw [Q.operationalChannel_eq_of_reconstructed_densities gA gB hspecA.2.1 hspecB.2.1
    hspecA.2.2 hspecB.2.2]
  rw [hprobA, hprobB, prod_withDensity hqA.coe_nnreal_ennreal hqB.coe_nnreal_ennreal]
  have hdens : (fun z : σA × σB => (qA z.1 : ℝ≥0∞) * (qB z.2 : ℝ≥0∞)) =
      fun z => ((qA z.1 * qB z.2 : ℝ≥0) : ℝ≥0∞) := by
    funext z
    rw [ENNReal.coe_mul]
  rw [hdens, integral_withDensity_eq_integral_smul
    (f := fun z : σA × σB => qA z.1 * qB z.2)
    ((hqA.comp measurable_fst).mul (hqB.comp measurable_snd))]
  change _ = operationSandwich (tensorContinuousChannels FA FB)
    (adConj (EA ⊗ₖ EB)).toContinuousLinearMap
      (∫ z, jointDensityChannel P.resourceInsertion P.jointDecoder P.densityA P.densityB z
        ∂P.probabilityA.prod P.probabilityB)
  rw [← (operationSandwich (tensorContinuousChannels FA FB)
    (adConj (EA ⊗ₖ EB)).toContinuousLinearMap).integral_comp_comm
      P.integrable_operationDensity]
  have hcA := P.instrumentA.ae_precompositionTraceWeight_smul_normalizedDensity
    EA' P.densityA hAi hAr
  have hcB := P.instrumentB.ae_precompositionTraceWeight_smul_normalizedDensity
    EB' P.densityB hBi hBr
  have hAprod := (Measure.quasiMeasurePreserving_fst (μ := P.probabilityA)
    (ν := P.probabilityB)).ae_eq_comp hcA
  have hBprod := (Measure.quasiMeasurePreserving_snd (μ := P.probabilityA)
    (ν := P.probabilityB)).ae_eq_comp hcB
  apply integral_congr_ae
  filter_upwards [hAprod, hBprod] with z hzA hzB
  change (qA z.1 : ℝ) • gA z.1 =
    operationPrecompositionContinuousRealLinear EA' (P.densityA z.1) at hzA
  change (qB z.2 : ℝ) • gB z.2 =
    operationPrecompositionContinuousRealLinear EB' (P.densityB z.2) at hzB
  change (qA z.1 * qB z.2 : ℝ≥0) • decodedTensorChannel (Q.jointDecoder z) Q.resourceInsertion
      (gA z.1) (gB z.2) =
    (tensorContinuousChannels FA FB).comp
      ((decodedTensorChannel (P.jointDecoder z) P.resourceInsertion
        (P.densityA z.1) (P.densityB z.2)).comp (adConj (EA ⊗ₖ EB)).toContinuousLinearMap)
  have hscale : (qA z.1 * qB z.2 : ℝ≥0) • decodedTensorChannel (Q.jointDecoder z)
      Q.resourceInsertion (gA z.1) (gB z.2) =
      decodedTensorChannel (Q.jointDecoder z) Q.resourceInsertion
        ((qA z.1 : ℝ) • gA z.1) ((qB z.2 : ℝ) • gB z.2) := by
    rw [NNReal.smul_def, NNReal.coe_mul]
    change _ = decodedTensorChannelRightRealLinear (Q.jointDecoder z) Q.resourceInsertion
      ((qA z.1 : ℝ) • gA z.1) ((qB z.2 : ℝ) • gB z.2)
    rw [map_smul]
    change _ = (qB z.2 : ℝ) • decodedTensorChannelLeftRealLinear (Q.jointDecoder z)
      Q.resourceInsertion (gB z.2) ((qA z.1 : ℝ) • gA z.1)
    rw [map_smul, smul_smul, mul_comm]
    rfl
  rw [hscale, hzA, hzB]
  unfold decodedTensorChannel
  rw [P.restrictLocal_jointDecoder EA EB hEA hEB FA FB hFA hFB hFAt hFBt z,
    P.restrictLocal_resourceInsertion EA EB hEA hEB FA FB hFA hFB hFAt hFBt]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The pure restricted channel at the level of linear maps. -/
theorem restrictLocal_operationalChannel_toLinearMap :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).operationalChannel.toLinearMap =
      (tensorChannels FA.toLinearMap FB.toLinearMap).comp
        (P.operationalChannel.toLinearMap.comp (adConj (EA ⊗ₖ EB))) := by
  rw [restrictLocal_operationalChannel]
  rfl

/-- The restricted mixed channel is the sandwiched original mixed channel. -/
theorem restrictLocal_mixedOperationalChannel {n : ℕ} (m : MixedResource ρA ρB n) :
    (P.restrictLocal EA EB hEA hEB FA FB hFA hFB hFAt hFBt).mixedOperationalChannel m =
      (tensorChannels FA.toLinearMap FB.toLinearMap).comp
        ((P.mixedOperationalChannel m).comp (adConj (EA ⊗ₖ EB))) := by
  apply LinearMap.ext
  intro X
  simp only [mixedOperationalChannel, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact LinearMap.congr_fun ((P.componentProtocol m k).restrictLocal_operationalChannel_toLinearMap
    EA EB hEA hEB FA FB hFA hFB hFAt hFBt) X

end Restricted

end StandardBorelClassicalProtocol

end

end NLQCLean.ClassicalCommunication
