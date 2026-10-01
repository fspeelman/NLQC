import NLQCLean.Models.ClassicalCommunication.AveragedChannels

/-!
# Actual standard-Borel protocols with free shared probability randomness

Randomness selects actual pure or common-map finite-mixed protocols. Original
finite quantum systems, standard-Borel outcome spaces and mixed component
counts may depend on the branch. The original channel is their measured
Bochner average, with integrability derived from CP/TP. Branchwise quantum
caps survive high-score branch and resource-component selection.
-/

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open MeasureTheory Matrix Set
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance randomBorelMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance randomBorelMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (randomBorelMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance randomBorelMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance randomBorelMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance randomBorelOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance randomBorelOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {d K : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB σA σB : α → Type*} {ιA' ιB' : Type*}
variable [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
variable [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
variable [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
variable [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
variable [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
variable [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
variable [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
variable [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
variable [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA'] [DecidableEq ιB']

section GeneralOutputs

variable (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
  (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) ιA' ιB')

/-- Actual average of the original Borel branch channels. -/
def sharedRandomOperationalChannel : MatrixOperation (Fin d × Fin d) (ιA' × ιB') :=
  averageOperationalChannel μ (fun a => (P a).operationalChannel)

/-- Original branch integrability follows from CP/TP and measurability,
independently of every original branch workspace and outcome space. -/
theorem integrable_sharedRandom_channelFamily
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) :
    Integrable (fun a => (P a).operationalChannel) μ :=
  integrable_completelyPositive_tracePreserving_family μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_completelyPositive)
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_tracePreserving)

/-- The actual average acts by averaging each original branch output. -/
theorem sharedRandomOperationalChannel_apply
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    sharedRandomOperationalChannel μ P X = ∫ a, (P a).operationalChannel X ∂μ :=
  averageOperationalChannel_apply μ _ (integrable_sharedRandom_channelFamily μ P hP) X

/-- Every original averaged channel score equals its actual mean score. -/
theorem linearScore_sharedRandomOperationalChannel
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ) :
    S (sharedRandomOperationalChannel μ P).toLinearMap =
      ∫ a, S (P a).operationalChannel.toLinearMap ∂μ :=
  linearScore_averageOperationalChannel μ _ (integrable_sharedRandom_channelFamily μ P hP) S

/-- CP of the original probability-average channel is derived. -/
theorem sharedRandomOperationalChannel_completelyPositive
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) :
    CompletelyPositive (sharedRandomOperationalChannel μ P).toLinearMap :=
  averageOperationalChannel_completelyPositive μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_completelyPositive)
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_tracePreserving)

/-- TP of the original probability-average channel is derived. -/
theorem sharedRandomOperationalChannel_tracePreserving
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (sharedRandomOperationalChannel μ P X).trace = X.trace :=
  averageOperationalChannel_tracePreserving μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_completelyPositive)
    (Filter.Eventually.of_forall fun a => (P a).operationalChannel_tracePreserving) X

/-- An actual branch scores at least the original average and satisfies
its almost-everywhere branchwise cap. The cap is not an expected cost. -/
theorem exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) :
    ∃ a, (P a).HasQuantumFootprint K ∧
      S (sharedRandomOperationalChannel μ P).toLinearMap ≤ S (P a).operationalChannel.toLinearMap := by
  have hs := (continuousMatrixOperationRealScore S).integrable_comp
    (integrable_sharedRandom_channelFamily μ P hP)
  obtain ⟨a, ha, hscore⟩ := exists_good_score_ge_integral μ
    (fun a => S (P a).operationalChannel.toLinearMap)
    {a | (P a).HasQuantumFootprint K} hs hK
  refine ⟨a, ha, ?_⟩
  rw [linearScore_sharedRandomOperationalChannel μ P hP S]
  exact hscore

variable {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))

/-- This continuous operation is the unchanged actual common-map mixed
branch channel on every matrix input. -/
def mixedBranchOperation (a : α) : MatrixOperation (Fin d × Fin d) (ιA' × ιB') :=
  ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap

omit [MeasurableSpace α] in
@[simp] theorem mixedBranchOperation_toLinearMap (a : α) :
    (mixedBranchOperation P m a).toLinearMap = (P a).mixedOperationalChannel (m a) := rfl

/-- Actual probability-average of the original mixed Borel branch channels. -/
def mixedSharedRandomOperationalChannel : MatrixOperation (Fin d × Fin d) (ιA' × ιB') :=
  averageOperationalChannel μ (mixedBranchOperation P m)

/-- Mixed branch-channel integrability follows from their derived CP/TP,
including variable component counts and variable original registers. -/
theorem integrable_mixedSharedRandom_channelFamily
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) :
    Integrable (mixedBranchOperation P m) μ :=
  integrable_completelyPositive_tracePreserving_family μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_completelyPositive (m a))
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_tracePreserving (m a))

/-- The actual mixed average acts by averaging original branch outputs. -/
theorem mixedSharedRandomOperationalChannel_apply
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    mixedSharedRandomOperationalChannel μ P m X = ∫ a, (P a).mixedOperationalChannel (m a) X ∂μ :=
  averageOperationalChannel_apply μ _ (integrable_mixedSharedRandom_channelFamily μ P m hP) X

/-- Every original averaged mixed score is its actual mean score. -/
theorem linearScore_mixedSharedRandomOperationalChannel
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ) :
    S (mixedSharedRandomOperationalChannel μ P m).toLinearMap =
      ∫ a, S ((P a).mixedOperationalChannel (m a)) ∂μ :=
  linearScore_averageOperationalChannel μ _ (integrable_mixedSharedRandom_channelFamily μ P m hP) S

/-- CP of the original mixed/random average is derived. -/
theorem mixedSharedRandomOperationalChannel_completelyPositive
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) :
    CompletelyPositive (mixedSharedRandomOperationalChannel μ P m).toLinearMap :=
  averageOperationalChannel_completelyPositive μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_completelyPositive (m a))
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_tracePreserving (m a))

/-- TP of the original mixed/random average is derived. -/
theorem mixedSharedRandomOperationalChannel_tracePreserving
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (mixedSharedRandomOperationalChannel μ P m X).trace = X.trace :=
  averageOperationalChannel_tracePreserving μ _ hP
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_completelyPositive (m a))
    (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_tracePreserving (m a)) X

/-- Select an actual randomness branch and pure common-map component with
score at least the original average and within the branchwise quantum cap. -/
theorem exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) :
    ∃ a, ∃ k : Fin (n a), ((P a).componentProtocol (m a) k).HasQuantumFootprint K ∧
      S (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤
        S ((P a).componentProtocol (m a) k).operationalChannel.toLinearMap := by
  have hs := (continuousMatrixOperationRealScore S).integrable_comp
    (integrable_mixedSharedRandom_channelFamily μ P m hP)
  obtain ⟨a, ha, hscore⟩ := exists_good_score_ge_integral μ
    (fun a => S ((P a).mixedOperationalChannel (m a)))
    {a | (P a).HasMixedQuantumFootprint (m a) K} hs hK
  obtain ⟨k, hk, hcap⟩ := (P a).exists_component_linearScore_ge_hasQuantumFootprint S (m a) ha
  refine ⟨a, k, hcap, ?_⟩
  rw [linearScore_mixedSharedRandomOperationalChannel μ P m hP S]
  exact hscore.trans hk

end GeneralOutputs


/-- The original averaged unitary Choi score gives an actual charged protocol. -/
theorem mem_pureReachable_of_sharedRandom_quantumFootprint
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) (sharedRandomOperationalChannel μ P).toLinearMap) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨a, hcap, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (unitaryScoreRealLinear (U : Matrix _ _ ℂ)) hK
  apply (P a).mem_pureReachable_of_quantumFootprint U hd hcap
  exact hscore.trans hs

/-- Original averaged-channel diamond accuracy is converted before selecting randomness or resource components. -/
theorem mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (herror : diamondError (sharedRandomOperationalChannel μ P).toLinearMap (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  have htrace := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving _
    (sharedRandomOperationalChannel_completelyPositive μ P hP) (sharedRandomOperationalChannel_tracePreserving μ P hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError
    (Matrix.mem_unitaryGroup_iff'.mp U.property) (sharedRandomOperationalChannel μ P).toLinearMap htrace
  apply mem_pureReachable_of_sharedRandom_quantumFootprint μ P hP U hd hK
  linarith

/-- The original averaged joint PVM score gives an actual charged protocol. -/
theorem mem_purePVMReachable_of_sharedRandom_quantumFootprint
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) (sharedRandomOperationalChannel μ P).toLinearMap) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨a, hcap, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (pvmScoreRealLinear (M : Matrix _ _ ℂ)) hK
  apply (P a).mem_purePVMReachable_of_quantumFootprint M hd hcap
  exact hscore.trans hs

/-- Original averaged-channel joint TV accuracy is converted before selecting randomness or resource components. -/
theorem mem_purePVMReachable_of_sharedRandom_quantumFootprint_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) (sharedRandomOperationalChannel μ P).toLinearMap ≤ ε) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  have hout := isPVMOutcomeChannel_of_completelyPositive_tracePreserving _
    (sharedRandomOperationalChannel_completelyPositive μ P hP) (sharedRandomOperationalChannel_tracePreserving μ P hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError
    (Matrix.mem_unitaryGroup_iff'.mp M.property) hout
  apply mem_purePVMReachable_of_sharedRandom_quantumFootprint μ P hP M hd hK
  linarith

/-- The original averaged mixed unitary Choi score gives an actual charged protocol. -/
theorem mem_pureReachable_of_mixedSharedRandom_quantumFootprint
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨a, k, hcap, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (unitaryScoreRealLinear (U : Matrix _ _ ℂ)) hK
  apply ((P a).componentProtocol (m a) k).mem_pureReachable_of_quantumFootprint U hd hcap
  exact hscore.trans hs

/-- Original averaged-channel diamond accuracy is converted before selecting randomness or resource components. -/
theorem mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (herror : diamondError (mixedSharedRandomOperationalChannel μ P m).toLinearMap (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  have htrace := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving _
    (mixedSharedRandomOperationalChannel_completelyPositive μ P m hP) (mixedSharedRandomOperationalChannel_tracePreserving μ P m hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError
    (Matrix.mem_unitaryGroup_iff'.mp U.property) (mixedSharedRandomOperationalChannel μ P m).toLinearMap htrace
  apply mem_pureReachable_of_mixedSharedRandom_quantumFootprint μ P m hP U hd hK
  linarith

/-- The original averaged mixed joint PVM score gives an actual charged protocol. -/
theorem mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨a, k, hcap, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (pvmScoreRealLinear (M : Matrix _ _ ℂ)) hK
  apply ((P a).componentProtocol (m a) k).mem_purePVMReachable_of_quantumFootprint M hd hcap
  exact hscore.trans hs

/-- Original averaged-channel joint TV accuracy is converted before selecting randomness or resource components. -/
theorem mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ ε) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  have hout := isPVMOutcomeChannel_of_completelyPositive_tracePreserving _
    (mixedSharedRandomOperationalChannel_completelyPositive μ P m hP) (mixedSharedRandomOperationalChannel_tracePreserving μ P m hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError
    (Matrix.mem_unitaryGroup_iff'.mp M.property) hout
  apply mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint μ P m hP M hd hK
  linarith

end

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol
