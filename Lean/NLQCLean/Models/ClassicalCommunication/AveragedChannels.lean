import NLQCLean.Models.ClassicalCommunication.BorelMixedCompression
import NLQCLean.Models.ClassicalCommunication.BranchSelection

/-!
# Actual channel averages under arbitrary probability randomness

A measurable family of finite-dimensional CP/TP channels is integrable by
the proved norm bound depending only on its logical input and output systems.
Its Bochner average is CP/TP, acts by averaging every input matrix, and has
exactly the average of each prescribed real-linear channel score.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix
open scoped MeasureTheory Matrix.Norms.Elementwise ComplexOrder

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance averagedMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance averagedMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (averagedMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance averagedMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance averagedMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance averagedOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance averagedOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

local instance averagedOperationMeasurableSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel _

local instance averagedOperationBorelSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

local instance averagedOperationFiniteDimensional
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional

local instance averagedOperationCompleteSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    CompleteSpace (MatrixOperation ι κ) := FiniteDimensional.complete ℝ _

variable {α ι κ : Type*} [MeasurableSpace α]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (μ : Measure α) [IsProbabilityMeasure μ]

/-- The actual operation-valued Bochner average. -/
def averageOperationalChannel (Φ : α → MatrixOperation ι κ) : MatrixOperation ι κ :=
  ∫ a, Φ a ∂μ

/-- CP/TP and measurability imply integrability under probability randomness;
no resource, private-register or outcome-cardinality bound is used. -/
theorem integrable_completelyPositive_tracePreserving_family [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace) : Integrable Φ μ := by
  obtain ⟨B, _, hbound⟩ := exists_completelyPositive_tracePreserving_norm_bound ι κ
  apply (integrable_const B).mono' hΦ
  filter_upwards [hCP, hTP] with a haCP haTP
  exact hbound (Φ a) haCP haTP

/-- Ordinary measurable actual channel families satisfy the same derived
integrability statement. -/
theorem integrable_measurable_completelyPositive_tracePreserving_family [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : Measurable Φ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace) : Integrable Φ μ :=
  integrable_completelyPositive_tracePreserving_family μ Φ hΦ.aestronglyMeasurable hCP hTP

/-- Every prescribed real-linear score is integrable for an actual CP/TP
channel family, as a continuous functional of its derived integrable channel. -/
theorem integrable_linearScore_completelyPositive_tracePreserving_family [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace)
    (S : (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ) :
    Integrable (fun a => S (Φ a).toLinearMap) μ :=
  (continuousMatrixOperationRealScore S).integrable_comp
    (integrable_completelyPositive_tracePreserving_family μ Φ hΦ hCP hTP)

private def averageOperationAt (X : Matrix ι ι ℂ) :
    MatrixOperation ι κ →L[ℝ] Matrix κ κ ℂ :=
  (show MatrixOperation ι κ →ₗ[ℝ] Matrix κ κ ℂ from
    { toFun := fun Φ => Φ X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

omit [IsProbabilityMeasure μ] in
/-- The average is the actual channel on every input matrix, with the
operation-valued and matrix-valued Bochner averages identified. -/
theorem averageOperationalChannel_apply
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ μ) (X : Matrix ι ι ℂ) :
    averageOperationalChannel μ Φ X = ∫ a, Φ a X ∂μ := by
  exact ((averageOperationAt (κ := κ) X).integral_comp_comm hΦ).symm

omit [IsProbabilityMeasure μ] in
/-- The original averaged channel has exactly the mean prescribed score. -/
theorem linearScore_averageOperationalChannel
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ μ)
    (S : (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ) :
    S (averageOperationalChannel μ Φ).toLinearMap = ∫ a, S (Φ a).toLinearMap ∂μ :=
  ((continuousMatrixOperationRealScore S).integral_comp_comm hΦ).symm

/-- Complete positivity of the averaged actual channel is derived. -/
theorem averageOperationalChannel_completelyPositive [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace) :
    CompletelyPositive (averageOperationalChannel μ Φ).toLinearMap :=
  completelyPositive_integral
    (integrable_completelyPositive_tracePreserving_family μ Φ hΦ hCP hTP) hCP

/-- Every matrix trace is preserved by the probability-average channel. -/
theorem averageOperationalChannel_tracePreserving [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace) (X : Matrix ι ι ℂ) :
    (averageOperationalChannel μ Φ X).trace = X.trace := by
  have hi := integrable_completelyPositive_tracePreserving_family μ Φ hΦ hCP hTP
  change operationTraceAt X (∫ a, Φ a ∂μ) = X.trace
  rw [← (operationTraceAt X).integral_comp_comm hi]
  have hae : (fun a => operationTraceAt X (Φ a)) =ᵐ[μ] fun _ => X.trace := by
    filter_upwards [hTP] with a ha
    exact ha X
  rw [integral_congr_ae hae]
  simp

/-- Any actual finite-dimensional CP/TP channel has normalized Choi trace one. -/
theorem trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving [Nonempty ι]
    (Γ : MatrixOperation ι κ) (hCP : CompletelyPositive Γ.toLinearMap)
    (hTP : ∀ X, (Γ X).trace = X.trace) : (choiMatrix Γ.toLinearMap).trace = 1 := by
  have h := trace_choiMatrix_channelOf_eq_one (operationStinespring_isometry Γ hCP hTP)
  rwa [channelOf_operationStinespring] at h

/-- Normalized Choi infidelity of the original average is dominated by its
normalized diamond error. -/
theorem one_sub_scoreU_averageOperationalChannel_le_diamondError [Nonempty ι]
    (Φ : α → MatrixOperation ι κ) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace)
    {U : Matrix κ ι ℂ} (hU : IsIsometry U) :
    1 - scoreU U (averageOperationalChannel μ Φ).toLinearMap ≤
      diamondError (averageOperationalChannel μ Φ).toLinearMap (adConj U) :=
  NLQCLean.one_sub_scoreU_le_diamondError hU _
    (trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving _
      (averageOperationalChannel_completelyPositive μ Φ hΦ hCP hTP)
      (averageOperationalChannel_tracePreserving μ Φ hΦ hCP hTP))

/-- Every CP/TP channel with both PVM output labels gives physical joint
probabilities on every density-matrix input. -/
theorem isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    {δ : Type*} [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (Γ : MatrixOperation δ (δ × δ)) (hCP : CompletelyPositive Γ.toLinearMap)
    (hTP : ∀ X, (Γ X).trace = X.trace) : IsPVMOutcomeChannel Γ.toLinearMap := by
  constructor
  · intro ρ hρ ab
    have hp : (Γ ρ).PosSemidef := by
      obtain ⟨A, hA⟩ := exists_kraus_of_completelyPositive Γ.toLinearMap hCP
      change (Γ.toLinearMap ρ).PosSemidef
      rw [hA, krausMap_apply]
      exact Matrix.posSemidef_sum _ (fun e _ => hρ.1.mul_mul_conjTranspose_same (A e))
    exact (Complex.nonneg_iff.mp (hp.diag_nonneg (i := ab))).1
  · intro ρ hρ
    change ∑ ab, (Γ ρ ab ab).re = 1
    rw [← Complex.re_sum]
    change (Γ ρ).trace.re = 1
    rw [hTP, hρ.2]
    rfl

/-- The original probability-average channel retains physical joint PVM
statistics, before any high-score branch is selected. -/
theorem isPVMOutcomeChannel_averageOperationalChannel
    {δ : Type*} [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (Φ : α → MatrixOperation δ (δ × δ)) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace) :
    IsPVMOutcomeChannel (averageOperationalChannel μ Φ).toLinearMap :=
  isPVMOutcomeChannel_of_completelyPositive_tracePreserving _
    (averageOperationalChannel_completelyPositive μ Φ hΦ hCP hTP)
    (averageOperationalChannel_tracePreserving μ Φ hΦ hCP hTP)

/-- Worst-case joint TV of the original averaged channel dominates its
average two-sided correct-label infidelity. -/
theorem one_sub_scorePVM_averageOperationalChannel_le_pvmTVError
    {δ : Type*} [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (Φ : α → MatrixOperation δ (δ × δ)) (hΦ : AEStronglyMeasurable Φ μ)
    (hCP : ∀ᵐ a ∂μ, CompletelyPositive (Φ a).toLinearMap)
    (hTP : ∀ᵐ a ∂μ, ∀ X, (Φ a X).trace = X.trace)
    {M : Matrix δ δ ℂ} (hM : IsIsometry M) :
    1 - scorePVM M (averageOperationalChannel μ Φ).toLinearMap ≤
      pvmTVError M (averageOperationalChannel μ Φ).toLinearMap :=
  NLQCLean.one_sub_scorePVM_le_pvmTVError hM
    (isPVMOutcomeChannel_averageOperationalChannel μ Φ hΦ hCP hTP)

end

end NLQCLean.ClassicalCommunication
