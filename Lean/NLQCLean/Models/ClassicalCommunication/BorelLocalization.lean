import NLQCLean.Models.ClassicalCommunication.BorelMixed
import NLQCLean.Models.ProjectiveScore

/-!
# Standard-Borel localization with measurable postprocessing

Alice and Bob measure their inputs together with their resource shares by
actual standard-Borel instruments with one-dimensional outputs (local POVMs),
do not communicate, and a fixed measurable function of both outcomes is the
reported label. The joint Born probability of an event `E ⊆ σA × σB` is the
integral over `E` of the trace of the joint operation density with respect to
the product of the two local trace probabilities.

Broadcasting both outcomes and outputting the reported label at both sides is
an actual standard-Borel protocol with free classical messages and
one-dimensional quantum messages. Its two-sided PVM score is exactly the
localization success probability, for pure and common-map mixed resources.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Kronecker Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance localizationMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup

noncomputable local instance localizationMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (localizationMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance borel_localization_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance borel_localization_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance localizationOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance localizationOperationComplexNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℂ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance localizationOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

local instance borel_localization_instance_3 {ν : Type*} [Fintype ν] :
    MeasurableSpace (Matrix ν ν ℂ) := borel (Matrix ν ν ℂ)

local instance borel_localization_instance_4 {ν : Type*} [Fintype ν] :
    BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance borel_localization_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance borel_localization_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

/-- Two one-dimensional factors form a one-dimensional system. -/
instance uniqueProdSelf {ω : Type*} [Unique ω] : Unique (ω × ω) := Unique.mk' _

section Label

variable {δ ν : Type*} [Fintype δ] [DecidableEq δ] [Fintype ν] [DecidableEq ν]

/-- Preparation of a classical label from a one-dimensional system. -/
def labelColumn (j : δ) : Matrix δ ν ℂ := fun a _ => if a = j then 1 else 0

omit [Fintype ν] in
theorem labelColumn_isometry [Unique ν] (j : δ) : IsIsometry (labelColumn (ν := ν) j) := by
  change (labelColumn j)ᴴ * labelColumn j = 1
  ext u v
  rw [Subsingleton.elim u v]
  simp [labelColumn, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The label preparation channel, as an actual operation. -/
def labelPreparation (j : δ) : MatrixOperation ν δ :=
  (adConj (labelColumn (ν := ν) j)).toContinuousLinearMap

theorem labelPreparation_completelyPositive (j : δ) :
    CompletelyPositive (labelPreparation (ν := ν) j).toLinearMap :=
  completelyPositive_adConj _

theorem labelPreparation_trace [Unique ν] (j : δ) (X : Matrix ν ν ℂ) :
    (labelPreparation (ν := ν) j X).trace = X.trace :=
  trace_adConj_isometry (labelColumn_isometry j) X

end Label

section Scores

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The real part of a fixed diagonal output entry on a fixed input. -/
def entryRealLinear (Y : Matrix ι ι ℂ) (p : κ) :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ where
  toFun Φ := (Φ Y p p).re
  map_add' Φ Ψ := by simp
  map_smul' r Φ := by simp

/-- The real part of the output trace on a fixed input. -/
def traceRealLinear (Y : Matrix ι ι ℂ) :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ where
  toFun Φ := (Φ Y).trace.re
  map_add' Φ Ψ := by simp [Matrix.trace_add]
  map_smul' r Φ := by simp [Matrix.trace_smul]

end Scores

/-- A standard-Borel localization scheme: two local instruments with
one-dimensional outputs (local POVMs on input and resource share) and a
measurable reporting function of both outcomes. -/
structure BorelLocalizationScheme (ιA ιB ρA ρB σA σB δ ω : Type*)
    [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [Fintype ω]
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ω]
    [Unique ω] [MeasurableSpace σA] [MeasurableSpace σB] where
  povmA : CPVectorInstrument σA (ιA × ρA) (ω × ω)
  povmB : CPVectorInstrument σB (ιB × ρB) (ω × ω)
  report : σA × σB → δ
  measurableSet_report : ∀ i, MeasurableSet (report ⁻¹' {i})

namespace BorelLocalizationScheme

variable {ιA ιB ρA ρB σA σB δ ω : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [Fintype ω]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ω]
variable [Unique ω] [Fintype δ] [DecidableEq δ]
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable (L : BorelLocalizationScheme ιA ιB ρA ρB σA σB δ ω)

omit [StandardBorelSpace σA] [StandardBorelSpace σB] in
theorem measurable_labelPreparation_report :
    Measurable (fun z => labelPreparation (ν := ω × ω) (L.report z)) := by
  let : MeasurableSpace δ := ⊤
  have hr : Measurable L.report := measurable_to_countable' L.measurableSet_report
  exact (show Measurable (fun j : δ => labelPreparation (ν := ω × ω) j) from
    measurable_from_top).comp hr

/-- Broadcast both outcomes and output the reported label at both sides. -/
def protocol (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) :
    StandardBorelClassicalProtocol ιA ιB ρA ρB ω ω ω ω σA σB δ δ where
  resource := γ
  resource_unit := hγ
  instrumentA := L.povmA
  instrumentB := L.povmB
  decA z := labelPreparation (L.report z)
  decB z := labelPreparation (L.report z)
  decA_choiMeasurable := (measurable_unnormalizedChoi_iff _).mpr L.measurable_labelPreparation_report
  decB_choiMeasurable := (measurable_unnormalizedChoi_iff _).mpr L.measurable_labelPreparation_report
  decA_completelyPositive z := labelPreparation_completelyPositive (ν := ω × ω) (L.report z)
  decB_completelyPositive z := labelPreparation_completelyPositive (ν := ω × ω) (L.report z)
  decA_tracePreserving z X := labelPreparation_trace (ν := ω × ω) (L.report z) X
  decB_tracePreserving z X := labelPreparation_trace (ν := ω × ω) (L.report z) X

/-- Only the resource Schmidt rank is charged: both quantum messages are one-dimensional. -/
theorem protocol_hasQuantumFootprint_iff (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) (K : ℕ) :
    (L.protocol γ hγ).HasQuantumFootprint K ↔ schmidtRank γ ≤ K := by
  change HasFootprint K γ ω ω ↔ _
  rw [hasFootprint_iff, Fintype.card_unique, mul_one, mul_one]

theorem protocol_withResource (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (η : ρA × ρB → ℂ) (hη : IsUnitVector η) :
    (L.protocol γ hγ).withResource η hη = L.protocol η hη := rfl

theorem protocol_hasMixedQuantumFootprint_iff (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    {n : ℕ} (m : MixedResource ρA ρB n) (r : ℕ) :
    (L.protocol γ hγ).HasMixedQuantumFootprint m r ↔ m.schmidtNumberLE r := by
  constructor
  · rintro ⟨R, hR, hK⟩ k
    simp only [Fintype.card_unique, mul_one] at hK
    exact (hR k).trans hK
  · intro hr
    exact ⟨r, hr, by simp only [Fintype.card_unique, mul_one, le_refl]⟩

/-- The joint decoder at the outcome pair `z` prepares the reported label at
both sides with the trace of its one-dimensional input. -/
theorem protocol_jointDecoder_diag (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (z : σA × σB) (W : Matrix ((ω × ω) × (ω × ω)) ((ω × ω) × (ω × ω)) ℂ) (a b : δ) :
    ((L.protocol γ hγ).jointDecoder z W) (a, b) (a, b) =
      if a = L.report z ∧ b = L.report z then W.trace else 0 := by
  have hJ : ((L.protocol γ hγ).jointDecoder z).toLinearMap =
      adConj ((labelColumn (ν := ω × ω) (L.report z) ⊗ₖ
        labelColumn (ν := ω × ω) (L.report z)) * exchangeMatrix ω ω ω ω) := by
    change (tensorChannels (adConj (labelColumn (L.report z)))
      (adConj (labelColumn (L.report z)))).comp (adConj (exchangeMatrix ω ω ω ω)) = _
    rw [tensorChannels_adConj, adConj_mul_eq_comp]
  have hW := congrArg (fun Φ => Φ W (a, b) (a, b)) hJ
  change ((L.protocol γ hγ).jointDecoder z).toLinearMap W (a, b) (a, b) = _
  rw [hW]
  have hsub : ∀ x y : (ω × ω) × (ω × ω), (x = y) = True :=
    fun x y => eq_true (Subsingleton.elim x y)
  simp [adConj_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, labelColumn, exchangeMatrix, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.trace, hsub]
  by_cases ha : a = L.report z <;> by_cases hb : b = L.report z <;> simp [ha, hb]

variable [Nonempty ιA] [Nonempty ιB]

/-- The joint Born density of an input matrix at the outcome pair `z`, with
respect to the product of the two local trace probabilities. -/
def bornDensity (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (z : σA × σB) : ℝ :=
  (Matrix.trace (tensorContinuousChannels ((L.protocol γ hγ).densityA z.1)
    ((L.protocol γ hγ).densityB z.2) ((L.protocol γ hγ).resourceInsertion X))).re

/-- The joint Born probability of an outcome event. -/
def bornProbability (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (E : Set (σA × σB)) : ℝ :=
  ∫ z in E, L.bornDensity γ hγ X z
    ∂((L.protocol γ hγ).probabilityA.prod (L.protocol γ hγ).probabilityB)

/-- Localization success probability on the ordered target basis: the average
over basis inputs of the Born probability that the reported label is correct. -/
def successScore (L : BorelLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB) ω)
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  (Fintype.card (ιA × ιB) : ℝ)⁻¹ *
    ∑ i, L.bornProbability γ hγ (pvmProj M i) (L.report ⁻¹' {i})

/-- Common-map mixed localization success. -/
def mixedSuccessScore (L : BorelLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB) ω)
    {n : ℕ} (m : MixedResource ρA ρB n) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  ∑ k, m.weight k * L.successScore (m.component k) (m.component_unit k) M

/-- The Born density is the trace score of the actual joint branch operation,
because both final label preparations preserve trace. -/
theorem bornDensity_eq_jointScore (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    L.bornDensity γ hγ X = (L.protocol γ hγ).jointScore
      (continuousMatrixOperationRealScore (traceRealLinear X)) := by
  funext z
  change _ = ((L.protocol γ hγ).jointDecoder z (tensorContinuousChannels
    ((L.protocol γ hγ).densityA z.1) ((L.protocol γ hγ).densityB z.2)
      ((L.protocol γ hγ).resourceInsertion X))).trace.re
  rw [StandardBorelClassicalProtocol.jointDecoder_tracePreserving]
  rfl

theorem integrable_bornDensity (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    Integrable (L.bornDensity γ hγ X)
      ((L.protocol γ hγ).probabilityA.prod (L.protocol γ hγ).probabilityB) := by
  rw [L.bornDensity_eq_jointScore]
  exact (L.protocol γ hγ).integrable_jointScore _

/-- **Born rule on rectangles.** The joint Born probability of a measurable
rectangle is the trace of the actual local operation masses `E_A(S) ⊗ E_B(T)`
applied to the input with the inserted resource. -/
theorem bornProbability_prod (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) {S : Set σA} {T : Set σB}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    L.bornProbability γ hγ X (S ×ˢ T) =
      (Matrix.trace (tensorContinuousChannels (L.povmA.operationMeasure S)
        (L.povmB.operationMeasure T) ((L.protocol γ hγ).resourceInsertion X))).re := by
  let P := L.protocol γ hγ
  obtain ⟨-, hAi, hAr, -, -⟩ := P.densityA_spec
  obtain ⟨-, hBi, hBr, -, -⟩ := P.densityB_spec
  let Λ := continuousMatrixOperationRealScore
    (traceRealLinear (κ := (ω × ω) × (ω × ω)) (P.resourceInsertion X))
  let B := tensorContinuousChannelsRealBilinear (ι := ιA × ρA) (κ := ω × ω)
    (τ := ιB × ρB) (υ := ω × ω)
  have hdens : L.bornDensity γ hγ X = fun z => Λ (B (P.densityA z.1) (P.densityB z.2)) := rfl
  have hint : Integrable (L.bornDensity γ hγ X)
      ((P.probabilityA.restrict S).prod (P.probabilityB.restrict T)) := by
    rw [Measure.prod_restrict]
    exact (L.integrable_bornDensity γ hγ X).integrableOn
  have hA : ∫ x in S, P.densityA x ∂P.probabilityA = L.povmA.operationMeasure S := by
    rw [← withDensityᵥ_apply hAi hS]
    exact congrArg (fun v => v S) hAr
  have hB : ∫ y in T, P.densityB y ∂P.probabilityB = L.povmB.operationMeasure T := by
    rw [← withDensityᵥ_apply hBi hT]
    exact congrArg (fun v => v T) hBr
  unfold bornProbability
  change ∫ z, L.bornDensity γ hγ X z ∂(P.probabilityA.prod P.probabilityB).restrict (S ×ˢ T) = _
  rw [← Measure.prod_restrict, integral_prod _ hint, hdens]
  have hinner : ∀ x, ∫ y, Λ (B (P.densityA x) (P.densityB y)) ∂P.probabilityB.restrict T =
      (Λ.comp (B.flip (L.povmB.operationMeasure T))) (P.densityA x) := by
    intro x
    rw [← hB]
    exact (Λ.comp (B (P.densityA x))).integral_comp_comm hBi.integrableOn
  simp only [hinner]
  rw [(Λ.comp (B.flip (L.povmB.operationMeasure T))).integral_comp_comm hAi.integrableOn, hA]
  rfl

/-- A diagonal label entry of the joint branch is the Born density on the
event that this label is reported. -/
theorem jointScore_entry (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (Y : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) (z : σA × σB) :
    (L.protocol γ hγ).jointScore (continuousMatrixOperationRealScore (entryRealLinear Y (i, i))) z =
      Set.indicator (L.report ⁻¹' {i}) (L.bornDensity γ hγ Y) z := by
  change ((L.protocol γ hγ).jointDecoder z (tensorContinuousChannels
    ((L.protocol γ hγ).densityA z.1) ((L.protocol γ hγ).densityB z.2)
      ((L.protocol γ hγ).resourceInsertion Y)) (i, i) (i, i)).re = _
  rw [L.protocol_jointDecoder_diag]
  by_cases h : i = L.report z
  · rw [ite_eq_left ⟨h, h⟩, Set.indicator_of_mem (by simp [h])]
    rfl
  · rw [ite_eq_right (fun hh => h hh.1), Set.indicator_of_notMem (by simpa [eq_comm] using h)]
    simp

/-- Each diagonal label entry of the operational channel is the Born
probability that this label is reported. -/
theorem operationalChannel_entry (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (Y : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) :
    ((L.protocol γ hγ).operationalChannel.toLinearMap Y (i, i) (i, i)).re =
      L.bornProbability γ hγ Y (L.report ⁻¹' {i}) := by
  have h := (L.protocol γ hγ).linearScore_operationalChannel (entryRealLinear Y (i, i))
  change entryRealLinear Y (i, i) (L.protocol γ hγ).operationalChannel.toLinearMap = _
  rw [h]
  simp_rw [L.jointScore_entry]
  exact integral_indicator (L.measurableSet_report i)

/-- **Localization score.** The broadcast protocol's two-sided PVM score is
exactly the Born success probability of the localization. -/
theorem protocol_scorePVM (L : BorelLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB) ω)
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    scorePVM M (L.protocol γ hγ).operationalChannel.toLinearMap = L.successScore γ hγ M := by
  simp only [scorePVM, successScore, L.operationalChannel_entry]

/-- Mixed localization success is the mixed broadcast protocol's PVM score. -/
theorem protocol_mixedScorePVM (L : BorelLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB) ω)
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    scorePVM M ((L.protocol γ hγ).mixedOperationalChannel m) = L.mixedSuccessScore m M := by
  rw [← pvmScoreRealLinear_apply,
    StandardBorelClassicalProtocol.linearScore_mixedOperationalChannel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pvmScoreRealLinear_apply]
  exact congrArg (m.weight k * ·) (L.protocol_scorePVM _ _ M)

end BorelLocalizationScheme

end

end NLQCLean.ClassicalCommunication
