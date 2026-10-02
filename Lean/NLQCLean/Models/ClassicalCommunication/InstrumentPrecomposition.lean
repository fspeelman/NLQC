import NLQCLean.Models.ClassicalCommunication.DensityCompression
import NLQCLean.Models.ClassicalCommunication.StandardBorelProtocol

/-!
# Isometric input precomposition of actual CP instruments

Precomposing every actual operation mass with an input isometry gives a
countably additive normalized CP instrument on the smaller input system.
Its trace probability need not equal the old probability. The exact change
of measure is derived from the trace of the precomposed actual density.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise NNReal ENNReal

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance precompositionMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance precompositionMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (precompositionMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance instrument_precomposition_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance instrument_precomposition_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance instrument_precomposition_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instrument_precomposition_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℂ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

noncomputable local instance instrument_precomposition_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

local instance instrument_precomposition_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance instrument_precomposition_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

local instance instrument_precomposition_instance_8 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional

local instance instrument_precomposition_instance_9 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : CompleteSpace (MatrixOperation ι κ) :=
  FiniteDimensional.complete ℝ (MatrixOperation ι κ)

variable {α ι κ τ : Type*}
variable [Fintype ι] [Fintype κ] [Fintype τ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

/-- Actual input precomposition is a real-linear map of operations. -/
def operationPrecompositionRealLinear (E : Matrix ι τ ℂ) :
    MatrixOperation ι κ →ₗ[ℝ] MatrixOperation τ κ where
  toFun Φ := Φ.comp (adConj E).toContinuousLinearMap
  map_add' _Φ _Ψ := ContinuousLinearMap.add_comp _ _ _
  map_smul' _r _Φ := ContinuousLinearMap.smul_comp _ _ _

/-- Finite-dimensional continuity permits honest vector-measure transport. -/
def operationPrecompositionContinuousRealLinear (E : Matrix ι τ ℂ) :
    MatrixOperation ι κ →L[ℝ] MatrixOperation τ κ :=
  (operationPrecompositionRealLinear E).toContinuousLinearMap

omit [DecidableEq τ] in
@[simp] theorem operationPrecompositionContinuousRealLinear_apply
    (E : Matrix ι τ ℂ) (Φ : MatrixOperation ι κ) :
    operationPrecompositionContinuousRealLinear E Φ =
      Φ.comp (adConj E).toContinuousLinearMap := rfl

/-- The real trace density relative to the new input dimension. -/
def precompositionTraceRealLinear (E : Matrix ι τ ℂ) :
    MatrixOperation ι κ →L[ℝ] ℝ :=
  (((Fintype.card τ : ℝ)⁻¹ • matrixRealTraceLinear (κ × τ)).toContinuousLinearMap).comp
    ((unnormalizedChoiContinuousRealLinearEquiv (ι := τ) (κ := κ)).toContinuousLinearMap.comp
      (operationPrecompositionContinuousRealLinear E))

@[simp] theorem precompositionTraceRealLinear_apply
    (E : Matrix ι τ ℂ) (Φ : MatrixOperation ι κ) :
    precompositionTraceRealLinear E Φ = (Fintype.card τ : ℝ)⁻¹ *
      (unnormalizedChoiMatrix (Φ.comp (adConj E).toContinuousLinearMap).toLinearMap).trace.re := rfl

/-- Positive-part trace weight is defined at every actual outcome; it agrees
with the normalized trace almost everywhere for actual CP densities. -/
def precompositionTraceWeight (E : Matrix ι τ ℂ) (Φ : α → MatrixOperation ι κ) :
    α → ℝ≥0 := fun x => Real.toNNReal (precompositionTraceRealLinear E (Φ x))

/-- The literal trace-normalized precomposed operation, including the
zero-trace convention. The same actual outcomes and original density version
are retained. -/
def normalizedPrecompositionDensity
    (E : Matrix ι τ ℂ) (Φ : α → MatrixOperation ι κ) : α → MatrixOperation τ κ :=
  fun x => (precompositionTraceWeight E Φ x : ℝ)⁻¹ •
    operationPrecompositionContinuousRealLinear E (Φ x)

/-- Complete positivity gives nonnegative trace weight on the new input. -/
theorem precompositionTraceRealLinear_nonneg [Nonempty τ]
    (E : Matrix ι τ ℂ) (Φ : MatrixOperation ι κ)
    (hΦ : CompletelyPositive Φ.toLinearMap) :
    0 ≤ precompositionTraceRealLinear E Φ := by
  have hCP := hΦ.comp (completelyPositive_adConj E)
  have hPSD := (completelyPositive_iff_unnormalizedChoi_posSemidef _).mp hCP
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Complex.nonneg_iff.mp hPSD.trace_nonneg).1

/-- A positive precomposed operation with zero trace weight is the zero
operation, by the actual Choi equivalence and PSD trace-null criterion. -/
theorem operationPrecomposition_eq_zero_of_trace_eq_zero [Nonempty τ]
    (E : Matrix ι τ ℂ) (Φ : MatrixOperation ι κ)
    (hΦ : CompletelyPositive Φ.toLinearMap)
    (hzero : precompositionTraceRealLinear E Φ = 0) :
    operationPrecompositionContinuousRealLinear E Φ = 0 := by
  have hCP := hΦ.comp (completelyPositive_adConj E)
  have hPSD := (completelyPositive_iff_unnormalizedChoi_posSemidef _).mp hCP
  have hcard : (Fintype.card τ : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have hre : (unnormalizedChoiMatrix
      (Φ.comp (adConj E).toContinuousLinearMap).toLinearMap).trace.re = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hcard
  have htrace : (unnormalizedChoiMatrix
      (Φ.comp (adConj E).toContinuousLinearMap).toLinearMap).trace = 0 :=
    Complex.ext hre (Complex.nonneg_iff.mp hPSD.trace_nonneg).2.symm
  apply (unnormalizedChoiContinuousRealLinearEquiv (ι := τ) (κ := κ)).injective
  rw [map_zero]
  exact hPSD.trace_eq_zero_iff.mp htrace

variable [MeasurableSpace α]

/-- The trace weight of an actually measurable density is measurable. -/
theorem measurable_precompositionTraceWeight
    (E : Matrix ι τ ℂ) (Φ : α → MatrixOperation ι κ) (hΦ : Measurable Φ) :
    Measurable (precompositionTraceWeight E Φ) :=
  measurable_real_toNNReal.comp
    ((precompositionTraceRealLinear (κ := κ) E).continuous.measurable.comp hΦ)

/-- Literal trace normalization remains actually measurable, not just an
almost-everywhere equivalence class. -/
theorem measurable_normalizedPrecompositionDensity
    (E : Matrix ι τ ℂ) (Φ : α → MatrixOperation ι κ) (hΦ : Measurable Φ) :
    Measurable (normalizedPrecompositionDensity E Φ) :=
  (measurable_precompositionTraceWeight E Φ hΦ).coe_nnreal_real.inv.smul
    ((operationPrecompositionContinuousRealLinear (κ := κ) E).continuous.measurable.comp hΦ)

namespace CPVectorInstrument

/-- Precomposition by an actual input isometry transports every original
operation mass and preserves complete positivity and total normalization. -/
def precomposeIsometry (I : CPVectorInstrument α ι κ)
    (E : Matrix ι τ ℂ) (hE : IsIsometry E) : CPVectorInstrument α τ κ where
  operationMeasure :=
    let L := operationPrecompositionContinuousRealLinear E
    I.operationMeasure.mapRange L.toLinearMap.toAddMonoidHom L.continuous
  completelyPositive S hS :=
    (I.completelyPositive S hS).comp (completelyPositive_adConj E)
  tracePreserving_total X := by
    change ((I.operationMeasure univ) (adConj E X)).trace = X.trace
    rw [I.tracePreserving_total]
    exact trace_adConj_isometry hE X

@[simp] theorem precomposeIsometry_operationMeasure_apply
    (I : CPVectorInstrument α ι κ) (E : Matrix ι τ ℂ) (hE : IsIsometry E)
    (S : Set α) :
    (I.precomposeIsometry E hE).operationMeasure S =
      (I.operationMeasure S).comp (adConj E).toContinuousLinearMap := rfl

/-- The precomposed density reconstructs the transported instrument under
the old probability before any trace reweighting. -/
theorem withDensity_operationPrecomposition [Nonempty ι]
    (I : CPVectorInstrument α ι κ) (E : Matrix ι τ ℂ) (hE : IsIsometry E)
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure) :
    I.traceProbability.withDensityᵥ
      (fun x => operationPrecompositionContinuousRealLinear E (Φ x)) =
        (I.precomposeIsometry E hE).operationMeasure := by
  let L := operationPrecompositionContinuousRealLinear (κ := κ) E
  apply VectorMeasure.ext
  intro S hS
  rw [withDensityᵥ_apply (L.integrable_comp hΦ) hS,
    L.integral_comp_comm hΦ.integrableOn]
  have hm := congrArg (fun v => v S) hrep
  rw [withDensityᵥ_apply hΦ hS] at hm
  rw [hm]
  rfl

/-- The new trace probability is exactly the original probability weighted
by the trace of the actual precomposed density. It is generally not the old
probability measure. -/
theorem traceProbability_precomposeIsometry [Nonempty ι] [Nonempty τ]
    (I : CPVectorInstrument α ι κ) (E : Matrix ι τ ℂ) (hE : IsIsometry E)
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure) :
    (I.precomposeIsometry E hE).traceProbability =
      I.traceProbability.withDensity (fun x => ENNReal.ofReal
        (precompositionTraceRealLinear E (Φ x))) := by
  let J := I.precomposeIsometry E hE
  let Q := precompositionTraceRealLinear (κ := κ) E
  obtain ⟨hgood, _⟩ := I.reconstructed_density_normalized Φ hΦ hrep
  have hnonneg : ∀ᵐ x ∂I.traceProbability, 0 ≤ Q (Φ x) :=
    hgood.mono fun x hx => precompositionTraceRealLinear_nonneg E (Φ x) hx.1
  apply Measure.ext
  intro S hS
  rw [← ofReal_measureReal (μ := J.traceProbability) (s := S) (measure_ne_top _ _)]
  change ENNReal.ofReal (J.toChoiInstrument.traceProbability.real S) = _
  rw [J.toChoiInstrument.traceProbability_real_apply hS,
    withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal
      (Q.integrable_comp hΦ).integrableOn (ae_restrict_of_ae hnonneg)]
  congr 1
  rw [Q.integral_comp_comm hΦ.integrableOn]
  have hm := congrArg (fun v => v S) hrep
  rw [withDensityᵥ_apply hΦ hS] at hm
  rw [hm]
  rfl

/-- Trace weighting cancels literal normalization on the original
probability almost everywhere. Zero weight implies a zero actual operation,
so cancellation does not discard a nonzero CP branch. -/
theorem ae_precompositionTraceWeight_smul_normalizedDensity [Nonempty ι] [Nonempty τ]
    (I : CPVectorInstrument α ι κ) (E : Matrix ι τ ℂ)
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure) :
    (fun x => (precompositionTraceWeight E Φ x : ℝ) • normalizedPrecompositionDensity E Φ x)
      =ᵐ[I.traceProbability] fun x => operationPrecompositionContinuousRealLinear E (Φ x) := by
  obtain ⟨hgood, _⟩ := I.reconstructed_density_normalized Φ hΦ hrep
  filter_upwards [hgood] with x hx
  let q : ℝ := precompositionTraceWeight E Φ x
  let F := operationPrecompositionContinuousRealLinear E (Φ x)
  have hq : q = precompositionTraceRealLinear E (Φ x) :=
    Real.coe_toNNReal _ (precompositionTraceRealLinear_nonneg E (Φ x) hx.1)
  change q • (q⁻¹ • F) = F
  by_cases hz : q = 0
  · have hF : F = 0 := operationPrecomposition_eq_zero_of_trace_eq_zero
      E (Φ x) hx.1 (hq.symm.trans hz)
    have hzero (r : ℝ) : r • (0 : MatrixOperation τ κ) = 0 :=
      (instrument_precomposition_instance_5 (ι := τ) (κ := κ)).toModule.toDistribMulAction.smul_zero r
    rw [hF, hzero, hzero]
  · rw [smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- Actual input precomposition has a literal measurable normalized density
under its changed trace probability, with proved integrability and exact
reconstruction of all original outcome masses. -/
theorem normalizedPrecompositionDensity_spec [Nonempty ι] [Nonempty τ]
    (I : CPVectorInstrument α ι κ) (E : Matrix ι τ ℂ) (hE : IsIsometry E)
    (Φ : α → MatrixOperation ι κ) (hΦmeas : Measurable Φ)
    (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure) :
    Measurable (normalizedPrecompositionDensity E Φ) ∧
      Integrable (normalizedPrecompositionDensity E Φ)
        (I.precomposeIsometry E hE).traceProbability ∧
      (I.precomposeIsometry E hE).traceProbability.withDensityᵥ
        (normalizedPrecompositionDensity E Φ) = (I.precomposeIsometry E hE).operationMeasure := by
  let q := precompositionTraceWeight E Φ
  let g := normalizedPrecompositionDensity E Φ
  let L := operationPrecompositionContinuousRealLinear (κ := κ) E
  have hqmeas : Measurable q := measurable_precompositionTraceWeight E Φ hΦmeas
  have hcancel := I.ae_precompositionTraceWeight_smul_normalizedDensity E Φ hΦ hrep
  have hweighted : Integrable (fun x => (q x : ℝ) • g x) I.traceProbability :=
    (L.integrable_comp hΦ).congr hcancel.symm
  have hmeasure : (I.precomposeIsometry E hE).traceProbability =
      I.traceProbability.withDensity (fun x => (q x : ℝ≥0∞)) := by
    simpa only [q, precompositionTraceWeight, ENNReal.ofReal] using
      I.traceProbability_precomposeIsometry E hE Φ hΦ hrep
  refine ⟨measurable_normalizedPrecompositionDensity E Φ hΦmeas, ?_, ?_⟩
  · rw [hmeasure]
    exact (integrable_withDensity_iff_integrable_coe_smul hqmeas).mpr hweighted
  · rw [hmeasure]
    have hqg : (q • g) = fun x => (q x : ℝ) • g x :=
      funext fun x => NNReal.smul_def (q x) (g x)
    have hweightedNN : Integrable (q • g) I.traceProbability := hqg ▸ hweighted
    have hcancelNN : (q • g) =ᵐ[I.traceProbability] fun x => L (Φ x) := hqg ▸ hcancel
    exact (withDensityᵥ_smul_eq_withDensityᵥ_withDensity hqmeas.aemeasurable hweightedNN).symm.trans
      ((WithDensityᵥEq.congr_ae hcancelNN).trans
        (I.withDensity_operationPrecomposition E hE Φ hΦ hrep))

end CPVectorInstrument

end

end NLQCLean.ClassicalCommunication
