import NLQCLean.Models.ClassicalCommunication.ChoiInstrumentDensities

/-!
# Countably additive positive Choi instruments

A Choi instrument is an actual matrix-valued vector measure, positive on
measurable sets, whose total input marginal is the identity. Its trace
probability measure and absolute continuity are derived from those
properties. In particular no probability or density representation is
assumed as a field.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

variable {α ι κ : Type*} [MeasurableSpace α]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable local instance choiMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (κ × ι) (κ × ι) ℂ) := Matrix.normedAddCommGroup

noncomputable local instance choiMatrixTopologicalSpace :
    TopologicalSpace (Matrix (κ × ι) (κ × ι) ℂ) :=
  (choiMatrixNormedAddCommGroup (ι := ι) (κ := κ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance : MeasurableSpace (Matrix (κ × ι) (κ × ι) ℂ) :=
  borel (Matrix (κ × ι) (κ × ι) ℂ)

noncomputable local instance : ContinuousENorm (Matrix (κ × ι) (κ × ι) ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix (κ × ι) (κ × ι) ℂ)
    (@SeminormedAddCommGroup.toSeminormedAddGroup (Matrix (κ × ι) (κ × ι) ℂ)
      (@NormedAddCommGroup.toSeminormedAddCommGroup (Matrix (κ × ι) (κ × ι) ℂ)
        (choiMatrixNormedAddCommGroup (ι := ι) (κ := κ))))

local instance : BorelSpace (Matrix (κ × ι) (κ × ι) ℂ) :=
  ⟨rfl⟩

/-- The unnormalized Choi-valued form of a countably additive instrument. -/
structure ChoiVectorInstrument (α ι κ : Type*) [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] where
  choiMeasure : VectorMeasure α (Matrix (κ × ι) (κ × ι) ℂ)
  positive : ∀ S, MeasurableSet S → (choiMeasure S).PosSemidef
  inputMarginal_total : ptraceA κ ι (choiMeasure univ) = 1

/-- Real matrix trace as a real-linear functional. -/
def matrixRealTraceLinear (ν : Type*) [Fintype ν] : Matrix ν ν ℂ →ₗ[ℝ] ℝ where
  toFun C := C.trace.re
  map_add' C D := by simp only [Matrix.trace_add, Complex.add_re]
  map_smul' r C := by simp [Matrix.trace_smul]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem trace_ptraceA_eq (C : Matrix (κ × ι) (κ × ι) ℂ) :
    (ptraceA κ ι C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag, ptraceA_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

namespace ChoiVectorInstrument

variable (P : ChoiVectorInstrument α ι κ)

/-- The total unnormalized Choi trace is the input dimension. -/
theorem trace_choiMeasure_univ : (P.choiMeasure univ).trace = Fintype.card ι := by
  have h := congrArg (fun C : Matrix ι ι ℂ => C.trace) P.inputMarginal_total
  rwa [trace_ptraceA_eq, Matrix.trace_one] at h

/-- Trace divided by the input dimension gives a signed measure before
its positivity is used to turn it into a genuine probability measure. -/
def traceProbabilitySigned : SignedMeasure α :=
  let L := ((Fintype.card ι : ℝ)⁻¹ • matrixRealTraceLinear (κ × ι)).toContinuousLinearMap
  P.choiMeasure.mapRange L.toLinearMap.toAddMonoidHom L.continuous

@[simp] theorem traceProbabilitySigned_apply (S : Set α) :
    P.traceProbabilitySigned S =
      (Fintype.card ι : ℝ)⁻¹ * (P.choiMeasure S).trace.re := rfl

private theorem traceProbabilitySigned_nonneg : 0 ≤[univ] P.traceProbabilitySigned := by
  rw [VectorMeasure.le_restrict_univ_iff_le]
  apply VectorMeasure.le_iff.mpr
  intro S hS
  change 0 ≤ P.traceProbabilitySigned S
  rw [traceProbabilitySigned_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Complex.nonneg_iff.mp (P.positive S hS).trace_nonneg).1

/-- The instrument's trace measure, derived from its positive set masses. -/
def traceProbability : Measure α :=
  P.traceProbabilitySigned.toMeasureOfZeroLE univ MeasurableSet.univ
    P.traceProbabilitySigned_nonneg

/-- The real mass of a measurable set is its normalized Choi trace. -/
theorem traceProbability_real_apply {S : Set α} (hS : MeasurableSet S) :
    P.traceProbability.real S =
      (Fintype.card ι : ℝ)⁻¹ * (P.choiMeasure S).trace.re := by
  rw [traceProbability, SignedMeasure.toMeasureOfZeroLE_real_apply
    _ P.traceProbabilitySigned_nonneg MeasurableSet.univ hS]
  simp only [univ_inter, traceProbabilitySigned_apply]

instance : IsFiniteMeasure P.traceProbability := by
  unfold traceProbability
  infer_instance

instance [Nonempty ι] : IsProbabilityMeasure P.traceProbability := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [P.traceProbability_real_apply MeasurableSet.univ, P.trace_choiMeasure_univ]
  simp [Fintype.card_ne_zero]

/-- A trace-null measurable set has zero positive Choi mass. -/
theorem choiMeasure_eq_zero_of_traceProbability_eq_zero [Nonempty ι]
    {S : Set α} (hS : MeasurableSet S) (hzero : P.traceProbability S = 0) :
    P.choiMeasure S = 0 := by
  have hmass : P.traceProbability.real S = 0 := by simp [Measure.real, hzero]
  rw [P.traceProbability_real_apply hS] at hmass
  have hcard : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have hre : (P.choiMeasure S).trace.re = 0 := (mul_eq_zero.mp hmass).resolve_left hcard
  have him : (P.choiMeasure S).trace.im = 0 :=
    (Complex.nonneg_iff.mp (P.positive S hS).trace_nonneg).2.symm
  apply (P.positive S hS).trace_eq_zero_iff.mp
  exact Complex.ext hre him

/-- Absolute continuity with respect to the trace probability is proved
from positivity and zero trace, not imposed in the instrument definition. -/
theorem choiMeasure_absolutelyContinuous [Nonempty ι] :
    P.choiMeasure ≪ᵥ P.traceProbability.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro S hS hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hS] at hzero
  exact P.choiMeasure_eq_zero_of_traceProbability_eq_zero hS hzero

/-- Coordinate Radon–Nikodym reconstructs an actual measurable integrable
matrix density for the countably additive Choi measure. -/
theorem exists_integrable_density [Nonempty ι] :
    ∃ C : α → Matrix (κ × ι) (κ × ι) ℂ,
      Measurable C ∧ Integrable C P.traceProbability ∧
        P.traceProbability.withDensityᵥ C = P.choiMeasure :=
  exists_finiteDimensional_vectorMeasure_density P.choiMeasure P.traceProbability
    P.choiMeasure_absolutelyContinuous

end ChoiVectorInstrument

end

end NLQCLean.ClassicalCommunication
