import NLQCLean.Models.ClassicalCommunication.ChoiChannelEquivalence

/-!
# Countably additive completely positive instruments

The instrument is an actual vector measure of continuous complex-linear
operations. Complete positivity is required of measurable-set masses and
trace preservation of the total operation. The Choi measure, its trace
probability, and its positive normalized density are derived, not supplied
as representation fields.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance cpMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance cpMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (cpMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance {ν : Type*} [Fintype ν] :
    ContinuousENorm (Matrix ν ν ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix ν ν ℂ)
    (@SeminormedAddCommGroup.toSeminormedAddGroup (Matrix ν ν ℂ)
      (@NormedAddCommGroup.toSeminormedAddCommGroup (Matrix ν ν ℂ)
        (cpMatrixNormedAddCommGroup (ν := ν))))

local instance {ν : Type*} [Fintype ν] : MeasurableSpace (Matrix ν ν ℂ) :=
  borel (Matrix ν ν ℂ)

local instance {ν : Type*} [Fintype ν] : BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

local instance {ν τ : Type*} [Fintype ν] [Fintype τ] :
    MeasurableSpace (Matrix ν ν ℂ →L[ℂ] Matrix τ τ ℂ) :=
  borel (Matrix ν ν ℂ →L[ℂ] Matrix τ τ ℂ)

local instance {ν τ : Type*} [Fintype ν] [Fintype τ] :
    BorelSpace (Matrix ν ν ℂ →L[ℂ] Matrix τ τ ℂ) := ⟨rfl⟩

/-- A countably additive CP-map-valued instrument on its original finite
input and output systems. No density or Choi representation is a field. -/
structure CPVectorInstrument (α ι κ : Type*) [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] where
  operationMeasure : VectorMeasure α (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ)
  completelyPositive : ∀ S, MeasurableSet S →
    CompletelyPositive (operationMeasure S).toLinearMap
  tracePreserving_total : ∀ X : Matrix ι ι ℂ,
    (operationMeasure univ X).trace = X.trace

variable {α ι κ : Type*} [MeasurableSpace α]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

namespace CPVectorInstrument

/-- Equality of actual operation vector measures determines an instrument;
the positivity and normalization proofs carry no additional data. -/
theorem ext_operationMeasure {I J : CPVectorInstrument α ι κ}
    (h : I.operationMeasure = J.operationMeasure) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The Choi form is obtained by transporting the actual vector measure
through the proved continuous Choi equivalence. -/
def toChoiInstrument [Nonempty ι] (I : CPVectorInstrument α ι κ) :
    ChoiVectorInstrument α ι κ where
  choiMeasure :=
    let L := unnormalizedChoiContinuousRealLinearEquiv.toContinuousLinearMap
    I.operationMeasure.mapRange L.toLinearMap.toAddMonoidHom L.continuous
  positive S hS :=
    (completelyPositive_iff_unnormalizedChoi_posSemidef _).mp
      (I.completelyPositive S hS)
  inputMarginal_total :=
    (tracePreserving_iff_ptraceA_unnormalizedChoi _).mp I.tracePreserving_total

@[simp] theorem toChoiInstrument_choiMeasure_apply [Nonempty ι]
    (I : CPVectorInstrument α ι κ) (S : Set α) :
    I.toChoiInstrument.choiMeasure S =
      unnormalizedChoiMatrix (I.operationMeasure S).toLinearMap := rfl

end CPVectorInstrument

namespace ChoiVectorInstrument

/-- Equality of actual Choi vector measures determines an instrument. -/
theorem ext_choiMeasure {P Q : ChoiVectorInstrument α ι κ}
    (h : P.choiMeasure = Q.choiMeasure) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Inverse Choi transport reconstructs an actual countably additive
CP-map-valued instrument, including its trace-preserving total operation. -/
def toCPInstrument [Nonempty ι] (P : ChoiVectorInstrument α ι κ) :
    CPVectorInstrument α ι κ where
  operationMeasure :=
    let L := unnormalizedChoiContinuousRealLinearEquiv.symm.toContinuousLinearMap
    P.choiMeasure.mapRange L.toLinearMap.toAddMonoidHom L.continuous
  completelyPositive S hS := by
    apply (completelyPositive_iff_unnormalizedChoi_posSemidef _).mpr
    change (unnormalizedChoiMatrix
      (channelFromUnnormalizedChoi (P.choiMeasure S)).toLinearMap).PosSemidef
    rw [unnormalizedChoi_channelFromUnnormalizedChoi]
    exact P.positive S hS
  tracePreserving_total := by
    apply (tracePreserving_iff_ptraceA_unnormalizedChoi _).mpr
    change ptraceA κ ι (unnormalizedChoiMatrix
      (channelFromUnnormalizedChoi (P.choiMeasure univ)).toLinearMap) = 1
    rw [unnormalizedChoi_channelFromUnnormalizedChoi]
    exact P.inputMarginal_total

@[simp] theorem toCPInstrument_operationMeasure_apply [Nonempty ι]
    (P : ChoiVectorInstrument α ι κ) (S : Set α) :
    P.toCPInstrument.operationMeasure S = channelFromUnnormalizedChoi (P.choiMeasure S) :=
  rfl

end ChoiVectorInstrument

namespace CPVectorInstrument

/-- Transporting an actual CP instrument to Choi form and back loses no
operation mass, normalization, or original quantum system. -/
theorem toChoiInstrument_toCPInstrument [Nonempty ι]
    (I : CPVectorInstrument α ι κ) : I.toChoiInstrument.toCPInstrument = I := by
  apply ext_operationMeasure
  apply VectorMeasure.ext
  intro S _
  simp only [ChoiVectorInstrument.toCPInstrument_operationMeasure_apply,
    toChoiInstrument_choiMeasure_apply]
  exact channelFromUnnormalizedChoi_unnormalizedChoi (I.operationMeasure S)

end CPVectorInstrument

namespace ChoiVectorInstrument

/-- Transporting a positive Choi instrument to CP form and back reproduces
its actual countably additive matrix measure. -/
theorem toCPInstrument_toChoiInstrument [Nonempty ι]
    (P : ChoiVectorInstrument α ι κ) : P.toCPInstrument.toChoiInstrument = P := by
  apply ext_choiMeasure
  apply VectorMeasure.ext
  intro S _
  simp only [CPVectorInstrument.toChoiInstrument_choiMeasure_apply,
    toCPInstrument_operationMeasure_apply]
  exact unnormalizedChoi_channelFromUnnormalizedChoi (P.choiMeasure S)

end ChoiVectorInstrument

/-- Countably additive CP-map instruments and positive Choi instruments are
equivalent descriptions, by actual continuous vector-measure transport. -/
def cpVectorInstrumentChoiEquiv [Nonempty ι] :
    CPVectorInstrument α ι κ ≃ ChoiVectorInstrument α ι κ where
  toFun := CPVectorInstrument.toChoiInstrument
  invFun := ChoiVectorInstrument.toCPInstrument
  left_inv := CPVectorInstrument.toChoiInstrument_toCPInstrument
  right_inv := ChoiVectorInstrument.toCPInstrument_toChoiInstrument

namespace CPVectorInstrument

variable [Nonempty ι] (I : CPVectorInstrument α ι κ)

/-- The probability measure is derived from the actual instrument by its
proved Choi representation and normalized trace, not given as a field. -/
def traceProbability : Measure α := I.toChoiInstrument.traceProbability

instance : IsProbabilityMeasure I.traceProbability := by
  unfold traceProbability
  infer_instance

/-- The original CP-map-valued instrument has an actual measurable
integrable CP density. Its unnormalized Choi trace equals the input dimension
almost everywhere and its integrated input marginal is the identity. -/
theorem exists_positive_normalized_density :
    ∃ Φ : α → (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ),
      Measurable Φ ∧ Integrable Φ I.traceProbability ∧
      I.traceProbability.withDensityᵥ Φ = I.operationMeasure ∧
      (∀ᵐ a ∂I.traceProbability, CompletelyPositive (Φ a).toLinearMap ∧
        (unnormalizedChoiMatrix (Φ a).toLinearMap).trace = (Fintype.card ι : ℂ)) ∧
      (∫ a, ptraceA κ ι (unnormalizedChoiMatrix (Φ a).toLinearMap)
        ∂I.traceProbability) = 1 := by
  let : FiniteDimensional ℝ (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) :=
    (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
  let : CompleteSpace (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) :=
    FiniteDimensional.complete ℝ (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ)
  obtain ⟨C, hmeas, hC, hrep, hpositive, hmarginal⟩ :=
    I.toChoiInstrument.exists_positive_normalized_density
  let L := (unnormalizedChoiContinuousRealLinearEquiv (ι := ι) (κ := κ)).symm.toContinuousLinearMap
  let Φ : α → (Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) := fun a => L (C a)
  have hΦ : Integrable Φ I.traceProbability := L.integrable_comp hC
  refine ⟨Φ, L.continuous.measurable.comp hmeas, hΦ, ?_, ?_, ?_⟩
  · apply VectorMeasure.ext
    intro S hS
    rw [withDensityᵥ_apply hΦ hS]
    change (∫ a in S, L (C a) ∂I.toChoiInstrument.traceProbability) =
      I.operationMeasure S
    rw [L.integral_comp_comm hC.integrableOn]
    rw [I.toChoiInstrument.setIntegral_density_eq C hC hrep hS]
    exact channelFromUnnormalizedChoi_unnormalizedChoi (I.operationMeasure S)
  · filter_upwards [hpositive] with a ha
    have hchoi : unnormalizedChoiMatrix (Φ a).toLinearMap = C a :=
      unnormalizedChoi_channelFromUnnormalizedChoi (C a)
    refine ⟨(completelyPositive_iff_unnormalizedChoi_posSemidef _).mpr ?_, ?_⟩
    · rw [hchoi]
      exact ha.1
    · rw [hchoi]
      exact ha.2
  · change (∫ a, ptraceA κ ι
      (unnormalizedChoiMatrix (channelFromUnnormalizedChoi (C a)).toLinearMap)
        ∂I.traceProbability) = 1
    simp_rw [unnormalizedChoi_channelFromUnnormalizedChoi]
    exact hmarginal

end CPVectorInstrument

end

end NLQCLean.ClassicalCommunication
