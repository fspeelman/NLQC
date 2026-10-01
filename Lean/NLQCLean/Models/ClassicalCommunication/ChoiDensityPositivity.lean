import NLQCLean.Models.ClassicalCommunication.ChoiVectorInstrument
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Matrix

/-!
# Positive normalized densities of Choi instruments

Positivity of the masses of an actual countably additive Choi instrument
forces its reconstructed matrix density to be positive almost everywhere.
The trace probability forces the density trace to equal the input dimension;
the total input marginal is preserved by its Bochner integral.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set TopologicalSpace
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

variable {α : Type*} [MeasurableSpace α]

noncomputable local instance densityMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance densityMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (densityMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance {ν : Type*} [Fintype ν] :
    ContinuousENorm (Matrix ν ν ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix ν ν ℂ)
    (@SeminormedAddCommGroup.toSeminormedAddGroup (Matrix ν ν ℂ)
      (@NormedAddCommGroup.toSeminormedAddCommGroup (Matrix ν ν ℂ)
        (densityMatrixNormedAddCommGroup (ν := ν))))

local instance {ν : Type*} [Fintype ν] : MeasurableSpace (Matrix ν ν ℂ) :=
  borel (Matrix ν ν ℂ)

local instance {ν : Type*} [Fintype ν] : BorelSpace (Matrix ν ν ℂ) := ⟨rfl⟩

private def conjTransposeRealLinear {ν : Type*} :
    Matrix ν ν ℂ →ₗ[ℝ] Matrix ν ν ℂ where
  toFun C := Cᴴ
  map_add' C D := Matrix.conjTranspose_add C D
  map_smul' r C := by simp

private def quadraticRealLinear {ν : Type*} [Fintype ν] (x : ν → ℂ) :
    Matrix ν ν ℂ →ₗ[ℝ] ℂ where
  toFun C := star x ⬝ᵥ (C *ᵥ x)
  map_add' C D := by simp only [Matrix.add_mulVec, dotProduct_add]
  map_smul' r C := by simp only [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

private theorem hermitian_quadratic_im_eq_zero {ν : Type*} [Fintype ν]
    {C : Matrix ν ν ℂ} (hC : C.IsHermitian) (x : ν → ℂ) :
    (star x ⬝ᵥ (C *ᵥ x)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (star x ⬝ᵥ (C *ᵥ x)) = star x ⬝ᵥ (C *ᵥ x)
  rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hC.eq]

/-- Positive matrix set integrals determine a positive matrix density
almost everywhere. The test vectors are made simultaneous using a countable
dense family, not an uncountable intersection of full-measure sets. -/
theorem ae_posSemidef_of_forall_setIntegral_posSemidef
    {ν : Type*} [Fintype ν] {μ : Measure α}
    (C : α → Matrix ν ν ℂ) (hC : Integrable C μ)
    (hpositive : ∀ S, MeasurableSet S → (∫ a in S, C a ∂μ).PosSemidef) :
    ∀ᵐ a ∂μ, (C a).PosSemidef := by
  let H := (conjTransposeRealLinear (ν := ν)).toContinuousLinearMap
  have hHermitian : ∀ᵐ a ∂μ, (C a).IsHermitian := by
    have h := Integrable.ae_eq_of_forall_setIntegral_eq
      (fun a => H (C a)) C (H.integrable_comp hC) hC ?_
    · exact h
    intro S hS _
    rw [H.integral_comp_comm hC.integrableOn]
    exact (hpositive S hS).isHermitian
  have hquadratic (x : ν → ℂ) :
      ∀ᵐ a ∂μ, 0 ≤ (star x ⬝ᵥ (C a *ᵥ x)).re := by
    let L := Complex.reCLM.comp (quadraticRealLinear x).toContinuousLinearMap
    apply ae_nonneg_of_forall_setIntegral_nonneg (L.integrable_comp hC)
    intro S hS _
    rw [L.integral_comp_comm hC.integrableOn]
    exact (hpositive S hS).re_dotProduct_nonneg x
  have hdense : ∀ᵐ a ∂μ, ∀ n : ℕ,
      0 ≤ (star (denseSeq (ν → ℂ) n) ⬝ᵥ
        (C a *ᵥ denseSeq (ν → ℂ) n)).re :=
    ae_all_iff.mpr fun n => hquadratic (denseSeq (ν → ℂ) n)
  filter_upwards [hHermitian, hdense] with a ha hqa
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ha
  intro x
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hermitian_quadratic_im_eq_zero ha x).symm⟩
  have hclosed : IsClosed {y : ν → ℂ | 0 ≤ (star y ⬝ᵥ (C a *ᵥ y)).re} := by
    apply isClosed_le continuous_const
    exact Complex.continuous_re.comp
      (continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id))
  exact (denseRange_denseSeq (ν → ℂ)).induction_on x hclosed hqa

namespace ChoiVectorInstrument

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
variable (P : ChoiVectorInstrument α ι κ)

omit [Nonempty ι] in
/-- Reconstruction as a vector measure identifies every measurable-set
integral with the instrument's actual positive Choi mass. -/
theorem setIntegral_density_eq
    (C : α → Matrix (κ × ι) (κ × ι) ℂ)
    (hC : Integrable C P.traceProbability)
    (hrep : P.traceProbability.withDensityᵥ C = P.choiMeasure)
    {S : Set α} (hS : MeasurableSet S) :
    (∫ a in S, C a ∂P.traceProbability) = P.choiMeasure S := by
  have h := congrArg (fun ν => ν S) hrep
  rwa [withDensityᵥ_apply hC hS] at h

omit [Nonempty ι] in
/-- A reconstructed instrument density is positive almost everywhere. -/
theorem density_ae_posSemidef
    (C : α → Matrix (κ × ι) (κ × ι) ℂ)
    (hC : Integrable C P.traceProbability)
    (hrep : P.traceProbability.withDensityᵥ C = P.choiMeasure) :
    ∀ᵐ a ∂P.traceProbability, (C a).PosSemidef := by
  apply ae_posSemidef_of_forall_setIntegral_posSemidef C hC
  intro S hS
  rw [P.setIntegral_density_eq C hC hrep hS]
  exact P.positive S hS

/-- Normalization by the derived trace probability forces the actual
complex trace of the density to equal the input dimension almost everywhere. -/
theorem density_ae_trace
    (C : α → Matrix (κ × ι) (κ × ι) ℂ)
    (hC : Integrable C P.traceProbability)
    (hrep : P.traceProbability.withDensityᵥ C = P.choiMeasure) :
    ∀ᵐ a ∂P.traceProbability, (C a).trace = (Fintype.card ι : ℂ) := by
  let L := ((Fintype.card ι : ℝ)⁻¹ •
    matrixRealTraceLinear (κ × ι)).toContinuousLinearMap
  have hscaled : (fun a => L (C a)) =ᵐ[P.traceProbability] fun _ => (1 : ℝ) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (L.integrable_comp hC) (integrable_const 1)
    intro S hS _
    rw [L.integral_comp_comm hC.integrableOn,
      P.setIntegral_density_eq C hC hrep hS]
    change (Fintype.card ι : ℝ)⁻¹ * (P.choiMeasure S).trace.re = _
    rw [← P.traceProbability_real_apply hS]
    simp
  filter_upwards [hscaled, P.density_ae_posSemidef C hC hrep] with a ha hpa
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hre := congrArg (fun r : ℝ => (Fintype.card ι : ℝ) * r) ha
  change (Fintype.card ι : ℝ) *
    ((Fintype.card ι : ℝ)⁻¹ * (C a).trace.re) = (Fintype.card ι : ℝ) * 1 at hre
  simp only [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at hre
  apply Complex.ext
  · simpa using hre
  · simpa using (Complex.nonneg_iff.mp hpa.trace_nonneg).2.symm

omit [Nonempty ι] in
/-- The Bochner integral of the reconstructed input marginal is the
identity on the original input register. -/
theorem integral_density_inputMarginal
    (C : α → Matrix (κ × ι) (κ × ι) ℂ)
    (hC : Integrable C P.traceProbability)
    (hrep : P.traceProbability.withDensityᵥ C = P.choiMeasure) :
    (∫ a, ptraceA κ ι (C a) ∂P.traceProbability) = 1 := by
  let L := ((ptraceA κ ι).restrictScalars ℝ).toContinuousLinearMap
  change (∫ a, L (C a) ∂P.traceProbability) = 1
  rw [L.integral_comp_comm hC]
  have htotal := P.setIntegral_density_eq C hC hrep MeasurableSet.univ
  simp only [Measure.restrict_univ] at htotal
  rw [htotal]
  exact P.inputMarginal_total

/-- A positive normalized density is derived from the countably additive
instrument, with exact reconstruction of all of its matrix masses. -/
theorem exists_positive_normalized_density :
    ∃ C : α → Matrix (κ × ι) (κ × ι) ℂ,
      Measurable C ∧ Integrable C P.traceProbability ∧
      P.traceProbability.withDensityᵥ C = P.choiMeasure ∧
      (∀ᵐ a ∂P.traceProbability, (C a).PosSemidef ∧
        (C a).trace = (Fintype.card ι : ℂ)) ∧
      (∫ a, ptraceA κ ι (C a) ∂P.traceProbability) = 1 := by
  obtain ⟨C, hmeas, hC, hrep⟩ := P.exists_integrable_density
  refine ⟨C, hmeas, hC, hrep, ?_, P.integral_density_inputMarginal C hC hrep⟩
  filter_upwards [P.density_ae_posSemidef C hC hrep, P.density_ae_trace C hC hrep]
    with a ha htrace
  exact ⟨ha, htrace⟩

end ChoiVectorInstrument

end

end NLQCLean.ClassicalCommunication
