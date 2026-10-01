import NLQCLean.Models.ClassicalCommunication.KrausRepresentation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensional vector-measure densities

Real-coordinate Radon–Nikodym derivatives reconstruct an actual measurable
Bochner-integrable density for every absolutely continuous finite-dimensional
vector measure.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Set Module
open scoped MeasureTheory

noncomputable section

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Scalar Radon–Nikodym derivatives in a finite real basis give an actual
measurable integrable density for a finite-dimensional vector measure. -/
theorem exists_finiteDimensional_vectorMeasure_density
    (ν : VectorMeasure α E) (μ : Measure α) [SigmaFinite μ]
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : α → E, Measurable f ∧ Integrable f μ ∧ μ.withDensityᵥ f = ν := by
  classical
  let b := Module.finBasis ℝ E
  let L : Fin (finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i => (b.coord i).toContinuousLinearMap
  let σ : Fin (finrank ℝ E) → SignedMeasure α :=
    fun i => ν.mapRange (L i).toLinearMap.toAddMonoidHom (L i).continuous
  have hσ : ∀ i, σ i ≪ᵥ μ.toENNRealVectorMeasure := by
    intro i s hs
    change L i (ν s) = 0
    rw [hν hs, map_zero]
  let f : α → E := fun a => ∑ i, (σ i).rnDeriv μ a • b i
  have hmeas : Measurable f := by
    apply Finset.measurable_sum
    intro i _
    exact ((σ i).measurable_rnDeriv μ).smul measurable_const
  have hint : Integrable f μ :=
    integrable_finsetSum Finset.univ fun i _ =>
      ((σ i).integrable_rnDeriv μ).smul_const (b i)
  have hcoord (i : Fin (finrank ℝ E)) (s : Set α) (hs : MeasurableSet s) :
      (∫ a in s, (σ i).rnDeriv μ a ∂μ) = L i (ν s) := by
    have h := congrArg (fun η : SignedMeasure α => η s)
      ((σ i).withDensityᵥ_rnDeriv_eq μ (hσ i))
    rw [withDensityᵥ_apply ((σ i).integrable_rnDeriv μ) hs] at h
    exact h
  refine ⟨f, hmeas, hint, ?_⟩
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply hint hs]
  change (∫ a in s, ∑ i, (σ i).rnDeriv μ a • b i ∂μ) = ν s
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (((σ i).integrable_rnDeriv μ).smul_const (b i)).integrableOn)]
  simp_rw [integral_smul_const, hcoord _ s hs]
  exact b.sum_repr (ν s)

end

end NLQCLean.ClassicalCommunication
