import NLQCLean.Geometry.VectorSard
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Sard slices

For a smooth map `f : E → F₁ × F₂`, the critical values form a null set in the
product, so for almost every `c ∈ F₁`, almost every `y ∈ F₂` has only regular
preimages over `(c, y)`. The order `(c, y)` matters: `Measure.ae_ae_of_ae_prod`
needs no measurability in that direction. This is roadmap step D2 of the direct
image-volume route.
-/

section

open MeasureTheory Set Function

open scoped ContDiff

namespace NLQCLean

variable {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [MeasureSpace F₁] [BorelSpace F₁] [(volume : Measure F₁).IsAddHaarMeasure]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [MeasureSpace F₂] [BorelSpace F₂] [(volume : Measure F₂).IsAddHaarMeasure]

/-- **Sard slices.** For a smooth map into a product, for almost every first
coordinate `c` and almost every second coordinate `y`, every preimage of
`(c, y)` is a regular point. -/
theorem ae_ae_regular_slice {f : E → F₁ × F₂} (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c : F₁, ∀ᵐ y : F₂, ∀ x, f x = (c, y) → Surjective (fderiv ℝ f x) := by
  have : (volume : Measure (F₁ × F₂)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hnull : (volume : Measure (F₁ × F₂)) (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 :=
    criticalImage_volume_eq_zero hf fun x hx => hx
  have hae : ∀ᵐ z : F₁ × F₂, z ∉ f '' {x | ¬ Surjective (fderiv ℝ f x)} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  rw [Measure.volume_eq_prod] at hae
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with c hc
  filter_upwards [hc] with y hy x hx
  by_contra h
  exact hy ⟨x, h, hx⟩

end NLQCLean
end
