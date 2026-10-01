/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.TauCeti.Analysis.Calculus.Sard.OutermostStratum

/-!
# Vector-valued Sard for smooth maps

This file specializes the vendored Tau Ceti Morse--Sard theorem
`NLQCLean.Vendor.TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero` to smooth maps between
finite-dimensional real normed spaces. A point is critical when the full Fréchet derivative there
is not surjective. No relation between the source and target dimensions is assumed.

The vendored theorem requires regularity `finrank ℝ E * finrank ℝ E + 1`; smoothness of class
`C^∞` exceeds this finite threshold for every finite-dimensional source. The critical subsets
below are arbitrary: they need not be measurable, since their images lie in the image of the full
critical set and measure is monotone.

## Main results

* `NLQCLean.criticalImage_addHaar_eq_zero`: every additive Haar measure vanishes on the image of
  any set of critical points of a smooth map.
* `NLQCLean.criticalImage_volume_eq_zero`: the same statement for the canonical volume.
* `NLQCLean.rankDeficientImage_addHaar_eq_zero`: the image of any set on which the derivative has
  rank smaller than the target dimension is null.
-/

section

open MeasureTheory Module Set

open scoped ContDiff

namespace NLQCLean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {s : Set E}

/-- **Sard's theorem for smooth maps.** A smooth map between finite-dimensional real normed spaces
sends any set of points at which its Fréchet derivative is not surjective to a null set of any
additive Haar measure on the target. The set is arbitrary, and the two dimensions are unrelated. -/
theorem criticalImage_addHaar_eq_zero [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x)) : μ (f '' s) = 0 :=
  measure_mono_null (image_mono fun x hx ↦ hs x hx)
    (Vendor.TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero μ hf
      (WithTop.coe_le_coe.mpr le_top))

/-- **Sard's theorem for smooth maps**, for the canonical volume of the target. -/
theorem criticalImage_volume_eq_zero [MeasureSpace F] [BorelSpace F]
    [(volume : Measure F).IsAddHaarMeasure] (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x)) : volume (f '' s) = 0 :=
  criticalImage_addHaar_eq_zero volume hf hs

/-- A smooth map between finite-dimensional real normed spaces sends any set of points at which
the rank of its Fréchet derivative is smaller than the target dimension to a null set of any
additive Haar measure on the target. -/
theorem rankDeficientImage_addHaar_eq_zero [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F)) < finrank ℝ F) :
    μ (f '' s) = 0 := by
  refine criticalImage_addHaar_eq_zero μ hf fun x hx hsurj ↦ ?_
  have hrank := hs x hx
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  exact lt_irrefl _ hrank

end NLQCLean

end
