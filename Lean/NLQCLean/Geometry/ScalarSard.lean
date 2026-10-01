/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.TauCeti.Analysis.Calculus.Sard.VanishingDerivative

/-!
# Scalar Sard for a vanishing derivative

This file specializes the vendored Tau Ceti vanishing-derivative Sard theorem to a smooth
real-valued map and Lebesgue measure. It is the scalar Sard input used by
`paper/sard-qualitative-proof.md`.
-/

section

open MeasureTheory Set

open scoped ContDiff ENNReal

namespace NLQCLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {s : Set E}

/-- A smooth real-valued map sends any set on which its full Fréchet derivative vanishes to a
Lebesgue-null set.  No measurability or regularity assumption is imposed on the set. -/
theorem scalarCriticalImage_volume_eq_zero (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : volume (f '' s) = 0 := by
  apply Vendor.TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero (n := ∞) volume
  · exact WithTop.coe_le_coe.mpr le_top
  · exact fun _ _ ↦ hf.contDiffAt
  · exact hs

end NLQCLean

end
