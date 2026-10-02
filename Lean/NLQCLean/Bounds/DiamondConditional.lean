import NLQCLean.Models.DiamondReachability
import NLQCLean.Bounds.ResourceConditional

/-!
# Conditional operational resource, qubit and Haar bounds

The operational diamond-reachable sets are
contained in the Borel score-reachable sets. Haar outer measure obeys the
same bound, and universal diamond implementations obey the same resource
and base-two logarithmic inequalities. The sole geometric premise is the
ordinary explicit polynomial image-volume property.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped ENNReal

/-- One universal constant bounds the Haar outer measure for both operational resource classes. -/
theorem exists_diamond_haar_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (pureDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (mixedDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hHaar⟩ := exists_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd hK hquarter e he he'
  let : NeZero d := ⟨by omega⟩
  obtain ⟨_, _, hp, hm⟩ := hHaar d K hd hK hquarter e he he'
  exact ⟨(measure_mono (pureDiamondReachable_subset_pureReachable K e)).trans hp,
    (measure_mono (mixedDiamondReachable_subset_mixedReachable K e)).trans hm⟩

/-- Resource bound in normalized diamond error, including arbitrary finite mixed implementations. -/
theorem exists_universal_diamond_resource_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, hbound⟩ := exists_universal_resource_constant_of_imageVolumeBound hGeom
  refine ⟨c, hc, ?_⟩
  intro d K hd hK e he he'
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := hbound d K hd hK e he he'
  exact ⟨fun h => hp h.score, fun h => hm h.score⟩

/-- Qubit bound in normalized diamond error with a single universal additive constant. -/
theorem exists_universal_diamond_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨b, hb, hbound⟩ := exists_universal_qubit_constant_of_imageVolumeBound hGeom
  refine ⟨b, hb, ?_⟩
  intro n K hn hK e he he'
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨hp, hm⟩ := hbound n K hn hK e he he'
  exact ⟨fun h => hp h.score, fun h => hm h.score⟩

end NLQCLean
