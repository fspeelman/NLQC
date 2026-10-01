import NLQCLean.Models.PVMTVReachability
import NLQCLean.Bounds.PVMHaarFractionConditional

/-!
# Conditional Haar outer measure for worst-case joint PVM TV

Convert TV to average basis score on the pure or mixed
channel before using the score-reachability bound. No TV measurability
or componentwise TV guarantee is required.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped ENNReal

/-- One universal constant bounds the Haar outer measure for both operational resource classes. -/
theorem exists_pvm_tv_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (purePVMTVReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((pvmCodimension d : ℝ) / 2))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (mixedPVMTVReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hHaar⟩ := exists_pvm_haar_fraction_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd hK hquarter e he he'
  have : NeZero d := ⟨by omega⟩
  obtain ⟨_, _, hp, hm⟩ := hHaar d K hd hK hquarter e he he'
  exact ⟨(measure_mono (purePVMTVReachable_subset_purePVMReachable K e)).trans hp,
    (measure_mono (mixedPVMTVReachable_subset_mixedPVMReachable K e)).trans hm⟩

end NLQCLean
