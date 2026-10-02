import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.BorelClassicalQubits
import NLQCLean.Bounds.NearBellUniversal

/-!
# Free classical communication: the strong universal PVM rate

Universality for actual Borel and measured shared-randomness PVM protocols of
quantum footprint `Kq` gives universality in the charged model at footprint
`4 d⁴ Kq⁵`. Theorem B(ii) then gives `c d² √log(1/ε) ≤ 4 d⁴ Kq⁵`, hence
`log(1/ε) ≤ C d⁴ Kq¹⁰` and, at `d = 2ⁿ`, the dimension coefficient `-2n/5` of
`cor:free-classical` (i) for measurements.
-/

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory

/-- Target-dependent actual PVM protocols transfer to the near-Bell universal bound. -/
theorem exists_borel_classical_strong_pvm_universal_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T, T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 := by
  obtain ⟨c, hc, hbound⟩ := exists_nearBell_universal_resource_constant hGeom
  refine ⟨16 / c ^ 2, by positivity, ?_⟩
  intro d K hd _hK ε hε hhalf hreach
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  apply log_le_fourth_tenth_power_of_finite_strong_charged_lower_bound hc hd0 hL
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd ε hε hhalf).1
    (fun T => borelAllPVMScoreReachable_subset_purePVMReachable hd0 ε (hreach T))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The strong universal PVM rate. -/
theorem exists_borel_classical_strong_pvm_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T, T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 :=
  exists_borel_classical_strong_pvm_universal_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- Universal PVM bound with the improved dimension coefficient `2/5`:
`log₂ Kq ≥ (1/10) log₂ log(1/ε) - (2/5) n - B`. -/
theorem exists_borel_classical_strong_pvm_universal_qubit_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T, T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_borel_classical_strong_pvm_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n K hn hK ε hε hhalf hall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  simpa only [Nat.cast_ofNat, show (4 : ℝ) / 10 = 2 / 5 by norm_num] using
    quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K)
      (hbound (2 ^ n) K (two_le_two_pow hn) hK ε hε hhalf hall)

end NLQCLean.ClassicalCommunication
