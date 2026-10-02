import NLQCLean.Bounds.BorelClassicalRates
import NLQCLean.Bounds.FiniteClassicalQubits

/-!
# Quantum-footprint logarithms for actual standard-Borel protocols

At logical dimension `2ⁿ`, the tenth-power logarithm bounds for actual
standard-Borel pure/common-map mixed channels and measured shared-randomness
averages give coefficient `1/10` on the error logarithm. The dimension
coefficient is `-3/5` for PVM universality and almost every target, and `-2/5`
for unitary universality. Each statement keeps exactly the three existing
geometry arguments.
-/

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory

theorem two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn

/-- Baseline universal unitary bound for actual Borel classical protocols. -/
theorem exists_borel_classical_unitary_universal_qubit_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_borel_classical_unitary_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n K hn hK ε hε hhalf hall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
    quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K)
      (hbound (2 ^ n) K (two_le_two_pow hn) hK ε hε hhalf hall)

/-- Universal PVM bound for actual Borel classical protocols, baseline coefficient. -/
theorem exists_borel_classical_pvm_universal_qubit_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ M, M ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_borel_classical_pvm_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n K hn hK ε hε hhalf hall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
    quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K)
      (hbound (2 ^ n) K (two_le_two_pow hn) hK ε hε hhalf hall)

/-- Universal unitary bound with the improved dimension coefficient `2/5`. -/
theorem exists_borel_classical_strong_unitary_universal_qubit_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_borel_classical_strong_unitary_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n K hn hK ε hε hhalf hall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  simpa only [Nat.cast_ofNat, show (4 : ℝ) / 10 = 2 / 5 by norm_num] using
    quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K)
      (hbound (2 ^ n) K (two_le_two_pow hn) hK ε hε hhalf hall)

/-- Almost every target: one additive constant before the dimension, and one
target threshold before every positive budget and all actual Borel and
measured shared-randomness unitary and PVM score witnesses. -/
theorem exists_ae_borel_classical_qubit_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
        ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          (T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) := by
  obtain ⟨C, hC, hae⟩ :=
    exists_ae_borel_classical_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n hn => ?_⟩
  filter_upwards [hae (2 ^ n) (two_le_two_pow hn)] with T hT
  obtain ⟨ε₀, hε₀pos, hε₀half, hT⟩ := hT
  refine ⟨ε₀, hε₀pos, hε₀half, fun K hK ε hε hsmall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → Real.log (1 / ε) ≤ C * ((2 ^ n : ℕ) : ℝ) ^ 6 * (K : ℝ) ^ 10) (hu : X) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
    simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
      quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K) (hX hu)
  obtain ⟨hU, hM⟩ := hT K ε hε hsmall
  exact ⟨hq hU, hq hM⟩

/-- **Theorem C, almost every target.** One target threshold gives both the
precision bound with dimension coefficient `-3/5` and the floors `Kq ≥ d²`
(unitaries) and `Kq ≥ d` (measurements), for all actual Borel and measured
shared-randomness score witnesses. -/
theorem exists_ae_borel_classical_qubit_and_floor_constant :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
        ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          (T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ) ∧ (2 ^ n) ^ 2 ≤ K) ∧
          (T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ) ∧ 2 ^ n ≤ K) := by
  obtain ⟨B, hB, hae⟩ :=
    exists_ae_borel_classical_qubit_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨B, hB, fun n hn => ?_⟩
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  filter_upwards [hae n hn,
    ae_borel_classical_full_spectral_threshold.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} (2 ^ n)]
    with T hT hF
  obtain ⟨ε₀, hε₀, hε₀half, hrate⟩ := hT
  obtain ⟨η, hη, -, hfloor⟩ := hF
  refine ⟨min ε₀ (η / 2), lt_min hε₀ (by positivity), (min_le_left _ _).trans hε₀half,
    fun K hK ε hε hsmall => ?_⟩
  have h1 := hrate K hK ε hε (hsmall.trans (min_le_left _ _))
  have h2 := hfloor K ε (by linarith [hsmall.trans (min_le_right _ _)])
  exact ⟨fun h => ⟨h1.1 h, h2.1 h⟩, fun h => ⟨h1.2 h, h2.2 h⟩⟩

end NLQCLean.ClassicalCommunication
