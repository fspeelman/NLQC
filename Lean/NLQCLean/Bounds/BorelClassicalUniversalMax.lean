import NLQCLean.Bounds.BorelClassicalStrongPVM
import NLQCLean.Bounds.FiniteLocalization
import NLQCLean.Models.SwapNeighborhood

/-!
# Universal free-classical bounds in general dimension

`cor:free-classical` (i) of the robust companion for every `d ≥ 2`: a quantum
footprint `Kq` that suffices, with free standard-Borel classical messages and
measured shared randomness, for every unitary satisfies
`Kq ≥ max(d²(1 - ε), c d^{-2/5} ln(1/ε)^{1/10})`, and for every rank-one PVM
`Kq ≥ max(d(1 - ε), c d^{-2/5} ln(1/ε)^{1/10})`. The floors come from SWAP and
the generalized Bell basis over the whole Borel and shared-randomness class;
the precision terms from the strong universal logarithm bounds.
-/

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory StandardBorelClassicalProtocol

/-- SWAP reached by an actual Borel or shared-random protocol forces
`Kq ≥ d²(1 - ε)`. -/
theorem swap_floor_of_mem_borelAllScoreReachable {d K : ℕ} (hd : 0 < d) {ε : ℝ}
    (h : swapElement d ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) :
    (d : ℝ) ^ 2 * (1 - ε) ≤ K := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rcases h with h | h
  · rw [borelScoreReachable, dite_eq_left hd] at h
    obtain ⟨s, P, ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩⟩ := h
    · simpa only [Fintype.card_fin] using P.swap_quantumFootprint_floor hK hs
    · simpa only [Fintype.card_fin] using P.mixed_swap_quantumFootprint_floor m hK hs
  · rw [borelSharedRandomScoreReachable, dite_eq_left hd] at h
    obtain ⟨s, P, ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩⟩ := h
    · exact sharedRandom_swap_quantumFootprint_floor s.μ P hP hK hs
    · exact mixedSharedRandom_swap_quantumFootprint_floor s.μ P m hP hK hs

/-- The generalized Bell basis reached by an actual Borel or shared-random
PVM protocol forces `Kq ≥ d(1 - ε)`. -/
theorem bell_floor_of_mem_borelAllPVMScoreReachable {d K : ℕ} [NeZero d] {ε : ℝ}
    (h : generalizedBellUnitary d ∈
      borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) :
    (d : ℝ) * (1 - ε) ≤ K := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rcases h with h | h
  · rw [borelPVMScoreReachable, dite_eq_left hd] at h
    obtain ⟨s, P, ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩⟩ := h
    · exact P.generalizedBellPVM_quantumFootprint_floor hK hs
    · exact P.mixed_generalizedBellPVM_quantumFootprint_floor m hK hs
  · rw [borelSharedRandomPVMScoreReachable, dite_eq_left hd] at h
    obtain ⟨s, P, ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩⟩ := h
    · exact sharedRandom_generalizedBellPVM_quantumFootprint_floor s.μ P hP hK hs
    · exact mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor s.μ P m hP hK hs

/-- The tenth-root form of `L ≤ C d⁴ K¹⁰`. -/
theorem quantumFootprint_rate_of_fourth_log_bound {C L : ℝ} {d r : ℕ}
    (hC : 0 < C) (hd : 0 < d) (hL : 0 ≤ L)
    (hbound : L ≤ C * (d : ℝ) ^ 4 * (r : ℝ) ^ 10) :
    C ^ (-(1 / 10 : ℝ)) * (d : ℝ) ^ (-(2 / 5 : ℝ)) * L ^ (1 / 10 : ℝ) ≤ r := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot := Real.rpow_le_rpow hL hbound (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hD : ((d : ℝ) ^ 4) ^ (1 / 10 : ℝ) = (d : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdR.le]
    norm_num
  have hr : ((r : ℝ) ^ 10) ^ (1 / 10 : ℝ) = r := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg r) (by decide : (10 : ℕ) ≠ 0)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hC.le (by positivity), hD, hr] at hroot
  have hCC : C ^ (-(1 / 10 : ℝ)) * C ^ (1 / 10 : ℝ) = 1 := by
    rw [← Real.rpow_add hC]
    norm_num
  have hDD : (d : ℝ) ^ (-(2 / 5 : ℝ)) * (d : ℝ) ^ (2 / 5 : ℝ) = 1 := by
    rw [← Real.rpow_add hdR]
    norm_num
  calc
    _ ≤ C ^ (-(1 / 10 : ℝ)) * (d : ℝ) ^ (-(2 / 5 : ℝ)) *
        (C ^ (1 / 10 : ℝ) * (d : ℝ) ^ (2 / 5 : ℝ) * r) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (C ^ (-(1 / 10 : ℝ)) * C ^ (1 / 10 : ℝ)) *
        ((d : ℝ) ^ (-(2 / 5 : ℝ)) * (d : ℝ) ^ (2 / 5 : ℝ)) * r := by ring
    _ = r := by rw [hCC, hDD]; ring

/-- **`cor:free-classical` (i), general dimension.** One universal constant
`c > 0`: a quantum footprint `Kq ≥ 1` sufficing for every unitary (respectively
every rank-one PVM) with free standard-Borel classical messages and measured
shared randomness, at score deficit `ε ∈ (0, 1/2]`, satisfies
`Kq ≥ max(d²(1 - ε), c d^{-2/5} ln(1/ε)^{1/10})`
(respectively `Kq ≥ max(d(1 - ε), c d^{-2/5} ln(1/ε)^{1/10})`). -/
theorem exists_borel_classical_universal_max_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
          max ((d : ℝ) ^ 2 * (1 - ε))
            (c * (d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) ≤ K) ∧
        ((∀ M, M ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
          max ((d : ℝ) * (1 - ε))
            (c * (d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) ≤ K) := by
  obtain ⟨CU, hCU, hU⟩ :=
    exists_borel_classical_strong_unitary_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  obtain ⟨CP, hCP, hPVM⟩ :=
    exists_borel_classical_strong_pvm_universal_log_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨min (CU ^ (-(1 / 10 : ℝ))) (CP ^ (-(1 / 10 : ℝ))), lt_min (by positivity) (by positivity),
    fun d K hd hK ε hε hhalf => ⟨fun hall => ?_, fun hall => ?_⟩⟩
  all_goals
    have hd0 : 0 < d := by omega
    have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
    have hpow : 0 ≤ (d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ) := by positivity
  · apply max_le (swap_floor_of_mem_borelAllScoreReachable hd0 (hall _))
    have hrate := quantumFootprint_rate_of_fourth_log_bound hCU hd0 hL
      (hU d K hd hK ε hε hhalf hall)
    calc min (CU ^ (-(1 / 10 : ℝ))) (CP ^ (-(1 / 10 : ℝ))) * (d : ℝ) ^ (-(2 / 5 : ℝ)) *
          Real.log (1 / ε) ^ (1 / 10 : ℝ)
        = min (CU ^ (-(1 / 10 : ℝ))) (CP ^ (-(1 / 10 : ℝ))) *
          ((d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) := by ring
      _ ≤ CU ^ (-(1 / 10 : ℝ)) * ((d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hpow
      _ ≤ K := by rw [← mul_assoc]; exact hrate
  · let : NeZero d := ⟨by omega⟩
    apply max_le (bell_floor_of_mem_borelAllPVMScoreReachable (hall _))
    have hrate := quantumFootprint_rate_of_fourth_log_bound hCP hd0 hL
      (hPVM d K hd hK ε hε hhalf hall)
    calc min (CU ^ (-(1 / 10 : ℝ))) (CP ^ (-(1 / 10 : ℝ))) * (d : ℝ) ^ (-(2 / 5 : ℝ)) *
          Real.log (1 / ε) ^ (1 / 10 : ℝ)
        = min (CU ^ (-(1 / 10 : ℝ))) (CP ^ (-(1 / 10 : ℝ))) *
          ((d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) := by ring
      _ ≤ CP ^ (-(1 / 10 : ℝ)) * ((d : ℝ) ^ (-(2 / 5 : ℝ)) * Real.log (1 / ε) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow
      _ ≤ K := by rw [← mul_assoc]; exact hrate

end NLQCLean.ClassicalCommunication
