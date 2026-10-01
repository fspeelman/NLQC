import NLQCLean.Bounds.FiniteClassicalAlmostEvery
import NLQCLean.Bounds.FiniteClassicalStrongUniversal

/-!
# Quantum-footprint logarithms for finite-shape classical protocols

At logical dimension `2ⁿ`, the tenth-power logarithm bounds give
coefficient `1/10` on the error logarithm. The baseline dimension coefficient
is `-3/5`; only universal unitary score implementation has the stronger
coefficient `-2/5`. These are logarithms of quantum footprint, not counts of
initial-resource qubits in a no-communication or localization model.
All classes are the honest twelve-system finite-shape score classes.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix MeasureTheory

/-- Taking base-two logarithms of a tenth-power bound gives an explicit
nonnegative additive constant. No protocol or geometry premise is used. -/
theorem quantumFootprint_log_of_tenth_power_bound
    {C L : ℝ} {a n K : ℕ} (hC : 0 < C) (hL : 0 < L) (hK : 0 < K)
    (hbound : L ≤ C * ((2 ^ n : ℕ) : ℝ) ^ a * (K : ℝ) ^ 10) :
    (1 / 10 : ℝ) * Real.logb 2 L - ((a : ℝ) / 10) * (n : ℝ) -
      max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hL hbound
  push_cast at hlog
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul hC.ne' (by positivity)] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] at hlog
  linarith [le_max_right (0 : ℝ) (Real.logb 2 C / 10)]

/-- Baseline universal unitary score bounds for pure and common-map
mixed finite-shape protocols. The logarithm is that of quantum footprint. -/
theorem exists_finite_classical_unitary_universal_qubit_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_finite_classical_unitary_universal_log_constant hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, ?_⟩
  intro n K hn hK ε hε hεhalf
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → Real.log (1 / ε) ≤ C * ((2 ^ n : ℕ) : ℝ) ^ 6 * (K : ℝ) ^ 10) (hu : X) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
    simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
      quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K) (hX hu)
  obtain ⟨hp, hm⟩ := hbound (2 ^ n) K hd hK ε hε hεhalf
  exact ⟨hq hp, hq hm⟩

/-- PVM universality keeps the baseline dimension coefficient and the full
joint-label score. No stronger unitary coefficient is imported here. -/
theorem exists_finite_classical_pvm_universal_qubit_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ M, M ∈ finitePurePVMScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ M, M ∈ finiteMixedPVMScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_finite_classical_pvm_universal_log_constant hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, ?_⟩
  intro n K hn hK ε hε hεhalf
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → Real.log (1 / ε) ≤ C * ((2 ^ n : ℕ) : ℝ) ^ 6 * (K : ℝ) ^ 10) (hu : X) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
    simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
      quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K) (hX hu)
  obtain ⟨hp, hm⟩ := hbound (2 ^ n) K hd hK ε hε hεhalf
  exact ⟨hq hp, hq hm⟩

/-- Only universal unitary score implementation has the improved `-2n/5`
coefficient, inherited from the charged near-SWAP universal argument. -/
theorem exists_finite_classical_strong_unitary_universal_qubit_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_finite_classical_strong_unitary_universal_log_constant hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, ?_⟩
  intro n K hn hK ε hε hεhalf
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → Real.log (1 / ε) ≤ C * ((2 ^ n : ℕ) : ℝ) ^ 4 * (K : ℝ) ^ 10) (hu : X) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
    simpa only [Nat.cast_ofNat, show (4 : ℝ) / 10 = 2 / 5 by norm_num] using
      quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K) (hX hu)
  obtain ⟨hp, hm⟩ := hbound (2 ^ n) K hd hK ε hε hεhalf
  exact ⟨hq hp, hq hm⟩

/-- One additive constant precedes the logical dimension and almost-every
target. The same fixed-target threshold serves every positive quantum budget
and all four finite pure/common-map mixed unitary/PVM score classes. -/
theorem exists_ae_finite_classical_qubit_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
        ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          (T ∈ finitePureScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finiteMixedScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finitePurePVMScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finiteMixedPVMScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) := by
  obtain ⟨C, hC, hae⟩ := exists_ae_finite_classical_log_constant hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun n hn => ?_⟩
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  filter_upwards [hae (2 ^ n) hd] with T hT
  obtain ⟨ε₀, hε₀pos, hε₀half, hT⟩ := hT
  refine ⟨ε₀, hε₀pos, hε₀half, fun K hK ε hε hsmall => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → Real.log (1 / ε) ≤ C * ((2 ^ n : ℕ) : ℝ) ^ 6 * (K : ℝ) ^ 10) (hu : X) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (K : ℝ) := by
    simpa only [Nat.cast_ofNat, show (6 : ℝ) / 10 = 3 / 5 by norm_num] using
      quantumFootprint_log_of_tenth_power_bound hC hL (by omega : 0 < K) (hX hu)
  obtain ⟨hpU, hmU, hpM, hmM⟩ := hT K ε hε hsmall
  exact ⟨hq hpU, hq hmU, hq hpM, hq hmM⟩

/-- Baseline unitary quantum-footprint logarithms from exactly the three
unchanged external geometry arguments. -/
theorem exists_finite_classical_unitary_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) :=
  exists_finite_classical_unitary_universal_qubit_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

/-- Baseline joint-label PVM quantum-footprint logarithms from those same
three arguments, without importing the stronger unitary rate. -/
theorem exists_finite_classical_pvm_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ M, M ∈ finitePurePVMScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ M, M ∈ finiteMixedPVMScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) :=
  exists_finite_classical_pvm_universal_qubit_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

/-- The stronger unitary-only universal logarithm keeps the original three
external arguments and the finite-score universality hypothesis. -/
theorem exists_finite_classical_strong_unitary_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable (2 ^ n) K ε) →
          (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (2 / 5 : ℝ) * (n : ℝ) - B ≤
            Real.logb 2 (K : ℝ)) :=
  exists_finite_classical_strong_unitary_universal_qubit_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

/-- The joint almost-every quantum-footprint logarithm retains the same
fixed-target threshold and exactly the three original geometry arguments. -/
theorem exists_ae_finite_classical_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
        ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          (T ∈ finitePureScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finiteMixedScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finitePurePVMScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) ∧
          (T ∈ finiteMixedPVMScoreReachable (2 ^ n) K ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - (3 / 5 : ℝ) * (n : ℝ) - B ≤
              Real.logb 2 (K : ℝ)) :=
  exists_ae_finite_classical_qubit_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

end NLQCLean.ClassicalCommunication
