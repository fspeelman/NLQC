import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.RectangularDiagonalAlmostEvery
import NLQCLean.Bounds.BorelClassicalRates
import NLQCLean.Models.ClassicalCommunication.BorelLocalRestriction
import NLQCLean.Models.ClassicalCommunication.RectangularDiagonalRestriction

/-!
# Rectangular diagonal gates with free standard-Borel classical messages

Actual standard-Borel protocols with free classical messages, pure or with a
common-map finite mixed resource, are restricted to the two lowest levels of
each party by `StandardBorelClassicalProtocol.restrictLocal`. The resource and
both quantum messages are unchanged, and the operational channel is the
genuine physical restriction of the original channel, so normalized diamond
error contracts. The two-qubit controlled-phase rate then gives, for almost
every rectangular diagonal phase, `log(1/ε) ≤ C Kq¹⁰` and quantum-footprint
coefficient `1/10` below a target-dependent threshold.

The source is `thm:diagonal` (ii) and its restriction paragraph in the robust
companion, `fixed-dimension.tex`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory ClassicalCommunication

/-- Two-qubit controlled phases with free standard-Borel classical messages:
one target threshold before every budget and every pure or common-map mixed
Borel protocol with normalized diamond error. -/
theorem exists_ae_borelControlledPhase_log_bound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB]
          [MeasurableSpace σA] [MeasurableSpace σB]
          [StandardBorelSpace σA] [StandardBorelSpace σB],
        ∀ P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB (Fin 2) (Fin 2),
        (P.HasQuantumFootprint Kq →
          diamondError P.operationalChannel.toLinearMap (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          diamondError (P.mixedOperationalChannel m) (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨256 / c ^ 2, by positivity, ?_⟩
  filter_upwards [hae] with θ hθ
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hθ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro Kq ε hε hε₀ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have htransfer (hreach : controlledPhaseTarget θ ∈ pureReachable 2 (2 ^ 4 * Kq ^ 5) ε) :
      Real.log (1 / ε) ≤ (256 / c ^ 2) * (Kq : ℝ) ^ 10 := by
    apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL
    have h := (hcharged (2 ^ 4 * Kq ^ 5) ε hε hε₀).1 hreach
    simpa only [show 2 ^ 4 = (16 : ℕ) by norm_num,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  exact ⟨fun hK he => htransfer
      (P.mem_pureReachable_of_quantumFootprint_diamondError
        (controlledPhaseTarget θ) (by decide) hK he),
    fun n m hK he => htransfer
      (P.mem_pureReachable_of_mixedQuantumFootprint_diamondError
        m (controlledPhaseTarget θ) (by decide) hK he)⟩

/-- Alice's corrected two-level output channel, as an actual operation. -/
noncomputable def rectangularDiagonalOutputA {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    MatrixOperation (Fin dA) (Fin 2) :=
  (channelOf (rectangularDiagonalDecoderA hA hB θ)).toContinuousLinearMap

/-- Bob's corrected two-level output channel, as an actual operation. -/
noncomputable def rectangularDiagonalOutputB {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    MatrixOperation (Fin dB) (Fin 2) :=
  (channelOf (rectangularDiagonalDecoderB hA hB θ)).toContinuousLinearMap

theorem rectangularDiagonalOutputA_completelyPositive {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    CompletelyPositive (rectangularDiagonalOutputA hA hB θ).toLinearMap :=
  correctedTwoLevelDecoderChannel_completelyPositive hA (qubitPhaseCorrectionA_unitary _).1

theorem rectangularDiagonalOutputB_completelyPositive {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    CompletelyPositive (rectangularDiagonalOutputB hA hB θ).toLinearMap :=
  correctedTwoLevelDecoderChannel_completelyPositive hB (qubitPhaseCorrectionB_unitary _).1

theorem rectangularDiagonalOutputA_trace {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) (X : Matrix (Fin dA) (Fin dA) ℂ) :
    (rectangularDiagonalOutputA hA hB θ X).trace = X.trace :=
  correctedTwoLevelDecoderChannel_trace hA (qubitPhaseCorrectionA_unitary _).1 X

theorem rectangularDiagonalOutputB_trace {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) (X : Matrix (Fin dB) (Fin dB) ℂ) :
    (rectangularDiagonalOutputB hA hB θ X).trace = X.trace :=
  correctedTwoLevelDecoderChannel_trace hB (qubitPhaseCorrectionB_unitary _).1 X

namespace ClassicalCommunication.StandardBorelClassicalProtocol

variable {dA dB : ℕ} [NeZero dA] [NeZero dB] {ρA ρB κA κB μA μB σA σB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB]
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable (P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
  σA σB (Fin dA) (Fin dB))

/-- The actual Borel protocol restricted to the two lowest levels, followed by
the corrected two-level output channels. -/
noncomputable def restrictRectangularDiagonal (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) :
    StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB (Fin 2) (Fin 2) :=
  P.restrictLocal (twoLevelIsometry hA) (twoLevelIsometry hB)
    (twoLevelIsometry_isometry hA) (twoLevelIsometry_isometry hB)
    (rectangularDiagonalOutputA hA hB θ) (rectangularDiagonalOutputB hA hB θ)
    (rectangularDiagonalOutputA_completelyPositive hA hB θ)
    (rectangularDiagonalOutputB_completelyPositive hA hB θ)
    (rectangularDiagonalOutputA_trace hA hB θ) (rectangularDiagonalOutputB_trace hA hB θ)

theorem restrictRectangularDiagonal_operationalChannel (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) :
    (P.restrictRectangularDiagonal hA hB θ).operationalChannel.toLinearMap =
      rectangularDiagonalRestrictedChannel hA hB θ P.operationalChannel.toLinearMap := by
  rw [restrictRectangularDiagonal, restrictLocal_operationalChannel_toLinearMap,
    rectangularDiagonalRestrictedChannel, rectangularDiagonalDecoderChannel_eq_local_tensor]
  rfl

theorem restrictRectangularDiagonal_mixedOperationalChannel (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ) {n : ℕ} (m : MixedResource ρA ρB n) :
    (P.restrictRectangularDiagonal hA hB θ).mixedOperationalChannel m =
      rectangularDiagonalRestrictedChannel hA hB θ (P.mixedOperationalChannel m) := by
  rw [restrictRectangularDiagonal, restrictLocal_mixedOperationalChannel,
    rectangularDiagonalRestrictedChannel, rectangularDiagonalDecoderChannel_eq_local_tensor]
  rfl

end ClassicalCommunication.StandardBorelClassicalProtocol

/-- **Rectangular diagonal gates, free standard-Borel classical messages.**
For almost every rectangular diagonal phase there is a threshold below which
every pure or common-map mixed standard-Borel protocol of quantum footprint
`Kq` and normalized diamond error `ε` has `log(1/ε) ≤ C Kq¹⁰`. -/
theorem exists_ae_borelRectangularDiagonal_log_bound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB]
            [MeasurableSpace σA] [MeasurableSpace σB]
            [StandardBorelSpace σA] [StandardBorelSpace σB],
          ∀ P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB (Fin dA) (Fin dB),
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel.toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) := by
  obtain ⟨C, hC, hae⟩ := exists_ae_borelControlledPhase_log_bound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    hGeom
  refine ⟨C, hC, fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro Kq ε hε hee ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  let Q := P.restrictRectangularDiagonal hA hB θ
  have hbound := hphase Kq ε hε hee ρA ρB κA κB μA μB σA σB Q
  have hgate := controlledPhase_rectangularAlternatingAngleMod hA hB θ
  refine ⟨fun hK he => ?_, fun n m hK he => ?_⟩
  · apply hbound.1 hK
    rw [hgate, P.restrictRectangularDiagonal_operationalChannel hA hB θ]
    exact (diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _).trans he
  · apply hbound.2 n m hK
    rw [hgate, P.restrictRectangularDiagonal_mixedOperationalChannel hA hB θ m]
    exact (diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _).trans he

/-- Quantum-footprint coefficient `1/10` for rectangular diagonal gates with
free standard-Borel classical messages. -/
theorem exists_ae_borelRectangularDiagonal_qubit_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB]
            [MeasurableSpace σA] [MeasurableSpace σB]
            [StandardBorelSpace σA] [StandardBorelSpace σB],
          ∀ P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB (Fin dA) (Fin dB),
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel.toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) := by
  obtain ⟨C, hC, hae⟩ :=
    exists_ae_borelRectangularDiagonal_log_bound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [hae dA dB hA hB] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro Kq ε hε hee ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have harithmetic (hlog : Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (Kq : ℝ) := by
    have hK : 0 < Kq := by
      by_contra hn
      have hz : Kq = 0 := Nat.eq_zero_of_not_pos hn
      rw [hz] at hlog
      rw [Nat.cast_zero, zero_pow (by decide : (10 : ℕ) ≠ 0), mul_zero] at hlog
      linarith
    simpa using quantumFootprint_log_of_tenth_power_bound (a := 0) (n := 0)
      hC hL hK (by simpa using hlog)
  have hbound := hphase Kq ε hε hee ρA ρB κA κB μA μB σA σB P
  exact ⟨fun hK he => harithmetic (hbound.1 hK he),
    fun n m hK he => harithmetic (hbound.2 n m hK he)⟩

/-- The Borel rectangular quantum-footprint rate. -/
theorem exists_ae_borelRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB]
            [MeasurableSpace σA] [MeasurableSpace σB]
            [StandardBorelSpace σA] [StandardBorelSpace σB],
          ∀ P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB (Fin dA) (Fin dB),
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel.toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) :=
  exists_ae_borelRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- **Borel LOSCC rectangular rate.** With only classical messages, resource
dimensions of product at most `2^q` force `q ≥ (1/5) log₂ log(1/ε) - B`. -/
theorem exists_ae_borelLOSCCRectangularDiagonal_qubit_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB]
            [MeasurableSpace σA] [MeasurableSpace σB]
            [StandardBorelSpace σA] [StandardBorelSpace σB],
          ∀ P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB (Fin dA) (Fin dB),
          Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
          Fintype.card μA = 1 → Fintype.card μB = 1 →
          (diamondError P.operationalChannel.toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n),
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨C, hC, hae⟩ :=
    exists_ae_borelRectangularDiagonal_log_bound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨max 0 ((1 / 5 : ℝ) * Real.logb 2 C), le_max_left _ _, fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [hae dA dB hA hB] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro q ε hε hee ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hq hμA hμB
  let R := min (Fintype.card ρA) (Fintype.card ρB)
  have hR : R ^ 2 ≤ 2 ^ q :=
    (min_resource_card_sq_le_product (ρA := ρA) (ρB := ρB)).trans hq
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hfoot : P.HasQuantumFootprint R := by
    apply (hasFootprint_iff R P.resource).mpr
    simpa only [hμA, hμB, mul_one] using
      le_min (schmidtRank_le_card_left P.resource) (schmidtRank_le_card_right P.resource)
  have hbound := hphase R ε hε hee ρA ρB κA κB μA μB σA σB P
  have harithmetic : Real.log (1 / ε) ≤ C * (R : ℝ) ^ 10 →
      (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
        max 0 ((1 / 5 : ℝ) * Real.logb 2 C) ≤ (q : ℝ) :=
    fun h => qubit_lower_of_tenth_power_and_squared_footprint hC hL h hR
  refine ⟨fun he => harithmetic (hbound.1 hfoot he), fun n m he => ?_⟩
  have hfootm : P.HasMixedQuantumFootprint m R := by
    apply (P.hasMixedQuantumFootprint_iff_rank_bound m R).mpr
    exact ⟨R, m.schmidtNumberLE_min_resource_card,
      by simpa only [hμA, hμB, mul_one] using (le_refl R)⟩
  exact harithmetic (hbound.2 n m hfootm he)

/-- The Borel LOSCC rectangular rate. -/
theorem exists_ae_borelLOSCCRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB]
            [MeasurableSpace σA] [MeasurableSpace σB]
            [StandardBorelSpace σA] [StandardBorelSpace σB],
          ∀ P : StandardBorelClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB (Fin dA) (Fin dB),
          Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
          Fintype.card μA = 1 → Fintype.card μB = 1 →
          (diamondError P.operationalChannel.toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n),
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) :=
  exists_ae_borelLOSCCRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean
