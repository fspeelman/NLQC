import NLQCLean.Bounds.ExplicitControlledPhase
import NLQCLean.Arithmetic.GelfondAngleMeasure

/-!
# Theorem E for every nonzero real algebraic angle

The forms of `thm:explicit` in `Bounds/ExplicitControlledPhase`, applied to the polynomial-type
transcendence measure `polynomialTypeTranscendenceMeasureExpAngle` (Gelfond's method for
`e^{iθ}`).
-/

namespace NLQCLean

open MvPolynomial PhysicalPolynomial ExplicitGate ClassicalCommunication

/-- **Theorem E (`thm:explicit`), least-deficit form.** For every nonzero real
algebraic angle `θ` there is `C_E > 0` with
`exp(-exp(C_E K²)) ≤ g_K(θ)` for every footprint `K ≥ 1`. -/
theorem exists_explicit_controlledPhaseLeastDeficit_lower_bound
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ K : ℕ, 1 ≤ K →
      Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ controlledPhaseLeastDeficit K θ :=
  exists_explicit_controlledPhaseLeastDeficit_lower_bound_of_transcendenceMeasure
    polynomialTypeTranscendenceMeasureExpAngle hθ0 hθ

/-- **Theorem E, protocol form.** Every pure protocol of footprint at most `K ≥ 1`
implementing the controlled phase with Choi infidelity (score deficit) at most `ε`,
and every common-map mixed protocol, has `ε ≥ exp(-exp(C_E K²))`; with free
standard-Borel classical messages and quantum footprint `Kq ≥ 1`,
`ε ≥ exp(-exp(256 C_E Kq¹⁰))`. -/
theorem exists_explicit_controlledPhase_protocol_bound
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ CE : ℝ, 0 < CE ∧
      (∀ {ρA ρB κA κB μA μB εA εB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
        (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
        {K : ℕ} {ε : ℝ}, 1 ≤ K → P.HasFootprint K →
        1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
        Real.exp (-Real.exp (CE * (K : ℝ) ^ 2)) ≤ ε) ∧
      (∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel.toLinearMap →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            Real.exp (-Real.exp (256 * CE * (Kq : ℝ) ^ 10)) ≤ ε))) :=
  exists_explicit_controlledPhase_protocol_bound_of_transcendenceMeasure
    polynomialTypeTranscendenceMeasureExpAngle hθ0 hθ

/-- **Theorem E, iterated-logarithm form.** For `0 < ε < 1/e`, a charged
footprint `K ≥ 1` reaching least deficit at most `ε` satisfies
`log₂ K ≥ ½ log₂ ln ln(1/ε) - b`. -/
theorem exists_explicit_controlledPhase_iterated_log_bound
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (K : ℕ) (ε : ℝ), 1 ≤ K → 0 < ε → ε < Real.exp (-1) →
      controlledPhaseLeastDeficit K θ ≤ ε →
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 K :=
  exists_explicit_controlledPhase_iterated_log_bound_of_transcendenceMeasure
    polynomialTypeTranscendenceMeasureExpAngle hθ0 hθ

/-- **Theorem E, quantum-footprint iterated-logarithm form.** With free
standard-Borel classical messages, for `0 < ε < 1/e`, every pure or common-map
mixed protocol of quantum footprint `Kq ≥ 1` and score deficit at most `ε`
satisfies `log₂ Kq ≥ (1/10) log₂ ln ln(1/ε) - b`. In LOSCC `Kq` is the
Schmidt number of the resource. -/
theorem exists_explicit_controlledPhase_quantum_iterated_log_bound
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ {ρA ρB κA κB μA μB σA σB : Type*}
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB]
        [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
        (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
          (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq → 0 < ε → ε < Real.exp (-1) →
        ((P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel.toLinearMap →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 Kq) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 Kq)) :=
  exists_explicit_controlledPhase_quantum_iterated_log_bound_of_transcendenceMeasure
    polynomialTypeTranscendenceMeasureExpAngle hθ0 hθ

end NLQCLean
