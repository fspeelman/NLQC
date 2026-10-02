import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.FiniteControlledPhaseLength
import NLQCLean.Approx.BorelClassicalSpectralFloors

/-!
# Outer length of controlled phases with free standard-Borel classical messages

`prop:phase-length`, free-classical part, in the source model: actual
standard-Borel protocols with pure or common-map mixed resources and measured
shared-randomness averages, with Choi infidelity (score deficit). The angle set
lies in the charged angle set at footprint `16 Kq⁵`, so its outer measure on a
compact semicircle interval `J` is at most `C_J exp(C Kq¹⁰) √ε`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open MeasureTheory ClassicalCommunication

/-- Angles in `J` whose controlled phase is reached by an actual Borel or
shared-random protocol of quantum footprint `Kq` and score deficit `ε`. -/
def borelControlledPhaseAngles (Kq : ℕ) (ε : ℝ) (J : Set ℝ) : Set ℝ :=
  {θ | θ ∈ J ∧ controlledPhaseTarget θ ∈
    borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} 2 Kq ε}

theorem borelControlledPhaseAngles_subset_charged (Kq : ℕ) (ε : ℝ) (J : Set ℝ) :
    borelControlledPhaseAngles.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} Kq ε J ⊆
      chargedControlledPhaseAngles (16 * Kq ^ 5) ε J := by
  rintro θ ⟨hθ, hreach⟩
  refine ⟨hθ, ?_⟩
  simpa only [show 2 ^ 4 = (16 : ℕ) by norm_num] using
    borelAllScoreReachable_subset_pureReachable (by decide : 0 < 2) ε hreach

/-- **`prop:phase-length`, free standard-Borel classical messages.** -/
theorem exists_borelControlledPhase_length_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ C_J : ℝ, 0 < C_J ∧ ∀ (Kq : ℕ), 1 ≤ Kq → ∀ (ε : ℝ), 0 < ε →
        volume (borelControlledPhaseAngles.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
          Kq ε (Set.Icc a b)) ≤
            ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) := by
  obtain ⟨C, hC, hlength⟩ := exists_chargedControlledPhase_length_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)
  refine ⟨256 * C, by linarith, ?_⟩
  intro a b hab hsemicircle
  obtain ⟨C_J, hCJ, hbound⟩ := hlength a b hab hsemicircle
  refine ⟨C_J, hCJ, fun Kq hKq ε hε => ?_⟩
  have hKbar : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hcharged := hbound (16 * Kq ^ 5) hKbar ε hε
  rw [finiteControlledPhase_charged_exponent_eq] at hcharged
  exact (measure_mono (borelControlledPhaseAngles_subset_charged Kq ε (Set.Icc a b))).trans
    hcharged

end NLQCLean
