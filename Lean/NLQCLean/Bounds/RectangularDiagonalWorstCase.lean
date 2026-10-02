import NLQCLean.Bounds.BorelRectangularDiagonal

/-!
# Worst-case rectangular diagonal bounds

`thm:diagonal` also asserts the bounds for the worst case over all diagonal
unitaries once `ε` is small. The almost-every statements give more: in each
dimension there is one fixed hard diagonal gate whose threshold applies to
every architecture and budget. Any budget that implements every diagonal
unitary to error `ε` below that threshold in particular implements this gate,
and so obeys the same bound.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory ClassicalCommunication

instance rectangularPhaseMeasure_isProbabilityMeasure (dA dB : ℕ) :
    IsProbabilityMeasure (rectangularPhaseMeasure dA dB) := by
  unfold rectangularPhaseMeasure
  infer_instance

/-- Worst case, charged footprint, coefficient `1/2`: one hard rectangular diagonal gate. -/
theorem exists_hard_chargedRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∃ θ : Fin dA × Fin dB → ℝ,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            (Fin dA) (Fin dB) εA εB,
          (P.HasFootprint K →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n) (R : ℕ), m.schmidtNumberLE R →
            R * Fintype.card μA * Fintype.card μB ≤ K →
            diamondError (m.mixedChannel P.encA P.encB P.decA P.decB)
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨B, hB, h⟩ := exists_ae_chargedRectangularDiagonal_qubit_bound
  exact ⟨B, hB, fun dA dB hA hB => (h dA dB hA hB).exists⟩

/-- Worst case, finite free classical messages, quantum-footprint coefficient `1/10`. -/
theorem exists_hard_finiteRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∃ θ : Fin dA × Fin dB → ℝ,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) := by
  obtain ⟨B, hB, h⟩ := exists_ae_finiteRectangularDiagonal_qubit_bound
  exact ⟨B, hB, fun dA dB hA hB => (h dA dB hA hB).exists⟩

/-- Worst case, finite LOSCC, initial-resource-qubit coefficient `1/5`. -/
theorem exists_hard_finiteLOSCCRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∃ θ : Fin dA × Fin dB → ℝ,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
          Fintype.card μA = 1 → Fintype.card μB = 1 →
          (diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n),
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨B, hB, h⟩ := exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound
  exact ⟨B, hB, fun dA dB hA hB => (h dA dB hA hB).exists⟩

/-- Worst case, free standard-Borel classical messages, coefficient `1/10`. -/
theorem exists_hard_borelRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∃ θ : Fin dA × Fin dB → ℝ,
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
  obtain ⟨B, hB, h⟩ := exists_ae_borelRectangularDiagonal_qubit_bound
  exact ⟨B, hB, fun dA dB _ _ hA hB => (h dA dB hA hB).exists⟩

/-- Worst case, standard-Borel LOSCC, coefficient `1/5`. -/
theorem exists_hard_borelLOSCCRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∃ θ : Fin dA × Fin dB → ℝ,
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
  obtain ⟨B, hB, h⟩ := exists_ae_borelLOSCCRectangularDiagonal_qubit_bound
  exact ⟨B, hB, fun dA dB _ _ hA hB => (h dA dB hA hB).exists⟩

end NLQCLean
