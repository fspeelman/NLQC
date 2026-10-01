import NLQCLean.Models.ClassicalCommunication.FiniteMixedReindex
import NLQCLean.Models.ClassicalCommunication.FiniteReachability

/-! # Original finite registers in canonical classical score classes

Actual basis transport preserves the original channel and quantum footprint.
-/

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol
open Matrix
attribute [local implicit_reducible] Matrix
noncomputable section
variable {d K : ℕ} {ρA ρB κA κB μA μB σA σB ηA ηB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Exact basis relabeling gives canonical score membership at the original quantum cap. -/
theorem mem_finitePureScoreReachable_of_quantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)

    (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hs : 1 - ε ≤ scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel) :
    T ∈ finitePureScoreReachable d K ε := by
  let s : Fin 12 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card σA, Fintype.card σB,
    Fintype.card ηA, Fintype.card ηB, Fintype.card εA, Fintype.card εB]
  refine ⟨s, P.toFin, (P.quantumFootprint_toFin K).mpr hK, ?_⟩
  exact hs.trans (congrArg (fun C => scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) C)
    P.operationalChannel_toFin).symm.le

/-- Exact basis relabeling gives canonical score membership at the original quantum cap. -/
theorem mem_finiteMixedScoreReachable_of_mixedQuantumFootprint {n : ℕ}
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (m : MixedResource ρA ρB n)
    (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (hs : 1 - ε ≤ scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (P.mixedOperationalChannel m)) :
    T ∈ finiteMixedScoreReachable d K ε := by
  let s : Fin 12 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card σA, Fintype.card σB,
    Fintype.card ηA, Fintype.card ηB, Fintype.card εA, Fintype.card εB]
  refine ⟨s, n, m.reindexRegisters (Fintype.equivFin ρA).symm
    (Fintype.equivFin ρB).symm, P.toFin, (P.mixedQuantumFootprint_toFin m K).mpr hK, ?_⟩
  exact hs.trans (congrArg (fun C => scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) C)
    (P.mixedOperationalChannel_toFin m)).symm.le

/-- Exact basis relabeling gives canonical score membership at the original quantum cap. -/
theorem mem_finitePurePVMScoreReachable_of_quantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)

    (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hs : 1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel) :
    T ∈ finitePurePVMScoreReachable d K ε := by
  let s : Fin 12 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card σA, Fintype.card σB,
    Fintype.card ηA, Fintype.card ηB, Fintype.card εA, Fintype.card εB]
  refine ⟨s, P.toFin, (P.quantumFootprint_toFin K).mpr hK, ?_⟩
  exact hs.trans (congrArg (fun C => scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) C)
    P.operationalChannel_toFin).symm.le

/-- Exact basis relabeling gives canonical score membership at the original quantum cap. -/
theorem mem_finiteMixedPVMScoreReachable_of_mixedQuantumFootprint {n : ℕ}
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (m : MixedResource ρA ρB n)
    (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (hs : 1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (P.mixedOperationalChannel m)) :
    T ∈ finiteMixedPVMScoreReachable d K ε := by
  let s : Fin 12 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card σA, Fintype.card σB,
    Fintype.card ηA, Fintype.card ηB, Fintype.card εA, Fintype.card εB]
  refine ⟨s, n, m.reindexRegisters (Fintype.equivFin ρA).symm
    (Fintype.equivFin ρB).symm, P.toFin, (P.mixedQuantumFootprint_toFin m K).mpr hK, ?_⟩
  exact hs.trans (congrArg (fun C => scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) C)
    (P.mixedOperationalChannel_toFin m)).symm.le

end
end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol
