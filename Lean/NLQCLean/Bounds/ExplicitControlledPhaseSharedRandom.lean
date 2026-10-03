import NLQCLean.Bounds.ExplicitControlledPhaseTranscript
import NLQCLean.Models.ClassicalCommunication.BorelSharedRandomness
import NLQCLean.Models.ClassicalCommunication.BranchSelection

/-!
# The explicit bound for `C₁` with free shared randomness

Shared randomness under uniform budgets (`thm:explicit`, last step of the proof): select a seed
whose score is at least the average and which satisfies the almost-everywhere Schmidt-number
and quantum-footprint caps, then apply the standard-Borel bound
`ε ≥ exp(-exp(C R⁴ Kq²))` to that seed's protocol.
-/

namespace NLQCLean

open MeasureTheory ClassicalCommunication StandardBorelClassicalProtocol

noncomputable section

noncomputable local instance srMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance srMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (srMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance srMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance srMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance srOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance srOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

/-- **`eq:explicit-quantum-tradeoff` with free shared randomness.** Unconditionally, there is
`C > 0` such that every standard-Borel free-classical protocol for `C₁` with measurable shared
randomness, almost every branch of which has resource Schmidt number at most `R` (pure branches)
or common-map mixed resource of Schmidt number at most `R`, and quantum footprint at most `Kq`,
and whose averaged channel has score deficit at most `ε`, satisfies `ε ≥ exp(-exp(C R⁴ Kq²))`. -/
theorem exists_explicit_controlledPhase_one_sharedRandom_quantum_tradeoff :
    ∃ CE : ℝ, 0 < CE ∧ ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      {ρA ρB κA κB μA μB σA σB : α → Type*}
      [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)] [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
      [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
      [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)] [∀ a, DecidableEq (κA a)]
      [∀ a, DecidableEq (κB a)] [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
      [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
      [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
      (P : ∀ a, StandardBorelClassicalProtocol (Fin 2) (Fin 2) (ρA a) (ρB a) (κA a) (κB a)
        (μA a) (μB a) (σA a) (σB a) (Fin 2) (Fin 2)) {R Kq : ℕ} {ε : ℝ},
      (AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
        (∀ᵐ a ∂μ, schmidtRank (P a).resource ≤ R ∧ (P a).HasQuantumFootprint Kq) →
        1 - ε ≤ scoreU (controlledPhase 1) (sharedRandomOperationalChannel μ P).toLinearMap →
        Real.exp (-Real.exp (CE * ((R : ℝ) ^ 4 * (Kq : ℝ) ^ 2))) ≤ ε) ∧
      (∀ {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
        AEStronglyMeasurable (mixedBranchOperation P m) μ →
        (∀ᵐ a ∂μ, (m a).schmidtNumberLE R ∧ (P a).HasMixedQuantumFootprint (m a) Kq) →
        1 - ε ≤ scoreU (controlledPhase 1) (mixedSharedRandomOperationalChannel μ P m).toLinearMap →
        Real.exp (-Real.exp (CE * ((R : ℝ) ^ 4 * (Kq : ℝ) ^ 2))) ≤ ε) := by
  obtain ⟨CE, hCE, hB⟩ := exists_explicit_controlledPhase_one_borel_quantum_tradeoff
  refine ⟨CE, hCE, ?_⟩
  intro α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P R Kq ε
  let S := unitaryScoreRealLinear (controlledPhase 1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  constructor
  · intro hP hgood hs
    have hint := (continuousMatrixOperationRealScore S).integrable_comp
      (integrable_sharedRandom_channelFamily μ P hP)
    obtain ⟨a, ⟨hR, hK⟩, hsc⟩ := exists_good_score_ge_integral μ
      (fun a => S (P a).operationalChannel.toLinearMap)
      {a | schmidtRank (P a).resource ≤ R ∧ (P a).HasQuantumFootprint Kq} hint hgood
    have hav := linearScore_sharedRandomOperationalChannel μ P hP S
    have hs' : 1 - ε ≤ scoreU (controlledPhase 1) (P a).operationalChannel.toLinearMap := by
      refine hs.trans ?_
      change S (sharedRandomOperationalChannel μ P).toLinearMap ≤ S (P a).operationalChannel.toLinearMap
      rw [hav]
      exact hsc
    exact (hB (P a)).1 hR hK hs'
  · intro n m hP hgood hs
    have hint := (continuousMatrixOperationRealScore S).integrable_comp
      (integrable_mixedSharedRandom_channelFamily μ P m hP)
    obtain ⟨a, ⟨hR, hK⟩, hsc⟩ := exists_good_score_ge_integral μ
      (fun a => S ((P a).mixedOperationalChannel (m a)))
      {a | (m a).schmidtNumberLE R ∧ (P a).HasMixedQuantumFootprint (m a) Kq} hint hgood
    have hav := linearScore_mixedSharedRandomOperationalChannel μ P m hP S
    have hs' : 1 - ε ≤ scoreU (controlledPhase 1) ((P a).mixedOperationalChannel (m a)) := by
      refine hs.trans ?_
      change S (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤
        S ((P a).mixedOperationalChannel (m a))
      rw [hav]
      exact hsc
    exact (hB (P a)).2 (n a) (m a) hR hK hs'

end

end NLQCLean
