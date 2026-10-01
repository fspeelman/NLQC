import NLQCLean.Exact.ControlledPhaseExclusion
import NLQCLean.Models.ClassicalCommunication.FiniteOutputRestriction

/-!
# Exact finite implementations under local logical restriction

Local input embeddings and local output Stinespring maps restrict the actual
operational channel. If the explicitly restricted ideal channel is a
two-qubit controlled phase, exact implementation forces algebraicity of its
exponential phase. The original logical and internal register types are
arbitrary finite types; mixed implementations retain their common maps and
the same actual resource decomposition throughout the construction.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ u₁₄

open Matrix ClassicalCommunication
open scoped Kronecker

variable {ιA : Type u₁} {ιB : Type u₂} {ιA' : Type u₃} {ιB' : Type u₄}
variable {ρA : Type u₅} {ρB : Type u₆} {κA : Type u₇} {κB : Type u₈}
variable {μA : Type u₉} {μB : Type u₁₀} {εA : Type u₁₁} {εB : Type u₁₂}
variable {δA : Type u₁₃} {δB : Type u₁₄}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [Fintype δA] [Fintype δB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq δA] [DecidableEq δB]

/-- The one-outcome specialization preserves the actual common-map mixed
channel for every resource decomposition, regardless of the pure resource
used to initialize the protocol structure. -/
theorem ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol_arbitrary_logical
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) :
    (FiniteClassicalProtocol.ofPureProtocol P).mixedOperationalChannel m =
      m.mixedChannel P.encA P.encB P.decA P.decB := by
  rw [FiniteClassicalProtocol.mixedOperationalChannel, MixedResource.mixedChannel]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [FiniteClassicalProtocol.operationalChannel, Fintype.sum_unique]
  rfl

/-- Exact implementation on arbitrary original finite registers, followed
by local input and output restriction to a controlled phase, forces an
algebraic exponential phase. The ideal restriction equation is explicit. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_exact_local_restriction
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (EA : Matrix ιA (Fin 2) ℂ) (EB : Matrix ιB (Fin 2) ℂ)
    (HA : Matrix (Fin 2 × δA) ιA' ℂ) (HB : Matrix (Fin 2 × δB) ιB' ℂ)
    (hEA : IsIsometry EA) (hEB : IsIsometry EB)
    (hHA : IsIsometry HA) (hHB : IsIsometry HB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} {θ : ℝ}
    (hIdeal : (tensorChannels (channelOf HA) (channelOf HB)).comp
      ((adConj U).comp (adConj (EA ⊗ₖ EB))) = adConj (controlledPhase θ))
    (hP : P.PerformsUnitary U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  let R := ((FiniteClassicalProtocol.ofPureProtocol P).precomposeLogicalInputs
    EA EB hEA hEB).postcomposeLogicalOutputs HA HB hHA hHB
  have hR : R.operationalChannel = adConj (controlledPhase θ) := by
    change P.operationalChannel = adConj U at hP
    dsimp only [R]
    rw [FiniteClassicalProtocol.postcomposeLogicalOutputs_operationalChannel,
      FiniteClassicalProtocol.precomposeLogicalInputs_operationalChannel,
      FiniteClassicalProtocol.operationalChannel_ofPureProtocol, hP]
    exact hIdeal
  have hQ : R.coherentProtocol.PerformsUnitary (controlledPhase θ) := by
    change R.coherentProtocol.operationalChannel = adConj (controlledPhase θ)
    rw [FiniteClassicalProtocol.coherentProtocol_operationalChannel, hR]
  exact R.coherentProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase hQ

/-- Common-map finite-mixed exactness survives the same local restriction.
The proof preserves the actual convex channel mixture and its shared maps,
then invokes the checked two-qubit exactness implication. -/
theorem MixedResource.isAlgebraic_exp_angle_of_exact_local_restriction
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ}
    {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (EA : Matrix ιA (Fin 2) ℂ) (EB : Matrix ιB (Fin 2) ℂ)
    (HA : Matrix (Fin 2 × δA) ιA' ℂ) (HB : Matrix (Fin 2 × δB) ιB' ℂ)
    (hEA : IsIsometry EA) (hEB : IsIsometry EB)
    (hHA : IsIsometry HA) (hHB : IsIsometry HB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} {θ : ℝ}
    (hIdeal : (tensorChannels (channelOf HA) (channelOf HB)).comp
      ((adConj U).comp (adConj (EA ⊗ₖ EB))) = adConj (controlledPhase θ))
    (hm : m.mixedChannel VA VB DA DB = adConj U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  let R := ((FiniteClassicalProtocol.ofPureProtocol P).precomposeLogicalInputs
    EA EB hEA hEB).postcomposeLogicalOutputs HA HB hHA hHB
  have hR : R.mixedOperationalChannel m = adConj (controlledPhase θ) := by
    dsimp only [R]
    rw [FiniteClassicalProtocol.postcomposeLogicalOutputs_mixedOperationalChannel,
      FiniteClassicalProtocol.precomposeLogicalInputs_mixedOperationalChannel,
      FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol_arbitrary_logical]
    change (tensorChannels (channelOf HA) (channelOf HB)).comp
      ((m.mixedChannel VA VB DA DB).comp (adConj (EA ⊗ₖ EB))) =
        adConj (controlledPhase θ)
    rw [hm]
    exact hIdeal
  have hQ : m.mixedChannel R.coherentProtocol.encA R.coherentProtocol.encB
      R.coherentProtocol.decA R.coherentProtocol.decB = adConj (controlledPhase θ) := by
    rw [← FiniteClassicalProtocol.mixedOperationalChannel_eq_coherentMixedChannel]
    exact hR
  exact m.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase
    R.coherentProtocol.encA_isometry R.coherentProtocol.encB_isometry
    R.coherentProtocol.decA_isometry R.coherentProtocol.decB_isometry hQ

end NLQCLean
