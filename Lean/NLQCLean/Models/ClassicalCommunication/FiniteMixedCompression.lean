import NLQCLean.Models.ClassicalCommunication.FiniteCompression
import NLQCLean.Models.ClassicalCommunication.FiniteMixed

/-!
# Finite common-map mixtures with free classical outcomes

An actual pure component is chosen with score at least the finite mixture's
score and within its Schmidt-number/message cap. The proved pure compression
then constructs an existing-model charged protocol. Component selection is
never asserted to preserve the mixture's channel or operational errors.
-/

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

variable {d K n : ℕ} {ρA ρB κA κB μA μB σA σB ηA ηB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq εA] [DecidableEq εB]

/-- Finite common-map mixed unitary score transfer through an actual
rank-capped component and the proved two-party outcome compression. -/
theorem mem_pureReachable_of_mixedQuantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (m : MixedResource ρA ρB n) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨k, hcomponent, hfoot⟩ :=
    P.exists_component_linearScore_ge_hasQuantumFootprint
      (unitaryScoreRealLinear (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) m hK
  apply (P.componentProtocol m k).mem_pureReachable_of_quantumFootprint U hd hfoot
  exact hscore.trans hcomponent

/-- Finite mixed PVM transfer retains the actual joint correct-label score. -/
theorem mem_purePVMReachable_of_mixedQuantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (m : MixedResource ρA ρB n) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  obtain ⟨k, hcomponent, hfoot⟩ :=
    P.exists_component_linearScore_ge_hasQuantumFootprint
      (pvmScoreRealLinear (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) m hK
  apply (P.componentProtocol m k).mem_purePVMReachable_of_quantumFootprint M hd hfoot
  exact hscore.trans hcomponent

/-- Original mixed diamond accuracy first gives a score bound using its
honest common-map coherent channel, before selecting a component. -/
theorem mem_pureReachable_of_mixedQuantumFootprint_diamondError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (m : MixedResource ρA ρB n) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs := m.scoreU_ge_of_diamondError_le
    P.coherentProtocol.encA_isometry P.coherentProtocol.encB_isometry
    P.coherentProtocol.decA_isometry P.coherentProtocol.decB_isometry
    (e := ε) (Matrix.mem_unitaryGroup_iff'.mp U.property)
    (by simpa only [P.mixedOperationalChannel_eq_coherentMixedChannel] using herror)
  rw [← P.mixedOperationalChannel_eq_coherentMixedChannel] at hs
  exact P.mem_pureReachable_of_mixedQuantumFootprint m U hd hK hs

/-- Joint-TV accuracy of the original mixed channel is used only for its
joint-label score, not as an error-preservation property of compression. -/
theorem mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (m : MixedResource ρA ρB n) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤ ε) :
    M ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs := m.one_sub_scorePVM_le_pvmTVError
    P.coherentProtocol.encA_isometry P.coherentProtocol.encB_isometry
    P.coherentProtocol.decA_isometry P.coherentProtocol.decB_isometry
    (Matrix.mem_unitaryGroup_iff'.mp M.property)
  rw [← P.mixedOperationalChannel_eq_coherentMixedChannel] at hs
  apply P.mem_purePVMReachable_of_mixedQuantumFootprint m M hd hK
  linarith

end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol
