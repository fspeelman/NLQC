import NLQCLean.Models.ClassicalCommunication.BranchSelection
import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression

/-!
# Compression from integrated finite-branch scores

Arbitrary probability randomness may vary the actual finite local maps and
the finite common-map mixed decomposition. A cap in every branch and an
integrable expected target score select an actual branch and pure component,
then the proved finite compression supplies an actual charged protocol.
These are integrated-score statements, not representation theorems for an
averaged CP-valued channel or standard-Borel outcome instruments.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix

attribute [local implicit_reducible] Matrix

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {d K : ℕ} {ρA ρB κA κB μA μB σA σB ηA ηB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq εA] [DecidableEq εB]

/-- A quantum cap in every actual finite mixed branch and its integrated
unitary score yield an actual charged score implementation. No enlarged
purification of random labels or expected resource cap is used. -/
theorem mem_pureReachable_of_integrated_finite_mixed_score
    (P : α → FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (n : α → ℕ) (m : ∀ a, MixedResource ρA ρB (n a))
    (U : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d)
    (hscore : Integrable
      (fun a => scoreU (U : Matrix _ _ ℂ) ((P a).mixedOperationalChannel (m a))) μ)
    (hK : ∀ a, (P a).HasMixedQuantumFootprint (m a) K)
    (hmean : 1 - ε ≤ ∫ a,
      scoreU (U : Matrix _ _ ℂ) ((P a).mixedOperationalChannel (m a)) ∂μ) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  obtain ⟨a, k, hcap, hge⟩ := exists_finite_protocol_branch_component_linearScore_ge μ
    P (unitaryScoreRealLinear (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
    n m K hscore hK
  change (∫ b, scoreU (U : Matrix _ _ ℂ) ((P b).mixedOperationalChannel (m b)) ∂μ) ≤
    scoreU (U : Matrix _ _ ℂ) ((P a).componentProtocol (m a) k).operationalChannel at hge
  exact ((P a).componentProtocol (m a) k).mem_pureReachable_of_quantumFootprint
    U hd hcap (hmean.trans hge)

/-- The analogous integrated score uses the existing two-sided joint-label
PVM score and yields an actual charged PVM score protocol. -/
theorem mem_purePVMReachable_of_integrated_finite_mixed_score
    (P : α → FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (n : α → ℕ) (m : ∀ a, MixedResource ρA ρB (n a))
    (M : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d)
    (hscore : Integrable
      (fun a => scorePVM (M : Matrix _ _ ℂ) ((P a).mixedOperationalChannel (m a))) μ)
    (hK : ∀ a, (P a).HasMixedQuantumFootprint (m a) K)
    (hmean : 1 - ε ≤ ∫ a,
      scorePVM (M : Matrix _ _ ℂ) ((P a).mixedOperationalChannel (m a)) ∂μ) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  obtain ⟨a, k, hcap, hge⟩ := exists_finite_protocol_branch_component_linearScore_ge μ
    P (pvmScoreRealLinear (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
    n m K hscore hK
  change (∫ b, scorePVM (M : Matrix _ _ ℂ) ((P b).mixedOperationalChannel (m b)) ∂μ) ≤
    scorePVM (M : Matrix _ _ ℂ) ((P a).componentProtocol (m a) k).operationalChannel at hge
  exact ((P a).componentProtocol (m a) k).mem_purePVMReachable_of_quantumFootprint
    M hd hcap (hmean.trans hge)

end NLQCLean.ClassicalCommunication
