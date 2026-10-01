import NLQCLean.Models.ClassicalCommunication.BarycenterSupport
import NLQCLean.Models.ClassicalCommunication.FiniteMixed

/-!
# Actual high-score branch selection

An integrable score under arbitrary probability randomness has an actual
branch with score at least its mean on any full-measure good set. Applied to
families of actual finite protocols, this preserves a per-branch resource
cap. It does not preserve operational error or establish the representation
of the average channel for a standard-Borel instrument model.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- A score at least its mean is attained on the given full-measure good set.
No measurable-set assumption on that set, or maximum-attainment premise,
is required. -/
theorem exists_good_score_ge_integral (score : α → ℝ) (G : Set α)
    (hscore : Integrable score μ) (hG : ∀ᵐ a ∂μ, a ∈ G) :
    ∃ a ∈ G, (∫ b, score b ∂μ) ≤ score a := by
  classical
  have hmean := integral_mem_convexHull_image score G hscore hG
  by_contra hnone
  have hsub : score '' G ⊆ Iio (∫ b, score b ∂μ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact lt_of_not_ge (fun h => hnone ⟨a, ha, h⟩)
  exact (lt_irrefl (∫ b, score b ∂μ))
    ((convexHull_min hsub (convex_Iio _)) hmean)

section FiniteProtocols

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

/-- Arbitrary probability randomness in a family of actual finite protocols
admits an actual high-score branch satisfying the stipulated per-branch
quantum footprint. Only the score function's integrability is used here. -/
theorem exists_finite_protocol_branch_linearScore_ge
    (P : α → FiniteClassicalProtocol
      ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)
    (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (K : ℕ) (hscore : Integrable (fun a => S (P a).operationalChannel) μ)
    (hK : ∀ a, (P a).HasQuantumFootprint K) :
    ∃ a, (P a).HasQuantumFootprint K ∧
      (∫ b, S (P b).operationalChannel ∂μ) ≤ S (P a).operationalChannel := by
  obtain ⟨a, _, ha⟩ := exists_good_score_ge_integral μ
    (fun a => S (P a).operationalChannel) univ hscore (Filter.Eventually.of_forall (by simp))
  exact ⟨a, hK a, ha⟩

/-- First select an actual randomness branch, then an actual pure component
of its common-map finite mixture. The cap is imposed in every branch, not
on an expected resource cost, and neither selection preserves operational
error. The finite component count may depend on the branch. -/
theorem exists_finite_protocol_branch_component_linearScore_ge
    (P : α → FiniteClassicalProtocol
      ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)
    (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (n : α → ℕ) (m : ∀ a, MixedResource ρA ρB (n a))
    (K : ℕ) (hscore : Integrable (fun a => S ((P a).mixedOperationalChannel (m a))) μ)
    (hK : ∀ a, (P a).HasMixedQuantumFootprint (m a) K) :
    ∃ a, ∃ k : Fin (n a),
      ((P a).componentProtocol (m a) k).HasQuantumFootprint K ∧
      (∫ b, S ((P b).mixedOperationalChannel (m b)) ∂μ) ≤
        S ((P a).componentProtocol (m a) k).operationalChannel := by
  obtain ⟨a, _, ha⟩ := exists_good_score_ge_integral μ
    (fun a => S ((P a).mixedOperationalChannel (m a))) univ hscore
    (Filter.Eventually.of_forall (by simp))
  obtain ⟨k, hk, hcap⟩ :=
    (P a).exists_component_linearScore_ge_hasQuantumFootprint S (m a) (hK a)
  exact ⟨a, k, hcap, ha.trans hk⟩

end FiniteProtocols

end NLQCLean.ClassicalCommunication
