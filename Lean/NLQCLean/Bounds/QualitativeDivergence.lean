import NLQCLean.Models.CompactForward
import NLQCLean.Exact.ScalarCriticalValues

/-!
# Unconditional qualitative unitary divergence

One target is chosen by scalar Sard before any budget. Exact compression
places all budget-K channels in finitely many compact physical families.
Their scores attain a maximum strictly below one. Affinity gives the same
gap for finite mixed resources with the prescribed Schmidt-number footprint.
The metric is normalized Choi infidelity; no effective rate is asserted.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix
open scoped Matrix.Norms.Frobenius

/-- A uniform normalized Choi gap for all pure protocols of footprint at most K.
Every internal finite register type is quantified after the gap. -/
def PureScoreGap {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB),
    P.HasFootprint K → scoreU U P.operationalChannel ≤ 1 - e

/-- The same gap for finite mixed decompositions of bounded Schmidt number.
Only the common component rank and both complete message dimensions are charged;
the local support dimension of a mixed resource is unrestricted. -/
def MixedScoreGap {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
    ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
      scoreU U (m.mixedChannel VA VB DA DB) ≤ 1 - e

/-- Score affinity averages the common pure gap over the given resource decomposition. -/
theorem PureScoreGap.mixed {d K : ℕ} {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e) :
    MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  rw [m.scoreU_mixedChannel VA VB DA DB U]
  calc
    ∑ k, m.weight k * scoreU U (operationalChannel (m.component k) VA VB DA DB)
        ≤ ∑ k, m.weight k * (1 - e) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (m.weight_nonneg k)
      let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB :=
        ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
      apply h ρA ρB κA κB μA μB εA εB P
      exact (hasFootprint_iff K (m.component k)).mpr
        ((Nat.mul_le_mul_right (Fintype.card μB)
          (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hK)
    _ = 1 - e := by rw [← Finset.sum_mul, m.weight_sum, one_mul]

/-- The exact-impossibility theorem excludes score one at every point of a finite physical shape. -/
theorem shapeScores_lt_one {d : ℕ} [NeZero d]
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d)
    (s : Fin 8 → ℕ) {v : ℝ} (hv : v ∈ shapeScores U s) : v < 1 := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact (PhysicalBlocks.toProtocol x hx).scoreU_lt_one_of_purity_not_mem hU hN

/-- The artificial zero and every physical score in the finite box are below one. -/
theorem boundedShapeScores_lt_one {d : ℕ} [NeZero d]
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d)
    (K : ℕ) {v : ℝ} (hv : v ∈ boundedShapeScores U K) : v < 1 := by
  rcases hv with hv | hv
  · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hv
    exact shapeScores_lt_one hU hN _ hs
  · have : v = 0 := hv
    simp [this]

/-- An upper bound on the finite compact family bounds every pure protocol. -/
theorem pureScoreGap_of_upperBound {d K : ℕ} (hd : 2 ≤ d)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {M : ℝ}
    (hM : M ∈ upperBounds (boundedShapeScores U K)) : PureScoreGap U K (1 - M) := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  have hle := hM (P.score_mem_boundedShapeScores hd U K hP)
  linarith

/-- Compactness turns the strict score-one exclusion into a common positive gap.
The target is an input chosen independently of K. -/
theorem exists_score_gap_of_purity_not_mem {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d)
    (K : ℕ) : ∃ e : ℝ, 0 < e ∧ PureScoreGap U K e ∧ MixedScoreGap U K e := by
  obtain ⟨M, hM⟩ := (isCompact_boundedShapeScores U K).exists_isGreatest
    (boundedShapeScores_nonempty U K)
  have hlt : M < 1 := boundedShapeScores_lt_one hU hN K hM.1
  exact ⟨1 - M, sub_pos.mpr hlt, pureScoreGap_of_upperBound hd hM.2,
    (pureScoreGap_of_upperBound hd hM.2).mixed⟩

/-- **Pure and finite-mixed gaps in one controlled-phase family.** The parameter is
chosen before every budget, accuracy gap, architecture, and mixed decomposition.
There is no additional mathematical hypothesis. -/
theorem exists_phase_qualitative_gap (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ t : ℝ, t ^ 2 ≤ 1 ∧ UnitaryTarget (phaseFamily d t) ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧
        PureScoreGap (phaseFamily d t) K e ∧ MixedScoreGap (phaseFamily d t) K e := by
  obtain ⟨t, ht, hN⟩ := exists_phase_purity_not_mem d hd
  have hU : UnitaryTarget (phaseFamily d t) :=
    ⟨(phaseFamily_unitary ht).1, (phaseFamily_unitary ht).2⟩
  exact ⟨t, ht, hU, fun K => exists_score_gap_of_purity_not_mem hd hU hN K⟩

/-- **Unconditional qualitative divergence for pure and finite mixed resources.**
For every d ≥ 2, one unitary has a positive normalized Choi gap at every
finite footprint, uniformly over all finite private/register dimensions and
all finite mixed decompositions of the specified Schmidt number. The same
gap works for pure and mixed resources. Budgets zero are also included. -/
theorem exists_unitary_qualitative_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, UnitaryTarget U ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧ PureScoreGap U K e ∧ MixedScoreGap U K e := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨t, _, hU, hgap⟩ := exists_phase_qualitative_gap d hd
  exact ⟨phaseFamily d t, hU, hgap⟩

end NLQCLean
