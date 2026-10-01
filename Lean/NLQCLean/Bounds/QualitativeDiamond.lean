import NLQCLean.Bounds.QualitativeDivergence
import NLQCLean.Models.ProtocolMetrics

/-!
# Unconditional qualitative divergence in normalized diamond error

The same target and positive budget-dependent gap work
for all pure and finite mixed protocols on arbitrary finite registers.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

/-- A uniform normalized diamond gap for all pure protocols of footprint at most K.
Every internal finite register type is quantified after the gap. -/
def PureDiamondGap {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB),
    P.HasFootprint K → e ≤ diamondError P.operationalChannel (adConj U)

/-- The same gap for finite mixed decompositions of bounded Schmidt number.
Only the common component rank and both complete message dimensions are charged;
the local support dimension of a mixed resource is unrestricted. -/
def MixedDiamondGap {d : ℕ}
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
      e ≤ diamondError (m.mixedChannel VA VB DA DB) (adConj U)

theorem PureScoreGap.diamond {d K : ℕ} [NeZero d] {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : UnitaryTarget U)
    (h : PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e) :
    PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  have hs := h ρA ρB κA κB μA μB εA εB P hP
  have hm := P.one_sub_scoreU_le_diamondError hU.1
  linarith

theorem MixedScoreGap.diamond {d K : ℕ} [NeZero d] {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : UnitaryTarget U)
    (h : MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e) :
    MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  have hs := h ρA ρB κA κB μA μB εA εB n m VA VB DA DB hVA hVB hDA hDB R hR hK
  have hm := m.one_sub_scoreU_le_diamondError hVA hVB hDA hDB hU.1
  linarith

/-- Qualitative diamond divergence: one fixed unitary before all budgets and all finite architectures. -/
theorem exists_unitary_qualitative_diamond_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, UnitaryTarget U ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧ PureDiamondGap U K e ∧ MixedDiamondGap U K e := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨U, hU, hgap⟩ := exists_unitary_qualitative_gap d hd
  refine ⟨U, hU, fun K => ?_⟩
  obtain ⟨e, he, hp, hm⟩ := hgap K
  exact ⟨e, he, hp.diamond hU, hm.diamond hU⟩

end NLQCLean
