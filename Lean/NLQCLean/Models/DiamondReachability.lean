import NLQCLean.Models.ProtocolMetrics
import NLQCLean.Models.MixedReachability
import NLQCLean.Models.UniversalReachability

/-!
# Operational diamond reachability on arbitrary finite registers

Reachability is the classical complement of the assertion that every
physical protocol has error strictly above e. Thus it means that some
physical protocol has error at most e, allowing every finite register type
and the actual finite mixed channel. Outer measure needs only inclusion
in the previously proved Borel score-reachable sets.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

/-- A strict normalized diamond lower bound for all pure protocols of footprint at most K.
Every internal finite register type is quantified after the gap. -/
def PureStrictDiamondGap {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB),
    P.HasFootprint K → e < diamondError P.operationalChannel (adConj U)

/-- The same gap for finite mixed decompositions of bounded Schmidt number.
Only the common component rank and both complete message dimensions are charged;
the local support dimension of a mixed resource is unrestricted. -/
def MixedStrictDiamondGap {d : ℕ}
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
      e < diamondError (m.mixedChannel VA VB DA DB) (adConj U)


/-- A pure implementation exists at error at most e; classical existential encoding. -/
def pureDiamondReachable (d K : ℕ) (e : ℝ) : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ¬ PureStrictDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e}

/-- A finite mixed implementation exists at error at most e, with common local maps. -/
def mixedDiamondReachable (d K : ℕ) (e : ℝ) : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ¬ MixedStrictDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e}

section OriginalRegisters

variable {d K n : ℕ} {e : ℝ}
variable {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
variable {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Direct membership for every original pure protocol, without register compression. -/
theorem PureProtocol.mem_pureDiamondReachable
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hK : P.HasFootprint K)
    (he : diamondError P.operationalChannel (adConj (U : Matrix _ _ ℂ)) ≤ e) :
    U ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  intro h
  exact (not_lt_of_ge he) (h ρA ρB κA κB μA μB εA εB P hK)

/-- Direct membership for the actual mixed channel and common-map implementation. -/
theorem MixedResource.mem_mixedDiamondReachable (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ} {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix (Fin d × εA) (κA × μB) ℂ} {DB : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R : ℕ} (hR : m.schmidtNumberLE R) (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : diamondError (m.mixedChannel VA VB DA DB) (adConj (U : Matrix _ _ ℂ)) ≤ e) :
    U ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  intro h
  exact (not_lt_of_ge he) (h ρA ρB κA κB μA μB εA εB n m VA VB DA DB hVA hVB hDA hDB R hR hK)

end OriginalRegisters

/-- Every physical pure diamond implementation lies in score reachability. -/
theorem pureDiamondReachable_subset_pureReachable {d : ℕ} [NeZero d] (K : ℕ) (e : ℝ) :
    pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ⊆ pureReachable d K e := by
  intro U hU
  by_contra hn
  apply hU
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  by_contra he
  have hs := P.scoreU_ge_of_diamondError_le (Matrix.mem_unitaryGroup_iff'.mp U.2) (le_of_not_gt he)
  exact hn (P.mem_pureReachable hP hs)

/-- Mixed diamond accuracy is converted on the original mixed channel before component selection. -/
theorem mixedDiamondReachable_subset_mixedReachable {d : ℕ} [NeZero d] (K : ℕ) (e : ℝ) :
    mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ⊆ mixedReachable d K e := by
  intro U hU
  by_contra hn
  apply hU
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  by_contra he
  have hs := m.scoreU_ge_of_diamondError_le hVA hVB hDA hDB
    (Matrix.mem_unitaryGroup_iff'.mp U.2) (le_of_not_gt he)
  exact hn (m.mem_mixedReachable VA VB DA DB hVA hVB hDA hDB hR hK hs)

/-- Every target has its own pure implementation on some finite registers. -/
def PureUniversalDiamond (d K : ℕ) (e : ℝ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d × Fin d) ℂ, U ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e

/-- Every target has its own finite mixed implementation on some finite registers. -/
def MixedUniversalDiamond (d K : ℕ) (e : ℝ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d × Fin d) ℂ, U ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e

theorem PureUniversalDiamond.score {d K : ℕ} [NeZero d] {e : ℝ}
    (h : PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) :
    PureUniversalScore d K e := fun U => pureDiamondReachable_subset_pureReachable K e (h U)

theorem MixedUniversalDiamond.score {d K : ℕ} [NeZero d] {e : ℝ}
    (h : MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) :
    MixedUniversalScore d K e := fun U => mixedDiamondReachable_subset_mixedReachable K e (h U)

end NLQCLean
