import NLQCLean.Models.PVMTVReachability

/-!
# Universal PVM reachability

Universality predicates for ordered rank-one PVM score and joint-TV tasks,
with their elementary pure/mixed and metric-to-score bridges.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

/-- Every ordered rank-one PVM basis lift has a budget-K pure protocol with score at least 1−e. -/
def PurePVMUniversalScore (d K : ℕ) (e : ℝ) : Prop :=
  ∀ M : Matrix.unitaryGroup (Fin d × Fin d) ℂ, M ∈ purePVMReachable d K e

/-- Every basis lift has a finite mixed implementation with score at least 1−e. -/
def MixedPVMUniversalScore (d K : ℕ) (e : ℝ) : Prop :=
  ∀ M : Matrix.unitaryGroup (Fin d × Fin d) ℂ, M ∈ mixedPVMReachable d K e

/-- Every basis lift has an arbitrary-register pure protocol with worst-case joint TV at most e. -/
def PurePVMUniversalTV (d K : ℕ) (e : ℝ) : Prop :=
  ∀ M : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
    M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e

/-- Every basis lift has a finite mixed resource with worst-case joint TV at most e. -/
def MixedPVMUniversalTV (d K : ℕ) (e : ℝ) : Prop :=
  ∀ M : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
    M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e

theorem mixedPVMUniversalScore_iff_pure (d K : ℕ) (e : ℝ) :
    MixedPVMUniversalScore d K e ↔ PurePVMUniversalScore d K e := by
  unfold MixedPVMUniversalScore PurePVMUniversalScore
  rw [mixedPVMReachable_eq_purePVMReachable]

theorem PurePVMUniversalScore.reachable_eq_univ {d K : ℕ} {e : ℝ}
    (h : PurePVMUniversalScore d K e) : purePVMReachable d K e = Set.univ :=
  Set.eq_univ_of_forall h

theorem PurePVMUniversalTV.score {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (h : PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) :
    PurePVMUniversalScore d K e := by
  have : NeZero d := ⟨hd.ne'⟩
  exact fun M => purePVMTVReachable_subset_purePVMReachable K e (h M)

theorem MixedPVMUniversalTV.score {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (h : MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) :
    MixedPVMUniversalScore d K e := by
  have : NeZero d := ⟨hd.ne'⟩
  exact fun M => mixedPVMTVReachable_subset_mixedPVMReachable K e (h M)

end NLQCLean
