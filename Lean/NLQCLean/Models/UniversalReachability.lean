import NLQCLean.Models.MixedReachability

/-!
# Universal score reachability

Universality predicates for unitary tasks and their elementary relation to
pure and finite-mixed score-reachable sets.
-/

namespace NLQCLean

open Matrix

/-- Every unitary has a budget-K pure protocol, with its own finite architecture. -/
def PureUniversalScore (d K : ℕ) (e : ℝ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
    ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
      P.HasFootprint K ∧ 1 - e ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel

/-- Every unitary has a finite mixed implementation with the charged Schmidt-number footprint. -/
def MixedUniversalScore (d K : ℕ) (e : ℝ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d × Fin d) ℂ, U ∈ mixedReachable d K e

theorem mixedUniversalScore_iff_pure (d K : ℕ) (e : ℝ) :
    MixedUniversalScore d K e ↔ PureUniversalScore d K e := by
  unfold MixedUniversalScore
  rw [mixedReachable_eq_pureReachable]
  rfl

theorem PureUniversalScore.reachable_eq_univ {d K : ℕ} {e : ℝ} (h : PureUniversalScore d K e) :
    pureReachable d K e = Set.univ := Set.eq_univ_of_forall h

end NLQCLean
