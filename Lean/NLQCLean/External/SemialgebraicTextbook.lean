/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Objects

/-!
# Enumerated external semialgebraic textbook propositions

Sources and side conditions are listed per clause below and
audited in `docs/LRT44_API_AUDIT.md`. No proposition is assumed globally.
The projection proposition is proved (`semialgebraicProjectionTheorem`).
Application-specific chart estimates, fiber counts and nullity are absent.
-/

section

namespace NLQCLean

/-- Coste Theorem 2.3, printed p.26 / PDF p.27. Projection onto the
first n coordinates preserves existence of a finite polynomial description. -/
def SemialgebraicProjectionTheorem : Prop :=
  ∀ n : ℕ, ∀ A : Set (RealEuclidean (n + 1)), Semialgebraic A →
    Semialgebraic (coordinateProjection (Fin.castAdd 1) '' A)

/-- Coste Proposition 3.15, printed pp.55--56 / PDF pp.56--57.
The coordinate/chart dictionary is proved by
`semialgebraicDimensionStrataTheorem` in `NLQCLean.Semialgebraic.Dimension`;
this proposition is not an external premise of the final bounds. -/
def SemialgebraicDimensionStrataTheorem : Prop :=
  ∀ n : ℕ, ∀ S : Set (RealEuclidean n), Semialgebraic S → S.Nonempty →
    ∀ P : SmoothCubeDecomposition S,
      coordinateInteriorDimension S = Finset.univ.sup P.dimension

/-- Coste Theorem 3.18, printed pp.56--57 / PDF pp.57--58.
No continuity is required, and injectivity need only hold on the domain. -/
def SemialgebraicDimensionImageTheorem : Prop :=
  ∀ n k : ℕ, ∀ A : Set (RealEuclidean n), Semialgebraic A → A.Nonempty →
    ∀ f : RealEuclidean n → RealEuclidean k, SemialgebraicMapOn A f →
      coordinateInteriorDimension (f '' A) ≤ coordinateInteriorDimension A ∧
      (Set.InjOn f A → coordinateInteriorDimension (f '' A) = coordinateInteriorDimension A)

/-- The fiber in A. -/
def semialgebraicMapFiber {n k : ℕ} (A : Set (RealEuclidean n))
    (f : RealEuclidean n → RealEuclidean k) (y : RealEuclidean k) :
    Set (RealEuclidean n) := {x | x ∈ A ∧ f x = y}

/-- Empty fibers are excluded, including when r=0. -/
def nonemptyFiberDimensionLocus {n k : ℕ} (A : Set (RealEuclidean n))
    (f : RealEuclidean n → RealEuclidean k) (r : ℕ) : Set (RealEuclidean k) :=
  {y | (semialgebraicMapFiber A f y).Nonempty ∧
    coordinateInteriorDimension (semialgebraicMapFiber A f y) = r}

/-- Coste Corollary 4.2 and preceding calculation, printed p.62 /
PDF p.63. Continuity is on A; the additive inequality is asserted only for
nonempty loci, avoiding natural truncated subtraction and empty dimensions. -/
def SemialgebraicDimensionFiberTheorem : Prop :=
  ∀ n k : ℕ, ∀ A : Set (RealEuclidean n), Semialgebraic A →
    ∀ f : RealEuclidean n → RealEuclidean k, ContinuousOn f A → SemialgebraicMapOn A f →
      ∀ r : ℕ, Semialgebraic (nonemptyFiberDimensionLocus A f r) ∧
        ((nonemptyFiberDimensionLocus A f r).Nonempty →
          coordinateInteriorDimension (nonemptyFiberDimensionLocus A f r) + r ≤
            coordinateInteriorDimension A)

/-- The conjunction of the three dimension statements. -/
def SemialgebraicDimensionTheorems : Prop :=
  SemialgebraicDimensionStrataTheorem ∧ SemialgebraicDimensionImageTheorem ∧
    SemialgebraicDimensionFiberTheorem

end NLQCLean
end
