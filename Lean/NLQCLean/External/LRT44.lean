/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Objects
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The explicit LRT Theorem 44 proposition

Fixed arXiv 2409.14869v2 p.21: the source
misprints and closed-neighborhood convention are documented in
`docs/LRT44_API_AUDIT.md`. This file defines a proposition, not its proof.
-/

section

namespace NLQCLean

/-- The projection onto the last l coordinates of R^n. -/
noncomputable def lastCoordinateProjection {n l : ℕ} (h : l ≤ n) :
    RealEuclidean n → RealEuclidean l :=
  coordinateProjection (fun i => ⟨n - l + i.val, by omega⟩)

/-- The closed epsilon-neighborhood in the source's existential form. -/
def closedEuclideanNeighborhood {n : ℕ} (S : Set (RealEuclidean n)) (ε : ℝ) :
    Set (RealEuclidean n) := {x | ∃ s ∈ S, ‖x - s‖ ≤ ε}

/-- LRT44, restricted to nonempty compact inputs to avoid the source's
empty-set Hausdorff convention. The empty case is a separate derived lemma.
The one kappa is chosen before every dimension, degree, set and tolerance.
Only the published selection conclusions occur here. -/
def LRTTheorem44 : Prop :=
  ∀ c : ℕ, ∃ κ : ℕ, ∀ n l D : ℕ, ∀ hln : l ≤ n, 1 ≤ l →
    ∀ S : Set (RealEuclidean n), IsCompact S → S.Nonempty →
      HasSemialgebraicFormat S c D → ∀ ε : ℝ, 0 < ε →
      ∃ A : Set (RealEuclidean n),
        IsClosed A ∧
        coordinateInteriorDimension A ≤ l ∧
        A ⊆ closedEuclideanNeighborhood S ε ∧
        Metric.hausdorffEDist (lastCoordinateProjection hln '' A)
          (lastCoordinateProjection hln '' S) ≤ ENNReal.ofReal ε ∧
        HasSemialgebraicFormat A κ (κ * D)

end NLQCLean
end
