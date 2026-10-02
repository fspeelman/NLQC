/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.CoordinateMaps

/-!
# Coordinate projections are contractions

Coordinate projections of Euclidean space do not increase norms or distances,
and a closed set inside a closed neighborhood of a compact set is compact.
-/

section

open Set Metric

namespace NLQCLean

/-- The closed epsilon-neighborhood in existential form. -/
def closedEuclideanNeighborhood {n : ℕ} (S : Set (RealEuclidean n)) (ε : ℝ) :
    Set (RealEuclidean n) := {x | ∃ s ∈ S, ‖x - s‖ ≤ ε}

theorem norm_coordinateProjection_le {n k : ℕ} (I : Fin k → Fin n)
    (hI : Function.Injective I) (x : RealEuclidean n) : ‖coordinateProjection I x‖ ≤ ‖x‖ := by
  classical
  have hsum : ∑ j : Fin k, (x (I j)) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.image I, (x i) ^ 2 := (Finset.sum_image hI.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have hx := EuclideanSpace.real_norm_sq_eq x
  have hproj := EuclideanSpace.real_norm_sq_eq (coordinateProjection I x)
  simp only [coordinateProjection_apply] at hproj
  nlinarith [norm_nonneg x, norm_nonneg (coordinateProjection I x)]

theorem dist_coordinateProjection_le {n k : ℕ} (I : Fin k → Fin n)
    (hI : Function.Injective I) (x y : RealEuclidean n) :
    dist (coordinateProjection I x) (coordinateProjection I y) ≤ dist x y := by
  have h := norm_coordinateProjection_le I hI (x - y)
  have heq : coordinateProjection I (x - y) = coordinateProjection I x - coordinateProjection I y := by
    ext j
    rfl
  simpa only [heq, dist_eq_norm] using h

theorem isCompact_of_subset_closedEuclideanNeighborhood {n : ℕ}
    {S A : Set (RealEuclidean n)} {ε : ℝ} (hS : IsCompact S) (hA : IsClosed A)
    (hAS : A ⊆ closedEuclideanNeighborhood S ε) : IsCompact A := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  apply (isCompact_closedBall (0 : RealEuclidean n) (R + ε)).of_isClosed_subset hA
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hAS hx
  simp only [mem_closedBall, dist_zero_right]
  calc
    ‖x‖ ≤ ‖x - s‖ + ‖s‖ := norm_le_norm_sub_add x s
    _ ≤ ε + R := add_le_add hxs (hR s hs)
    _ = R + ε := add_comm _ _

end NLQCLean

end
