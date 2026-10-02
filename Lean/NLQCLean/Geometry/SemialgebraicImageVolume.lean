/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.SmoothCubeFamilyVolume

/-!
# The coordinate-graph image-volume inequality

All top-dimensional cubes share the same fiber bound, while
lower-dimensional images have measure zero. The resulting constant is 4^a.
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

theorem SmoothCubeDecomposition.volume_image_le_coordinateFibers {a m : ℕ}
    {C : Set (RealEuclidean a)} (P : SmoothCubeDecomposition C)
    (hd : ∀ i, P.dimension i ≤ m) {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ I : Fin m → Fin a, Function.Injective I →
      ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
        Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M)
    (p : RealEuclidean a → RealEuclidean m) {U : Set (RealEuclidean a)}
    (hU : IsOpen U) (hCU : C ⊆ U) (hp : ContDiffOn ℝ 1 p U)
    {b : ℝ} (hb : 0 ≤ b) (hJ : ∀ x ∈ C, topRealJacobian (fderiv ℝ p x) ≤ b) :
    volume (p '' C) ≤ (2 : ℝ≥0∞) ^ a *
      (ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
        volume (closedBall (0 : RealEuclidean m) R)) := by
  classical
  let Top := {i : Fin P.count // P.dimension i = m}
  let S : Top → Set (RealEuclidean a) := fun i => P.piece i.val
  have hS (i : Top) : SemialgebraicSmoothCube (S i) m := by
    simpa only [S, i.prop] using P.smoothCube i.val
  have hdis : Pairwise (fun i j : Top => Disjoint (S i) (S j)) :=
    fun _ _ hij => P.disjoint (fun h => hij (Subtype.ext h))
  have htop := volume_iUnion_smoothCubes_le S hS hdis C
    (fun i => P.piece_subset i.val) hR M hfib p hU hCU hp hb hJ
  let Z : Set (RealEuclidean m) :=
    ⋃ i : Fin P.count, if P.dimension i < m then p '' P.piece i else ∅
  have hZ : volume Z = 0 := by
    apply measure_iUnion_null
    intro i
    split_ifs with hi
    · exact (P.smoothCube i).volume_image_eq_zero (hp.mono ((P.piece_subset i).trans hCU)) hi
    · exact measure_empty
  have hcover : p '' C ⊆ (p '' (⋃ i : Top, S i)) ∪ Z := by
    rintro y ⟨x, hx, rfl⟩
    rw [← P.covers] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hdimeq : P.dimension i = m
    · exact Or.inl ⟨x, mem_iUnion.mpr ⟨⟨i, hdimeq⟩, hi⟩, rfl⟩
    · apply Or.inr
      refine mem_iUnion.mpr ⟨i, ?_⟩
      rw [ite_eq_left (lt_of_le_of_ne (hd i) hdimeq)]
      exact ⟨x, hi, rfl⟩
  calc
    _ ≤ volume ((p '' (⋃ i : Top, S i)) ∪ Z) := measure_mono hcover
    _ ≤ volume (p '' (⋃ i : Top, S i)) + volume Z := measure_union_le _ _
    _ = volume (p '' (⋃ i : Top, S i)) := by rw [hZ, add_zero]
    _ ≤ _ := htop

theorem euclidean_closedBall_volume (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall (0 : RealEuclidean m) R) =
      ENNReal.ofReal (R ^ m) * euclideanUnitBallVolume m := by
  simpa only [finrank_euclideanSpace_fin, euclideanUnitBallVolume] using
    volume.addHaar_closedBall (0 : RealEuclidean m) hR

theorem coordinate_graph_volume_constant_eq (a m M : ℕ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) :
    (2 : ℝ≥0∞) ^ a * (ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
      volume (closedBall (0 : RealEuclidean m) R)) =
    ENNReal.ofReal ((4 : ℝ) ^ a) * (M : ℝ≥0∞) * euclideanUnitBallVolume m *
      ENNReal.ofReal (R ^ m) * ENNReal.ofReal b := by
  have hfour : ENNReal.ofReal ((4 : ℝ) ^ a) = (2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ a := by
    rw [← mul_pow, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hfour, ENNReal.ofReal_mul hb, ENNReal.ofReal_pow (by norm_num), euclidean_closedBall_volume m hR]
  norm_num only [ENNReal.ofReal_ofNat]
  ac_rfl

end NLQCLean
end
