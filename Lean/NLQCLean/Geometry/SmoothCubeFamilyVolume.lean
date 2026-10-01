/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.FiniteFiberImageVolume

/-!
# One volume bound for all top-dimensional smooth cubes

Group all strata and charts by their coordinate projection before
applying the common fiber bound. No number of strata enters the constant.
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

theorem volume_iUnion_smoothCubes_le {a m : ℕ} {ι : Type*} [Countable ι]
    (S : ι → Set (RealEuclidean a)) (hS : ∀ i, SemialgebraicSmoothCube (S i) m)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (C : Set (RealEuclidean a)) (hSC : ∀ i, S i ⊆ C)
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ I : Fin m → Fin a, Function.Injective I →
      ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
        Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M)
    (p : RealEuclidean a → RealEuclidean m) {U : Set (RealEuclidean a)}
    (hU : IsOpen U) (hCU : C ⊆ U) (hp : ContDiffOn ℝ 1 p U)
    {b : ℝ} (hb : 0 ≤ b) (hJ : ∀ x ∈ C, topRealJacobian (fderiv ℝ p x) ≤ b) :
    volume (p '' (⋃ i, S i)) ≤ (2 : ℝ≥0∞) ^ a *
      (ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
        volume (closedBall (0 : RealEuclidean m) R)) := by
  classical
  choose φ him hφ hinj hparts using fun i => (hS i).exists_maximalCoordinateGraphPartitions
  let P (i : ι) : MaximalCoordinateGraphPartitions (φ i) := (hparts i).some
  let D (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) := (P u.1).partition s |>.domain u.2
  let O (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) := ((P u.1).partition s |>.chart u.2).baseDomain
  let g (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) := ((P u.1).partition s |>.chart u.2).graph
  have hpiece (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) : g s u '' D s u ⊆ S u.1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← him u.1]
    exact (P u.1).graph_mem_image s u.2 hy
  have hgraphdis (s : Set.powersetCard (Fin a) m) :
      Pairwise (fun u v : ι × ℕ => Disjoint (g s u '' D s u) (g s v '' D s v)) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    by_cases hik : i = k
    · subst k
      exact ((P i).partition s).disjoint (fun hjl => hne (Prod.ext rfl hjl))
    · exact (hdis hik).mono (hpiece s (i, j)) (hpiece s (k, l))
  have hcover : (⋃ s : Set.powersetCard (Fin a) m, ⋃ u : ι × ℕ, g s u '' D s u) = ⋃ i, S i := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      obtain ⟨u, hu⟩ := mem_iUnion.mp hs
      exact mem_iUnion.mpr ⟨u.1, hpiece s u hu⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hi' : x ∈ φ i '' openUnitCube m := by simpa only [him i] using hi
      rw [← (P i).source_cover] at hi'
      obtain ⟨s, hs⟩ := mem_iUnion.mp hi'
      obtain ⟨j, hj⟩ := mem_iUnion.mp hs
      exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨(i, j), hj⟩⟩
  have himage : p '' (⋃ i, S i) =
      ⋃ s : Set.powersetCard (Fin a) m, ⋃ u : ι × ℕ, (p ∘ g s u) '' D s u := by
    rw [← hcover]
    simp only [image_iUnion, image_image, Function.comp_def]
  have hbound (s : Set.powersetCard (Fin a) m) :
      volume (⋃ u : ι × ℕ, (p ∘ g s u) '' D s u) ≤
        ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
          volume (closedBall (0 : RealEuclidean m) R) := by
    apply volume_iUnion_smoothGraphImages_le (D s) (O s) (g s) C (coordinateMinorAxes s)
      (coordinateMinorAxes_injective s)
      (fun u => ((P u.1).partition s).measurable_domain u.2)
      (fun u => ((P u.1).partition s |>.chart u.2).open_baseDomain)
      (fun u => ((P u.1).partition s).domain_subset u.2)
      (fun u => ((P u.1).partition s |>.chart u.2).smooth)
      (fun u => (hpiece s u).trans (hSC u.1))
      (fun u y hy => ((P u.1).partition s |>.chart u.2).projection_graph y
        (((P u.1).partition s).domain_subset u.2 hy))
      (hgraphdis s) hR M (hfib _ (coordinateMinorAxes_injective s)) p hU hCU hp hb hJ
    exact fun u y hy => (P u.1).sqrt_gram_det_le (hφ u.1) (hinj u.1) s u.2 hy
  rw [himage]
  calc
    _ ≤ ∑' s : Set.powersetCard (Fin a) m, volume (⋃ u : ι × ℕ, (p ∘ g s u) '' D s u) :=
      measure_iUnion_le _
    _ ≤ ∑' _ : Set.powersetCard (Fin a) m,
        ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
          volume (closedBall (0 : RealEuclidean m) R) := ENNReal.tsum_le_tsum hbound
    _ = (Fintype.card (Set.powersetCard (Fin a) m) : ℝ≥0∞) *
        (ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
          volume (closedBall (0 : RealEuclidean m) R)) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      gcongr
      exact_mod_cast card_coordinateMinorIndices_le a m

end NLQCLean
end
