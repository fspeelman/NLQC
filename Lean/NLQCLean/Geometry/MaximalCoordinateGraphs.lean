/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.CoordinateGraphSlope

/-!
# Disjoint maximal-minor coordinate graphs

Resolve maximal-minor ties by a finite ordering, then apply the proved
coordinate-graph construction to these measurable assignments.
-/

section

open Set Filter
open scoped Topology

namespace NLQCLean

theorem exists_disjoint_measurable_refinement {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i)) :
    ∃ D : ι → Set α, (∀ i, MeasurableSet (D i)) ∧ (∀ i, D i ⊆ S i) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ (⋃ i, D i) = ⋃ i, S i := by
  classical
  let e := Fintype.equivFin ι
  let T := fun j => S (e.symm j)
  refine ⟨fun i => disjointed T (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    change MeasurableSet (disjointed T (e i))
    rw [disjointed_apply, Finset.sup_eq_iSup]
    exact (hS _).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hS _)
  · intro i
    simpa only [T, Equiv.symm_apply_apply] using disjointed_subset T (e i)
  · intro i j hij
    exact disjoint_disjointed T (e.injective.ne hij)
  · rw [e.surjective.iUnion_comp, iUnion_disjointed]
    exact e.symm.surjective.iUnion_comp S

def maximalCoordinateMinorLocus {a m : ℕ} (φ : RealEuclidean m → RealEuclidean a)
    (s : Set.powersetCard (Fin a) m) : Set (RealEuclidean m) :=
  coordinateFullRankLocus φ (coordinateMinorAxes s) ∩
    ⋂ t : Set.powersetCard (Fin a) m, {x | x ∈ openUnitCube m ∧
      |coordinateDerivativeDet φ (coordinateMinorAxes t) x| ≤
        |coordinateDerivativeDet φ (coordinateMinorAxes s) x|}

theorem measurableSet_maximalCoordinateMinorLocus {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} (hφ : ContDiffOn ℝ 1 φ (openUnitCube m))
    (s : Set.powersetCard (Fin a) m) : MeasurableSet (maximalCoordinateMinorLocus φ s) :=
  (isOpen_coordinateFullRankLocus hφ _).measurableSet.inter
    (MeasurableSet.iInter fun _ => measurableSet_coordinateDerivativeDet_compare hφ _ _)

theorem iUnion_maximalCoordinateMinorLocus {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a}
    (hfull : ∀ x ∈ openUnitCube m, Function.Injective (fderiv ℝ φ x)) :
    (⋃ s : Set.powersetCard (Fin a) m, maximalCoordinateMinorLocus φ s) = openUnitCube m := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact hs.1.1
  · intro hx
    obtain ⟨s, hs, hmax, _⟩ := exists_maximal_coordinateMinor (fderiv ℝ φ x) (hfull x hx)
    refine mem_iUnion.mpr ⟨s, ⟨⟨hx, hs⟩, ?_⟩⟩
    exact mem_iInter.mpr fun t => ⟨hx, hmax t⟩

structure MaximalCoordinateGraphPartitions {a m : ℕ} (φ : RealEuclidean m → RealEuclidean a) where
  assigned : Set.powersetCard (Fin a) m → Set (RealEuclidean m)
  measurable_assigned : ∀ s, MeasurableSet (assigned s)
  assigned_subset : ∀ s, assigned s ⊆ maximalCoordinateMinorLocus φ s
  disjoint : Pairwise (fun s t => Disjoint (assigned s) (assigned t))
  covers : (⋃ s, assigned s) = openUnitCube m
  partition : ∀ s, CoordinateGraphPartition φ (coordinateMinorAxes s) (assigned s)

theorem exists_maximalCoordinateGraphPartitions {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube m)) (hinj : InjOn φ (openUnitCube m))
    (hfull : ∀ x ∈ openUnitCube m, Function.Injective (fderiv ℝ φ x)) :
    Nonempty (MaximalCoordinateGraphPartitions φ) := by
  classical
  obtain ⟨D, hDm, hDsub, hDdis, hDcov⟩ := exists_disjoint_measurable_refinement
    (maximalCoordinateMinorLocus φ) (measurableSet_maximalCoordinateMinorLocus hφ)
  have hP (s : Set.powersetCard (Fin a) m) :
      Nonempty (CoordinateGraphPartition φ (coordinateMinorAxes s) (D s)) := by
    apply exists_coordinateGraphPartition hφ hinj _ (hDm s) (fun x hx => (hDsub s hx).1.1)
    intro x hx
    exact (coordinateDerivativeDet_ne_zero_iff φ _ x).mp (hDsub s hx).1.2
  exact ⟨{
    assigned := D
    measurable_assigned := hDm
    assigned_subset := hDsub
    disjoint := hDdis
    covers := hDcov.trans (iUnion_maximalCoordinateMinorLocus hfull)
    partition := fun s => (hP s).some }⟩

theorem CoordinateGraphPartition.image_subset {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} {I : Fin m → Fin a} {B : Set (RealEuclidean m)}
    (P : CoordinateGraphPartition φ I B) (j : ℕ) :
    (P.chart j).graph '' P.domain j ⊆ φ '' B := by
  rw [← P.covers]
  exact subset_iUnion (fun k => (P.chart k).graph '' P.domain k) j

theorem CoordinateGraphPartition.exists_parameter_of_mem_domain {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} {I : Fin m → Fin a} {B : Set (RealEuclidean m)}
    (P : CoordinateGraphPartition φ I B) (hinj : InjOn φ (openUnitCube m))
    (hB : B ⊆ openUnitCube m) (j : ℕ) {y : RealEuclidean m} (hy : y ∈ P.domain j) :
    ∃ x ∈ B, x ∈ (P.chart j).parameterDomain ∧ coordinateProjection I (φ x) = y ∧
      φ x = (P.chart j).graph y := by
  obtain ⟨x, hx, hxy⟩ := P.image_subset j ⟨y, hy, rfl⟩
  have him : (P.chart j).graph y ∈ φ '' (P.chart j).parameterDomain := by
    rw [← (P.chart j).image_eq]
    exact ⟨y, P.domain_subset j hy, rfl⟩
  obtain ⟨w, hw, hwy⟩ := him
  have hxw : x = w := hinj (hB hx) ((P.chart j).parameter_subset hw) (hxy.trans hwy.symm)
  refine ⟨x, hx, hxw.symm ▸ hw, ?_, hxy⟩
  rw [hxy, (P.chart j).projection_graph y (P.domain_subset j hy)]

namespace MaximalCoordinateGraphPartitions

variable {a m : ℕ} {φ : RealEuclidean m → RealEuclidean a}
  (P : MaximalCoordinateGraphPartitions φ)

theorem assigned_subset_cube (s : Set.powersetCard (Fin a) m) : P.assigned s ⊆ openUnitCube m :=
  fun _ hx => (P.assigned_subset s hx).1.1

theorem graph_mem_image (s : Set.powersetCard (Fin a) m) (j : ℕ) {y : RealEuclidean m}
    (hy : y ∈ (P.partition s).domain j) :
    ((P.partition s).chart j).graph y ∈ φ '' openUnitCube m :=
  image_mono (P.assigned_subset_cube s) ((P.partition s).image_subset j ⟨y, hy, rfl⟩)

theorem sqrt_gram_det_le (hφ : ContDiffOn ℝ 1 φ (openUnitCube m))
    (hinj : InjOn φ (openUnitCube m)) (s : Set.powersetCard (Fin a) m) (j : ℕ)
    {y : RealEuclidean m} (hy : y ∈ (P.partition s).domain j) :
    Real.sqrt (((fderiv ℝ ((P.partition s).chart j).graph y).adjoint).comp
      (fderiv ℝ ((P.partition s).chart j).graph y)).det ≤ (2 : ℝ) ^ a := by
  obtain ⟨x, hx, hxparam, hxy, _⟩ := (P.partition s).exists_parameter_of_mem_domain hinj
    (P.assigned_subset_cube s) j hy
  have hmax := P.assigned_subset s hx
  rw [← hxy]
  exact ((P.partition s).chart j).sqrt_gram_det_le_of_maximal hφ hxparam hmax.1.2
    (fun t => (mem_iInter.mp hmax.2 t).2)

theorem source_disjoint (hinj : InjOn φ (openUnitCube m)) :
    Pairwise (fun u v : Set.powersetCard (Fin a) m × ℕ =>
      Disjoint (((P.partition u.1).chart u.2).graph '' (P.partition u.1).domain u.2)
        (((P.partition v.1).chart v.2).graph '' (P.partition v.1).domain v.2)) := by
  rintro ⟨s, j⟩ ⟨t, k⟩ hne
  by_cases hst : s = t
  · subst t
    exact (P.partition s).disjoint (fun hjk => hne (Prod.ext rfl hjk))
  · have hd : Disjoint (φ '' P.assigned s) (φ '' P.assigned t) := by
      apply Set.disjoint_image_image
      intro x hx z hz heq
      have hxz := hinj (P.assigned_subset_cube s hx) (P.assigned_subset_cube t hz) heq
      exact Set.disjoint_left.mp (P.disjoint hst) hx (hxz.symm ▸ hz)
    exact hd.mono ((P.partition s).image_subset j) ((P.partition t).image_subset k)

theorem source_cover :
    (⋃ s : Set.powersetCard (Fin a) m, ⋃ j : ℕ,
      ((P.partition s).chart j).graph '' (P.partition s).domain j) = φ '' openUnitCube m := by
  simp only [(P.partition _).covers]
  rw [← image_iUnion, P.covers]

end MaximalCoordinateGraphPartitions

theorem SemialgebraicSmoothCube.exists_maximalCoordinateGraphPartitions {a m : ℕ}
    {C : Set (RealEuclidean a)} (hC : SemialgebraicSmoothCube C m) :
    ∃ φ : RealEuclidean m → RealEuclidean a,
      φ '' openUnitCube m = C ∧ ContDiffOn ℝ 1 φ (openUnitCube m) ∧
      InjOn φ (openUnitCube m) ∧ Nonempty (MaximalCoordinateGraphPartitions φ) := by
  obtain ⟨_, _, _, φ, him, _, hφ, hder, hemb⟩ := hC
  have hinj : InjOn φ (openUnitCube m) := injOn_iff_injective.mpr hemb.injective
  exact ⟨φ, him, hφ, hinj, NLQCLean.exists_maximalCoordinateGraphPartitions hφ hinj hder⟩

end NLQCLean
end
