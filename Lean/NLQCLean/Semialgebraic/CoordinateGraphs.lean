/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Dimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# coordinate graph charts

Charts are constructed from the inverse function theorem
for the chosen coordinate projection of a C1 parametrization. Their domains,
maps, projection identities and image identities are ordinary concrete data.
No slope or multiplicity estimate is part of the chart definition.
-/

section

open Set Filter
open scoped Topology

namespace NLQCLean

structure CoordinateGraphChart {n d : ℕ} (φ : RealEuclidean d → RealEuclidean n)
    (I : Fin d → Fin n) where
  parameterDomain : Set (RealEuclidean d)
  baseDomain : Set (RealEuclidean d)
  graph : RealEuclidean d → RealEuclidean n
  open_parameterDomain : IsOpen parameterDomain
  open_baseDomain : IsOpen baseDomain
  parameter_subset : parameterDomain ⊆ openUnitCube d
  smooth : ContDiffOn ℝ 1 graph baseDomain
  projection_graph : ∀ y ∈ baseDomain, coordinateProjection I (graph y) = y
  mapsTo_base : MapsTo (coordinateProjection I ∘ φ) parameterDomain baseDomain
  graph_on_parameter : ∀ x ∈ parameterDomain, graph (coordinateProjection I (φ x)) = φ x
  image_eq : graph '' baseDomain = φ '' parameterDomain

theorem exists_coordinateGraphChart {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) (I : Fin d → Fin n)
    {x : RealEuclidean d} (hx : x ∈ openUnitCube d)
    (hfull : Function.Bijective ((coordinateProjectionL I).comp (fderiv ℝ φ x))) :
    ∃ P : CoordinateGraphChart φ I, x ∈ P.parameterDomain := by
  let F := coordinateProjection I ∘ φ
  have hφAt := (hφ x hx).contDiffAt ((isOpen_openUnitCube d).mem_nhds hx)
  have hFAt : ContDiffAt ℝ 1 F x :=
    (contDiff_coordinateProjection I).contDiffAt.comp x hφAt
  let e := (LinearEquiv.ofBijective
    ((coordinateProjectionL I).comp (fderiv ℝ φ x)).toLinearMap hfull).toContinuousLinearEquiv
  have hFd : HasFDerivAt F (e : RealEuclidean d →L[ℝ] RealEuclidean d) x :=
    (coordinateProjectionL I).hasFDerivAt.comp x hφAt.differentiableAt_one.hasFDerivAt
  let E := hFAt.toOpenPartialHomeomorph F hFd one_ne_zero
  have hE : (E : RealEuclidean d → RealEuclidean d) = F :=
    hFAt.toOpenPartialHomeomorph_coe hFd one_ne_zero
  have hxS : x ∈ E.source := hFAt.mem_toOpenPartialHomeomorph_source hFd one_ne_zero
  have hxT : F x ∈ E.target := E.map_source hxS
  have hleft : E.symm (F x) = x := E.left_inv hxS
  have hInv : ContDiffAt ℝ 1 E.symm (F x) := by
    apply E.contDiffAt_symm hxT (f₀' := e)
    · simpa only [hleft, hE] using hFd
    · simpa only [hleft, hE] using hFAt
  have hG : ContDiffAt ℝ 1 (φ ∘ E.symm) (F x) :=
    (show ContDiffAt ℝ 1 φ (E.symm (F x)) by simpa only [hleft] using hφAt).comp _ hInv
  obtain ⟨u, hu, hgu⟩ := hG.contDiffOn le_rfl (by simp)
  have hpre : E.symm ⁻¹' openUnitCube d ∈ 𝓝 (F x) :=
    hInv.continuousAt.preimage_mem_nhds (by simpa only [hleft] using
      ((isOpen_openUnitCube d).mem_nhds hx))
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp
    (inter_mem hu (inter_mem (E.open_target.mem_nhds hxT) hpre))
  have hWT : W ⊆ E.target := fun y hy => (hW hy).2.1
  let V := E.symm '' W
  have hV : V ⊆ openUnitCube d := by
    rintro z ⟨y, hy, rfl⟩
    exact (hW hy).2.2
  refine ⟨{
    parameterDomain := V
    baseDomain := W
    graph := φ ∘ E.symm
    open_parameterDomain := E.isOpen_image_symm_of_subset_target hWo hWT
    open_baseDomain := hWo
    parameter_subset := hV
    smooth := hgu.mono (fun y hy => (hW hy).1)
    projection_graph := ?_
    mapsTo_base := ?_
    graph_on_parameter := ?_
    image_eq := ?_ }, ?_⟩
  · intro y hy
    exact E.right_inv (hWT hy)
  · rintro z ⟨y, hy, rfl⟩
    change E (E.symm y) ∈ W
    rw [E.right_inv (hWT hy)]
    exact hy
  · rintro z ⟨y, hy, rfl⟩
    change φ (E.symm (E (E.symm y))) = φ (E.symm y)
    rw [E.right_inv (hWT hy)]
  · exact (image_image φ E.symm W).symm
  · exact ⟨F x, hxW, hleft⟩

theorem CoordinateGraphChart.graph_injOn {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n} {I : Fin d → Fin n}
    (P : CoordinateGraphChart φ I) : InjOn P.graph P.baseDomain := by
  intro y hy z hz heq
  simpa only [P.projection_graph y hy, P.projection_graph z hz] using
    congrArg (coordinateProjection I) heq

theorem CoordinateGraphChart.projection_injOn {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n} {I : Fin d → Fin n}
    (P : CoordinateGraphChart φ I) : InjOn (coordinateProjection I) (φ '' P.parameterDomain) := by
  rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩ heq
  simpa only [P.graph_on_parameter x hx, P.graph_on_parameter w hw] using congrArg P.graph heq

theorem CoordinateGraphChart.measurableSet_image {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n} {I : Fin d → Fin n}
    (P : CoordinateGraphChart φ I) : MeasurableSet (φ '' P.parameterDomain) := by
  rw [← P.image_eq]
  exact P.open_baseDomain.measurableSet.image_of_continuousOn_injOn
    P.smooth.continuousOn P.graph_injOn

noncomputable def CoordinateGraphChart.empty {n d : ℕ}
    (φ : RealEuclidean d → RealEuclidean n) (I : Fin d → Fin n) :
    CoordinateGraphChart φ I where
  parameterDomain := ∅
  baseDomain := ∅
  graph := fun _ => 0
  open_parameterDomain := isOpen_empty
  open_baseDomain := isOpen_empty
  parameter_subset := empty_subset _
  smooth := contDiffOn_empty
  projection_graph := fun _ h => False.elim h
  mapsTo_base := fun _ h => False.elim h
  graph_on_parameter := fun _ h => False.elim h
  image_eq := by simp

theorem exists_coordinateGraphChart_cover {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) (I : Fin d → Fin n)
    {B : Set (RealEuclidean d)} (hB : B ⊆ openUnitCube d)
    (hfull : ∀ x ∈ B,
      Function.Bijective ((coordinateProjectionL I).comp (fderiv ℝ φ x))) :
    ∃ P : ℕ → CoordinateGraphChart φ I, B ⊆ ⋃ j, (P j).parameterDomain := by
  classical
  by_cases hne : B.Nonempty
  · have : Nonempty B := hne.to_subtype
    have hex (x : B) := exists_coordinateGraphChart hφ I (hB x.property) (hfull x x.property)
    choose P hP using hex
    obtain ⟨e, he⟩ := (IsLindelof.of_coe (s := B)).indexed_countable_subcover
      (fun x : B => (P x).parameterDomain) (fun x => (P x).open_parameterDomain)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hP ⟨x, hx⟩⟩)
    exact ⟨fun j => P (e j), he⟩
  · exact ⟨fun _ => CoordinateGraphChart.empty φ I,
      (Set.not_nonempty_iff_eq_empty.mp hne) ▸ empty_subset _⟩

theorem CoordinateGraphChart.projection_fderiv_graph {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n} {I : Fin d → Fin n}
    (P : CoordinateGraphChart φ I) {y : RealEuclidean d} (hy : y ∈ P.baseDomain) :
    (coordinateProjectionL I).comp (fderiv ℝ P.graph y) =
      ContinuousLinearMap.id ℝ (RealEuclidean d) := by
  have hdiff := (P.smooth y hy).contDiffAt (P.open_baseDomain.mem_nhds hy)
  have heq : (coordinateProjection I ∘ P.graph) =ᶠ[𝓝 y] id := by
    filter_upwards [P.open_baseDomain.mem_nhds hy] with z hz
    exact P.projection_graph z hz
  have hder := (coordinateProjectionL I).hasFDerivAt.comp y
    hdiff.differentiableAt_one.hasFDerivAt
  have hfd := heq.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ ((coordinateProjectionL I) ∘ P.graph) y = fderiv ℝ id y at hfd
  rw [hder.fderiv, fderiv_id] at hfd
  exact hfd

/-- A countable family of C1 graphs, restricted to measurable
domains, whose images form a disjoint cover of the assigned source locus.
Different base domains may overlap; their multiplicities are handled in
`NLQCLean.Geometry.GraphFiberMultiplicity`. -/
structure CoordinateGraphPartition {n d : ℕ}
    (φ : RealEuclidean d → RealEuclidean n) (I : Fin d → Fin n)
    (B : Set (RealEuclidean d)) where
  chart : ℕ → CoordinateGraphChart φ I
  domain : ℕ → Set (RealEuclidean d)
  measurable_domain : ∀ j, MeasurableSet (domain j)
  domain_subset : ∀ j, domain j ⊆ (chart j).baseDomain
  disjoint : Pairwise (fun j k => Disjoint ((chart j).graph '' domain j)
    ((chart k).graph '' domain k))
  covers : (⋃ j, (chart j).graph '' domain j) = φ '' B

theorem exists_coordinateGraphPartition {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d))
    (hinj : InjOn φ (openUnitCube d)) (I : Fin d → Fin n)
    {B : Set (RealEuclidean d)} (hBm : MeasurableSet B) (hB : B ⊆ openUnitCube d)
    (hfull : ∀ x ∈ B,
      Function.Bijective ((coordinateProjectionL I).comp (fderiv ℝ φ x))) :
    Nonempty (CoordinateGraphPartition φ I B) := by
  classical
  obtain ⟨P, hP⟩ := exists_coordinateGraphChart_cover hφ I hB hfull
  let S : ℕ → Set (RealEuclidean n) := fun j => φ '' (B ∩ (P j).parameterDomain)
  have hSm (j : ℕ) : MeasurableSet (S j) :=
    (hBm.inter (P j).open_parameterDomain.measurableSet).image_of_continuousOn_injOn
      (hφ.continuousOn.mono (inter_subset_left.trans hB))
      (hinj.mono (inter_subset_left.trans hB))
  have hScov : (⋃ j, S j) = φ '' B := by
    ext z
    simp only [mem_iUnion, S, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨j, x, ⟨hx, _⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hP hx)
      exact ⟨j, x, ⟨hx, hj⟩, rfl⟩
  let T := disjointed S
  have hTm (j : ℕ) : MeasurableSet (T j) := MeasurableSet.disjointed hSm j
  have hTsub (j : ℕ) : T j ⊆ φ '' (P j).parameterDomain :=
    (disjointed_le S j).trans (image_mono inter_subset_right)
  let D : ℕ → Set (RealEuclidean d) := fun j => coordinateProjection I '' T j
  have hDm (j : ℕ) : MeasurableSet (D j) :=
    (hTm j).image_of_continuousOn_injOn (continuous_coordinateProjection I).continuousOn
      ((P j).projection_injOn.mono (hTsub j))
  have hDsub (j : ℕ) : D j ⊆ (P j).baseDomain := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hTsub j hz
    exact (P j).mapsTo_base hx
  have hDeq (j : ℕ) : (P j).graph '' D j = T j := by
    ext z
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hTsub j hw
      simpa only [(P j).graph_on_parameter x hx] using hw
    · intro hz
      refine ⟨coordinateProjection I z, ⟨z, hz, rfl⟩, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hTsub j hz
      exact (P j).graph_on_parameter x hx
  refine ⟨⟨P, D, hDm, hDsub, ?_, ?_⟩⟩
  · simpa only [hDeq] using (disjoint_disjointed S)
  · simp only [hDeq]
    exact (iSup_disjointed S).trans hScov

noncomputable def coordinateDerivativeDet {n d : ℕ}
    (φ : RealEuclidean d → RealEuclidean n) (I : Fin d → Fin n)
    (x : RealEuclidean d) : ℝ :=
  ((coordinateProjectionL I).comp (fderiv ℝ φ x)).det

theorem coordinateDerivativeDet_ne_zero_iff {n d : ℕ}
    (φ : RealEuclidean d → RealEuclidean n) (I : Fin d → Fin n)
    (x : RealEuclidean d) : coordinateDerivativeDet φ I x ≠ 0 ↔
      Function.Bijective ((coordinateProjectionL I).comp (fderiv ℝ φ x)) := by
  change ¬ (((coordinateProjectionL I).comp (fderiv ℝ φ x)).toLinearMap.det = 0) ↔ _
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact ⟨fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩, fun h => h.1⟩

theorem continuousOn_coordinateDerivativeDet {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) (I : Fin d → Fin n) :
    ContinuousOn (coordinateDerivativeDet φ I) (openUnitCube d) :=
  ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuousOn_const.clm_comp
      (hφ.continuousOn_fderiv_of_isOpen (isOpen_openUnitCube d) le_rfl))

def coordinateFullRankLocus {n d : ℕ}
    (φ : RealEuclidean d → RealEuclidean n) (I : Fin d → Fin n) :
    Set (RealEuclidean d) := {x | x ∈ openUnitCube d ∧ coordinateDerivativeDet φ I x ≠ 0}

theorem isOpen_coordinateFullRankLocus {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) (I : Fin d → Fin n) :
    IsOpen (coordinateFullRankLocus φ I) := by
  exact (continuousOn_coordinateDerivativeDet hφ I).isOpen_inter_preimage
    (isOpen_openUnitCube d) (isClosed_singleton (x := (0 : ℝ))).isOpen_compl

/-- Raw tangent-minor comparisons are Borel on the parameter cube. A common
change of tangent frame multiplies all these determinants by the same factor;
the quantitative comparison is proved separately in the area-formula argument. -/
theorem measurableSet_coordinateDerivativeDet_compare {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) (I J : Fin d → Fin n) :
    MeasurableSet {x | x ∈ openUnitCube d ∧
      |coordinateDerivativeDet φ I x| ≤ |coordinateDerivativeDet φ J x|} := by
  have hI := (continuousOn_coordinateDerivativeDet hφ I).domRestrict.abs.measurable
  have hJ := (continuousOn_coordinateDerivativeDet hφ J).domRestrict.abs.measurable
  have h := (isOpen_openUnitCube d).measurableSet.subtype_image (measurableSet_le hI hJ)
  convert h using 1
  ext x
  simp [and_comm]

theorem mem_iUnion_coordinateFullRankLocus {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n} {x : RealEuclidean d}
    (hx : x ∈ openUnitCube d) (hinj : Function.Injective (fderiv ℝ φ x)) :
    ∃ I : Fin d → Fin n, Function.Injective I ∧ x ∈ coordinateFullRankLocus φ I := by
  obtain ⟨I, hI, hfull⟩ := exists_bijective_coordinateProjection_comp (fderiv ℝ φ x) hinj
  exact ⟨I, hI, hx, (coordinateDerivativeDet_ne_zero_iff φ I x).mpr hfull⟩

theorem exists_coordinateFullRankPartition {n d : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d))
    (hinj : InjOn φ (openUnitCube d)) (I : Fin d → Fin n) :
    Nonempty (CoordinateGraphPartition φ I (coordinateFullRankLocus φ I)) :=
  exists_coordinateGraphPartition hφ hinj I
    (isOpen_coordinateFullRankLocus hφ I).measurableSet (fun _ hx => hx.1)
    (fun x hx => (coordinateDerivativeDet_ne_zero_iff φ I x).mp hx.2)

/-- Every point of an audited embedded cube belongs to a coordinate-full-rank
locus. Each locus has the proved disjoint measurable graph partition. The area-formula argument assigns the coordinate choice by
maximizing minors before restriction. -/
theorem SemialgebraicSmoothCube.exists_coordinateGraphPartitions {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) :
    ∃ φ : RealEuclidean d → RealEuclidean n,
      φ '' openUnitCube d = C ∧ ContDiffOn ℝ 1 φ (openUnitCube d) ∧
      InjOn φ (openUnitCube d) ∧
      (∀ I : Fin d → Fin n, Nonempty (CoordinateGraphPartition φ I (coordinateFullRankLocus φ I))) ∧
      (⋃ I : Fin d → Fin n, φ '' coordinateFullRankLocus φ I) = C := by
  obtain ⟨_, _, _, φ, hφimage, _, hφ, hder, hemb⟩ := hC
  have hinj : InjOn φ (openUnitCube d) := injOn_iff_injective.mpr hemb.injective
  refine ⟨φ, hφimage, hφ, hinj, fun I => exists_coordinateFullRankPartition hφ hinj I, ?_⟩
  rw [← hφimage, ← image_iUnion]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨I, hI⟩ := mem_iUnion.mp hx
    exact hI.1
  · intro hx
    obtain ⟨I, _, hI⟩ := mem_iUnion_coordinateFullRankLocus hx (hder x hx)
    exact mem_iUnion.mpr ⟨I, hI⟩

end NLQCLean
end
