import NLQCLean.Geometry.SmoothCubeFamilyVolume

/-!
# Volume of images of C¹ pieces with measurable domains

The top-dimensional volume bound of `SmoothCubeFamilyVolume` for countably many
pieces `φᵢ '' Wᵢ`, where each `φᵢ` is C¹ and injective with injective derivative
on the open unit cube and each `Wᵢ` is a measurable subset of the cube. No
semialgebraicity of the pieces or charts is required. This is the volume engine
of the direct image-volume route (roadmap step D1).
-/

section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace NLQCLean

/-- Maximal-minor coordinate-graph partitions of `φ` over a measurable part `W`
of the open unit cube. -/
structure MaximalCoordinateGraphPartitionsOn {a m : ℕ}
    (φ : RealEuclidean m → RealEuclidean a) (W : Set (RealEuclidean m)) where
  assigned : Set.powersetCard (Fin a) m → Set (RealEuclidean m)
  measurable_assigned : ∀ s, MeasurableSet (assigned s)
  assigned_subset : ∀ s, assigned s ⊆ maximalCoordinateMinorLocus φ s
  disjoint : Pairwise (fun s t => Disjoint (assigned s) (assigned t))
  covers : (⋃ s, assigned s) = W
  partition : ∀ s, CoordinateGraphPartition φ (coordinateMinorAxes s) (assigned s)

theorem exists_maximalCoordinateGraphPartitionsOn {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube m)) (hinj : InjOn φ (openUnitCube m))
    (hfull : ∀ x ∈ openUnitCube m, Function.Injective (fderiv ℝ φ x))
    {W : Set (RealEuclidean m)} (hWm : MeasurableSet W) (hW : W ⊆ openUnitCube m) :
    Nonempty (MaximalCoordinateGraphPartitionsOn φ W) := by
  classical
  obtain ⟨D, hDm, hDsub, hDdis, hDcov⟩ := exists_disjoint_measurable_refinement
    (maximalCoordinateMinorLocus φ) (measurableSet_maximalCoordinateMinorLocus hφ)
  have hP (s : Set.powersetCard (Fin a) m) :
      Nonempty (CoordinateGraphPartition φ (coordinateMinorAxes s) (D s ∩ W)) := by
    apply exists_coordinateGraphPartition hφ hinj _ ((hDm s).inter hWm)
      (fun x hx => (hDsub s hx.1).1.1)
    intro x hx
    exact (coordinateDerivativeDet_ne_zero_iff φ _ x).mp (hDsub s hx.1).1.2
  refine ⟨{
    assigned := fun s => D s ∩ W
    measurable_assigned := fun s => (hDm s).inter hWm
    assigned_subset := fun s x hx => hDsub s hx.1
    disjoint := fun s t hst => (hDdis hst).mono inter_subset_left inter_subset_left
    covers := ?_
    partition := fun s => (hP s).some }⟩
  rw [← iUnion_inter, hDcov, iUnion_maximalCoordinateMinorLocus hfull]
  exact inter_eq_right.mpr hW

namespace MaximalCoordinateGraphPartitionsOn

variable {a m : ℕ} {φ : RealEuclidean m → RealEuclidean a} {W : Set (RealEuclidean m)}
  (P : MaximalCoordinateGraphPartitionsOn φ W)

theorem assigned_subset_cube (s : Set.powersetCard (Fin a) m) : P.assigned s ⊆ openUnitCube m :=
  fun _ hx => (P.assigned_subset s hx).1.1

theorem assigned_subset_W (s : Set.powersetCard (Fin a) m) : P.assigned s ⊆ W := by
  intro x hx
  have h : x ∈ ⋃ t, P.assigned t := mem_iUnion.mpr ⟨s, hx⟩
  rwa [P.covers] at h

theorem graph_mem_image (s : Set.powersetCard (Fin a) m) (j : ℕ) {y : RealEuclidean m}
    (hy : y ∈ (P.partition s).domain j) :
    ((P.partition s).chart j).graph y ∈ φ '' W :=
  image_mono (P.assigned_subset_W s) ((P.partition s).image_subset j ⟨y, hy, rfl⟩)

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

theorem source_cover :
    (⋃ s : Set.powersetCard (Fin a) m, ⋃ j : ℕ,
      ((P.partition s).chart j).graph '' (P.partition s).domain j) = φ '' W := by
  simp only [(P.partition _).covers]
  rw [← image_iUnion, P.covers]

end MaximalCoordinateGraphPartitionsOn

/-- **Volume engine for C¹ pieces.** Countably many disjoint pieces `φᵢ '' Wᵢ`
inside a set `C` whose coordinate fibers have at most `M` points almost
everywhere. The pieces need only be C¹, injective and immersive on the open unit
cube, with measurable domains `Wᵢ` in the cube. -/
theorem volume_iUnion_C1Pieces_le {a m : ℕ} {ι : Type*} [Countable ι]
    (φ : ι → RealEuclidean m → RealEuclidean a) (W : ι → Set (RealEuclidean m))
    (hWm : ∀ i, MeasurableSet (W i)) (hWcube : ∀ i, W i ⊆ openUnitCube m)
    (hφ : ∀ i, ContDiffOn ℝ 1 (φ i) (openUnitCube m))
    (hinj : ∀ i, InjOn (φ i) (openUnitCube m))
    (hder : ∀ i, ∀ x ∈ openUnitCube m, Function.Injective (fderiv ℝ (φ i) x))
    (hdis : Pairwise (fun i j => Disjoint (φ i '' W i) (φ j '' W j)))
    (C : Set (RealEuclidean a)) (hSC : ∀ i, φ i '' W i ⊆ C)
    {R : ℝ} (hR : C ⊆ closedBall 0 R) (M : ℕ)
    (hfib : ∀ I : Fin m → Fin a, Function.Injective I →
      ∀ᵐ y, (semialgebraicMapFiber C (coordinateProjection I) y).Finite ∧
        Nat.card (semialgebraicMapFiber C (coordinateProjection I) y) ≤ M)
    (p : RealEuclidean a → RealEuclidean m) {U : Set (RealEuclidean a)}
    (hU : IsOpen U) (hCU : C ⊆ U) (hp : ContDiffOn ℝ 1 p U)
    {b : ℝ} (hb : 0 ≤ b) (hJ : ∀ x ∈ C, topRealJacobian (fderiv ℝ p x) ≤ b) :
    volume (p '' (⋃ i, φ i '' W i)) ≤ (2 : ℝ≥0∞) ^ a *
      (ENNReal.ofReal (b * (2 : ℝ) ^ a) * (M : ℝ≥0∞) *
        volume (closedBall (0 : RealEuclidean m) R)) := by
  classical
  set S : ι → Set (RealEuclidean a) := fun i => φ i '' W i with hSdef
  let P (i : ι) : MaximalCoordinateGraphPartitionsOn (φ i) (W i) :=
    (exists_maximalCoordinateGraphPartitionsOn (hφ i) (hinj i) (hder i) (hWm i) (hWcube i)).some
  let D (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) := (P u.1).partition s |>.domain u.2
  let O (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) :=
    ((P u.1).partition s |>.chart u.2).baseDomain
  let g (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) := ((P u.1).partition s |>.chart u.2).graph
  have hpiece (s : Set.powersetCard (Fin a) m) (u : ι × ℕ) : g s u '' D s u ⊆ S u.1 := by
    rintro x ⟨y, hy, rfl⟩
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
      have hi' : x ∈ φ i '' W i := hi
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
  change volume (p '' (⋃ i, S i)) ≤ _
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
