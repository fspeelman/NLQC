import NLQCLean.Geometry.DirectVolume.Count
import NLQCLean.Geometry.C1PieceFamilyVolume

/-!
# Direct image-volume route: charts of the Lagrange sets

At a regular level the lifted Lagrange level set is an `m`-dimensional manifold
whose tangent spaces project injectively to the point coordinates (L9). Near each
of its points, a coordinate projection `π_I` and the inverse function theorem for
the equal-dimensional map `K = (H, π_I ∘ x)` give a C¹ chart of the Lagrange set
defined on the open unit cube (L10). Countably many such charts, disjointified,
cover the Lagrange set and satisfy every hypothesis of the C¹-piece volume
engine (L11). Roadmap step D5 (`D0-PROOF.md` §8.3, §9).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function Filter Topology Metric

variable {a m L D : ℕ}

/-- The center of the open unit cube. -/
noncomputable def cubeCenter (m : ℕ) : RealEuclidean m := WithLp.toLp 2 fun _ => 1 / 2

theorem cubeCenter_mem (m : ℕ) : cubeCenter m ∈ openUnitCube m := by
  intro i; simp [cubeCenter]; norm_num

theorem norm_sub_cubeCenter_lt {u : RealEuclidean m} (hu : u ∈ openUnitCube m) :
    ‖u - cubeCenter m‖ < m + 1 := by
  have hsq : ‖u - cubeCenter m‖ ^ 2 < ((m : ℝ) + 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hle : ∑ i, ((u - cubeCenter m) i) ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hu i
      simp only [cubeCenter, PiLp.sub_apply]
      nlinarith [this.1, this.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hle
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- **L10 (chart at a point).** -/
theorem exists_lagrangeChart_at (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (b : Fin L → ℝ)
    (v : Fin a → ℝ)
    (hreg : ∀ q, lagrangeMap p g J q = (b, v) → Surjective (fderiv ℝ (lagrangeMap p g J) q))
    {q₀ : Fin (a + m + L) → ℝ} (hq₀ : q₀ ∈ lagrangeLevel p g J b v) :
    ∃ (A : Set (Fin (a + m + L) → ℝ)) (φ : RealEuclidean m → RealEuclidean a),
      IsOpen A ∧ q₀ ∈ A ∧ ContDiffOn ℝ 1 φ (openUnitCube m) ∧ InjOn φ (openUnitCube m) ∧
      (∀ u ∈ openUnitCube m, Injective (fderiv ℝ φ u)) ∧
      φ '' openUnitCube m ⊆ lagrangeSet p g J b v ∧
      liftX '' (lagrangeLevel p g J b v ∩ A) ⊆ φ '' openUnitCube m := by
  classical
  set H := lagrangeMap p g J with hH
  have hHq₀ : H q₀ = (b, v) := Set.mem_singleton_iff.mp hq₀.1
  have hHdiff : ∀ q, DifferentiableAt ℝ H q := fun q =>
    ((contDiff_lagrangeMap p g J).differentiable (by simp)).differentiableAt
  set DH := fderiv ℝ H q₀ with hDH
  have hsurj : Surjective DH := hreg q₀ hHq₀
  -- The kernel of `DH` has dimension `m`.
  set P₀ : Submodule ℝ (Fin (a + m + L) → ℝ) := LinearMap.ker DH.toLinearMap with hP₀
  have hrank : Module.finrank ℝ P₀ = m := by
    have h := LinearMap.finrank_range_add_finrank_ker DH.toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod,
      Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    change L + a + Module.finrank ℝ P₀ = a + m + L at h
    omega
  let e : RealEuclidean m ≃L[ℝ] P₀ :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hrank])
  let Lx : RealEuclidean m →L[ℝ] RealEuclidean a :=
    (liftXL a m).comp ((P₀.subtypeL).comp (e : RealEuclidean m →L[ℝ] P₀))
  have hkerzero : ∀ w ∈ P₀, liftX w = 0 → w = 0 := by
    intro w hw hlx
    refine eq_zero_of_fderiv_lagrangeMap_vertical p g J hq₀.2 (fun k => ?_) hw
    have := congrArg (fun x : RealEuclidean a => x k) hlx
    simpa [liftX] using this
  have hL : Injective Lx := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hw := hkerzero (e u) (e u).2 (by simpa [Lx] using hu)
    have : e u = 0 := Subtype.ext hw
    simpa using this
  obtain ⟨I, -, hbij⟩ := exists_bijective_coordinateProjection_comp Lx hL
  -- The equal-dimensional map `K` has an invertible derivative.
  set K := lagrangeCoordMap p g J I with hKdef
  set DK : (Fin (a + m + L) → ℝ) →L[ℝ] ((Fin L → ℝ) × (Fin a → ℝ)) × RealEuclidean m :=
    DH.prod ((coordinateProjectionL I).comp (liftXL a m)) with hDK
  have hKd : HasFDerivAt K DK q₀ := by
    refine (hHdiff q₀).hasFDerivAt.prodMk ?_
    have : (fun q => coordinateProjection I (liftX q)) =
        ((coordinateProjectionL I).comp (liftXL a m) : (Fin (a + m + L) → ℝ) →L[ℝ] _) := by
      funext q; simp [coordinateProjectionL]
    rw [this]
    exact ContinuousLinearMap.hasFDerivAt _
  have hDKinj : Injective DK := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    simp only [hDK, ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hw
    have hwP : w ∈ P₀ := hw.1
    set u := e.symm ⟨w, hwP⟩ with hu
    have hLu : Lx u = liftX w := by simp [Lx, hu]
    have hπ : (coordinateProjectionL I).comp Lx u = 0 := by
      simp only [ContinuousLinearMap.coe_comp, comp_apply, hLu]
      simpa using hw.2
    have hu0 : u = 0 := hbij.1 (by rw [hπ, map_zero])
    have : (⟨w, hwP⟩ : P₀) = 0 := by
      rw [← e.apply_symm_apply ⟨w, hwP⟩, ← hu, hu0, map_zero]
    simpa using congrArg Subtype.val this
  have hDKbij : Bijective DK := by
    refine ⟨hDKinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_lagrangeCoordMap_target, Module.finrank_fin_fun])
      (f := DK.toLinearMap)).mp hDKinj
  let K' := (LinearEquiv.ofBijective DK.toLinearMap hDKbij).toContinuousLinearEquiv
  have hK'eq : (K' : (Fin (a + m + L) → ℝ) →L[ℝ] _) = DK :=
    ContinuousLinearMap.ext fun _ => rfl
  have hKd' : HasFDerivAt K (K' : (Fin (a + m + L) → ℝ) →L[ℝ] _) q₀ := by
    rw [hK'eq]; exact hKd
  have hKAt : ContDiffAt ℝ 1 K q₀ :=
    ((contDiff_lagrangeCoordMap p g J I).of_le (by simp)).contDiffAt
  -- Inverse function theorem.
  let E := hKAt.toOpenPartialHomeomorph K hKd' one_ne_zero
  have hE : (E : _ → _) = K := hKAt.toOpenPartialHomeomorph_coe hKd' one_ne_zero
  have hq₀S : q₀ ∈ E.source := hKAt.mem_toOpenPartialHomeomorph_source hKd' one_ne_zero
  have hw₀T : K q₀ ∈ E.target := by rw [← hE]; exact E.map_source hq₀S
  have hleft : E.symm (K q₀) = q₀ := by
    have := E.left_inv hq₀S; rwa [hE] at this
  have hInv : ContDiffAt ℝ 1 E.symm (K q₀) := by
    apply E.contDiffAt_symm hw₀T (f₀' := K')
    · simpa only [hleft, hE] using hKd'
    · simpa only [hleft, hE] using hKAt
  have hG : ContDiffAt ℝ 1 (liftX ∘ E.symm) (K q₀) := by
    have hlx : ContDiffAt ℝ 1 (liftX : (Fin (a + m + L) → ℝ) → RealEuclidean a)
        (E.symm (K q₀)) := by
      have : (liftX : (Fin (a + m + L) → ℝ) → RealEuclidean a) = liftXL a m := by
        funext q; simp
      rw [this]; exact (liftXL a m).contDiff.contDiffAt
    exact hlx.comp _ hInv
  obtain ⟨u₀, hu₀, hGu⟩ := hG.contDiffOn le_rfl (by simp)
  have hpre : E.symm ⁻¹' lagrangeOpen p g J b ∈ 𝓝 (K q₀) :=
    hInv.continuousAt.preimage_mem_nhds (by
      rw [hleft]; exact (isOpen_lagrangeOpen p g J b).mem_nhds hq₀.2)
  set W' := u₀ ∩ (E.target ∩ E.symm ⁻¹' lagrangeOpen p g J b) with hW'
  have hW'n : W' ∈ 𝓝 (K q₀) := inter_mem hu₀ (inter_mem (E.open_target.mem_nhds hw₀T) hpre)
  -- A small box around the slice value.
  set z₀ := coordinateProjection I (liftX q₀) with hz₀
  let ι : RealEuclidean m → ((Fin L → ℝ) × (Fin a → ℝ)) × RealEuclidean m := fun z => ((b, v), z)
  have hιc : Continuous ι := continuous_const.prodMk continuous_id
  have hKq₀ : K q₀ = ι z₀ := by
    change (H q₀, coordinateProjection I (liftX q₀)) = ((b, v), z₀)
    rw [hHq₀]
  have hιn : ι ⁻¹' W' ∈ 𝓝 z₀ := hιc.continuousAt.preimage_mem_nhds (by rw [← hKq₀]; exact hW'n)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hιn
  set s : ℝ := ε / (m + 1) with hs
  have hspos : 0 < s := by positivity
  let ψ : RealEuclidean m → RealEuclidean m := fun u => z₀ + s • (u - cubeCenter m)
  let ψinv : RealEuclidean m → RealEuclidean m := fun z => cubeCenter m + s⁻¹ • (z - z₀)
  have hψinv : ∀ u, ψinv (ψ u) = u := by
    intro u; simp only [ψ, ψinv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hspos.ne',
      one_smul, add_sub_cancel]
  have hψψinv : ∀ z, ψ (ψinv z) = z := by
    intro z; simp only [ψ, ψinv, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hspos.ne',
      one_smul, add_sub_cancel]
  have hψW : ∀ u ∈ openUnitCube m, ι (ψ u) ∈ W' := by
    intro u hu
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp only [ψ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    calc s * ‖u - cubeCenter m‖ < s * (m + 1) :=
          mul_lt_mul_of_pos_left (norm_sub_cubeCenter_lt hu) hspos
      _ = ε := by rw [hs]; field_simp
  set φ : RealEuclidean m → RealEuclidean a := fun u => liftX (E.symm (ι (ψ u))) with hφ
  -- Properties of the chart.
  have hKφ : ∀ u ∈ openUnitCube m, K (E.symm (ι (ψ u))) = ι (ψ u) := by
    intro u hu
    have := E.right_inv (hψW u hu).2.1
    rwa [hE] at this
  have hπφ : ∀ u ∈ openUnitCube m, coordinateProjection I (φ u) = ψ u := by
    intro u hu
    have := congrArg Prod.snd (hKφ u hu)
    simpa [hKdef, lagrangeCoordMap, ι, hφ] using this
  have hψc : ContDiff ℝ 1 (fun u => ι (ψ u)) := by
    refine contDiff_const.prodMk ?_
    exact contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul s)
  have hφC : ContDiffOn ℝ 1 φ (openUnitCube m) :=
    hGu.comp hψc.contDiffOn fun u hu => (hψW u hu).1
  refine ⟨E.source ∩ {q | ψinv (coordinateProjection I (liftX q)) ∈ openUnitCube m}, φ,
    ?_, ?_, hφC, ?_, ?_, ?_, ?_⟩
  · refine E.open_source.inter ((isOpen_openUnitCube m).preimage ?_)
    have : Continuous fun q : Fin (a + m + L) → ℝ => coordinateProjection I (liftX q) := by
      have h : (fun q : Fin (a + m + L) → ℝ => coordinateProjection I (liftX q)) =
          ((coordinateProjectionL I).comp (liftXL a m) : (Fin (a + m + L) → ℝ) →L[ℝ] _) := by
        funext q; simp [coordinateProjectionL]
      rw [h]; exact ContinuousLinearMap.continuous _
    exact continuous_const.add ((this.sub (continuous_const (y := z₀))).const_smul s⁻¹)
  · refine ⟨hq₀S, ?_⟩
    show ψinv z₀ ∈ openUnitCube m
    simpa [ψinv] using cubeCenter_mem m
  · intro u hu u' hu' huu
    have h1 := hπφ u hu
    have h2 := hπφ u' hu'
    rw [huu] at h1
    rw [← hψinv u, ← hψinv u', ← h1, h2]
  · intro u hu
    rw [injective_iff_map_eq_zero]
    intro w hzero
    have hev : (fun u => coordinateProjection I (φ u)) =ᶠ[𝓝 u] ψ := by
      filter_upwards [(isOpen_openUnitCube m).mem_nhds hu] with u' hu'
      exact hπφ u' hu'
    have hφd : HasFDerivAt φ (fderiv ℝ φ u) u :=
      ((hφC u hu).differentiableWithinAt one_ne_zero).differentiableAt
        ((isOpen_openUnitCube m).mem_nhds hu) |>.hasFDerivAt
    have hψd : HasFDerivAt ψ (s • ContinuousLinearMap.id ℝ (RealEuclidean m)) u := by
      have := ((hasFDerivAt_id (𝕜 := ℝ) u).sub_const (cubeCenter m)).const_smul s |>.const_add z₀
      simpa [ψ] using this
    have h1 : HasFDerivAt (fun u => coordinateProjection I (φ u))
        ((coordinateProjectionL I).comp (fderiv ℝ φ u)) u :=
      (coordinateProjectionL I).hasFDerivAt.comp u hφd
    have h2 := (hψd.congr_of_eventuallyEq hev).unique h1
    have := congrArg (fun T : RealEuclidean m →L[ℝ] RealEuclidean m => T w) h2
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.coe_comp, comp_apply] at this
    rw [hzero, map_zero] at this
    exact (smul_eq_zero.mp this).resolve_left hspos.ne'
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨E.symm (ι (ψ u)), ⟨?_, (hψW u hu).2.2⟩, rfl⟩
    have := congrArg Prod.fst (hKφ u hu)
    simpa [hKdef, lagrangeCoordMap, ι, hH] using this
  · rintro _ ⟨q, ⟨hqL, hqS, hqA⟩, rfl⟩
    refine ⟨ψinv (coordinateProjection I (liftX q)), hqA, ?_⟩
    have hKq : K q = ι (ψ (ψinv (coordinateProjection I (liftX q)))) := by
      rw [hψψinv]
      simp [hKdef, lagrangeCoordMap, ι, Set.mem_singleton_iff.mp hqL.1]
    have hqE : E.symm (K q) = q := by
      have := E.left_inv hqS; rwa [hE] at this
    simp only [hφ]
    rw [← hKq, hqE]

/-- **L11 (countable disjoint charts).** A nonempty Lagrange set at a regular
level is the disjoint union of countably many C¹ pieces `φₙ '' Dₙ` with
measurable domains in the open unit cube. -/
theorem exists_lagrangeCharts (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (b : Fin L → ℝ)
    (v : Fin a → ℝ)
    (hreg : ∀ q, lagrangeMap p g J q = (b, v) → Surjective (fderiv ℝ (lagrangeMap p g J) q))
    (hne : (lagrangeLevel p g J b v).Nonempty) :
    ∃ (φ : ℕ → RealEuclidean m → RealEuclidean a) (D : ℕ → Set (RealEuclidean m)),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, D n ⊆ openUnitCube m) ∧
      (∀ n, ContDiffOn ℝ 1 (φ n) (openUnitCube m)) ∧
      (∀ n, InjOn (φ n) (openUnitCube m)) ∧
      (∀ n, ∀ u ∈ openUnitCube m, Injective (fderiv ℝ (φ n) u)) ∧
      Pairwise (fun i j => Disjoint (φ i '' D i) (φ j '' D j)) ∧
      (⋃ n, φ n '' D n) = lagrangeSet p g J b v := by
  classical
  set W := lagrangeLevel p g J b v with hW
  have hex : ∀ q : W, ∃ (A : Set (Fin (a + m + L) → ℝ)) (φ : RealEuclidean m → RealEuclidean a),
      IsOpen A ∧ (q : Fin (a + m + L) → ℝ) ∈ A ∧ ContDiffOn ℝ 1 φ (openUnitCube m) ∧
      InjOn φ (openUnitCube m) ∧ (∀ u ∈ openUnitCube m, Injective (fderiv ℝ φ u)) ∧
      φ '' openUnitCube m ⊆ lagrangeSet p g J b v ∧ liftX '' (W ∩ A) ⊆ φ '' openUnitCube m :=
    fun q => exists_lagrangeChart_at p g J b v hreg q.2
  choose A φ hAo hqA hφC hφI hφD hφsub hφcov using hex
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  obtain ⟨q₀, hq₀⟩ := hne
  have hTne : T.Nonempty := by
    have h : (q₀ : Fin (a + m + L) → ℝ) ∈ ⋃ i ∈ T, A i := by
      rw [hTU]; exact mem_iUnion.mpr ⟨⟨q₀, hq₀⟩, hqA ⟨q₀, hq₀⟩⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    obtain ⟨hiT, -⟩ := mem_iUnion.mp hi
    exact ⟨i, hiT⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  set ψ : ℕ → RealEuclidean m → RealEuclidean a := fun n => φ (f n) with hψ
  set S : ℕ → Set (RealEuclidean a) := fun n => ψ n '' openUnitCube m with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (isOpen_openUnitCube m).measurableSet.image_of_continuousOn_injOn
      (hφC (f n)).continuousOn (hφI (f n))
  have hcover : (⋃ n, S n) = lagrangeSet p g J b v := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => hφsub (f n)
    · rintro _ ⟨q, hqW, rfl⟩
      have h : q ∈ ⋃ i ∈ T, A i := by
        rw [hTU]; exact mem_iUnion.mpr ⟨⟨q, hqW⟩, hqA ⟨q, hqW⟩⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      obtain ⟨hiT, hqi⟩ := mem_iUnion.mp hi
      rw [hf] at hiT
      obtain ⟨n, rfl⟩ := hiT
      exact mem_iUnion.mpr ⟨n, hφcov (f n) ⟨q, ⟨hqW, hqi⟩, rfl⟩⟩
  -- Disjointify the images (repair R1 of the D0 review).
  set E : ℕ → Set (RealEuclidean a) := disjointed S with hE
  set D : ℕ → Set (RealEuclidean m) := fun n => openUnitCube m ∩ ψ n ⁻¹' E n with hD
  have hDm : ∀ n, MeasurableSet (D n) := by
    intro n
    have hmeas : Measurable ((openUnitCube m).piecewise (ψ n) fun _ => 0) :=
      ContinuousOn.measurable_piecewise (hφC (f n)).continuousOn continuousOn_const
        (isOpen_openUnitCube m).measurableSet
    have : D n = openUnitCube m ∩ ((openUnitCube m).piecewise (ψ n) fun _ => 0) ⁻¹' E n := by
      ext u
      simp only [hD, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hu, h⟩; exact ⟨hu, by rwa [Set.piecewise_eq_of_mem _ _ _ hu]⟩
      · rintro ⟨hu, h⟩; exact ⟨hu, by rwa [Set.piecewise_eq_of_mem _ _ _ hu] at h⟩
    rw [this]
    exact (isOpen_openUnitCube m).measurableSet.inter
      (hmeas (MeasurableSet.disjointed hSm n))
  have himage : ∀ n, ψ n '' D n = E n := by
    intro n
    apply Subset.antisymm
    · rintro _ ⟨u, ⟨-, hu⟩, rfl⟩; exact hu
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := disjointed_subset S n hx
      exact ⟨u, ⟨hu, hx⟩, rfl⟩
  refine ⟨ψ, D, hDm, fun n => inter_subset_left, fun n => hφC (f n), fun n => hφI (f n),
    fun n => hφD (f n), ?_, ?_⟩
  · intro i j hij
    rw [himage i, himage j]
    exact disjoint_disjointed S hij
  · simp only [himage]
    rw [hE, iUnion_disjointed, hcover]

end NLQCLean.DirectVolume
