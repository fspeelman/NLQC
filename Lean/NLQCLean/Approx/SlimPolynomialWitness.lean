import NLQCLean.Approx.SlimWitnessCoordinates
import NLQCLean.Approx.PolynomialWitnessThickening
import NLQCLean.Approx.ReachableWitnessCover

/-!
# The slim polynomial witness family and its compact target cover

Seven polynomial equations (two spheres, four normalized Gram
constraints with column counts `d r` and `d s`, zero padding) and one leakage inequality,
all of degree at most twelve, define a compact source of radius `√6` in `ℝ^(38K²)`. The
normalized cubic overlap `h = H/d` is a polynomial map of degree at most eighteen.
Thickening adds one ball constraint (radius `√7 < 3`). Every target `U ∈ S_d` that is pure or
finite-mixed score reachable at `0 ≤ e ≤ 1/16` lies in the compact witness target set of some
slim shape at normalized distance `√(21 e / 2)`; only inclusion is asserted.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker

theorem polynomialDegree_normalizedOutputCoordinates {a d D : ℕ}
    {f : RealEuclidean a → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE D (fun x => normalizedOutputCoordinates d (f x) j) := by
  simpa only [normalizedOutputCoordinates_apply] using
    polynomialDegree_overlapOutputCoordinates (hf.real_smul (1 / (d : ℝ))) j

namespace SlimReverseBlocks

variable {a d K D : ℕ} {s : SlimReverseShape d K}

/-- One degree bound for each coordinate of the six independent slim blocks. -/
def PolynomialDegreeLE (D : ℕ) (f : RealEuclidean a → SlimReverseBlocks s) : Prop :=
  (∀ i, ComplexPolynomialDegreeLE D (fun x => (f x).1 i)) ∧
  (∀ i, ComplexPolynomialDegreeLE D (fun x => (f x).2.1 i)) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.2.2)

namespace PolynomialDegreeLE

variable {f : RealEuclidean a → SlimReverseBlocks s}

theorem linear (L : RealEuclidean a →ₗ[ℝ] SlimReverseBlocks s) :
    PolynomialDegreeLE 1 (fun x => L x) := by
  let Lη := (LinearMap.fst ℝ _ _).comp L
  let L1 := (LinearMap.snd ℝ _ _).comp L
  let Lg := (LinearMap.fst ℝ _ _).comp L1
  let L2 := (LinearMap.snd ℝ _ _).comp L1
  let LA := (LinearMap.fst ℝ _ _).comp L2
  let L3 := (LinearMap.snd ℝ _ _).comp L2
  let LB := (LinearMap.fst ℝ _ _).comp L3
  let L4 := (LinearMap.snd ℝ _ _).comp L3
  let LTA := (LinearMap.fst ℝ _ _).comp L4
  let LTB := (LinearMap.snd ℝ _ _).comp L4
  exact ⟨fun i => ComplexPolynomialDegreeLE.linear ((LinearMap.proj i).comp Lη),
    fun i => ComplexPolynomialDegreeLE.linear ((LinearMap.proj i).comp Lg),
    MatrixPolynomialDegreeLE.linear LA, MatrixPolynomialDegreeLE.linear LB,
    MatrixPolynomialDegreeLE.linear LTA, MatrixPolynomialDegreeLE.linear LTB⟩

theorem rescale (hf : PolynomialDegreeLE D f) :
    PolynomialDegreeLE D (fun x => rescaleBlocks (f x)) :=
  ⟨hf.1, hf.2.1, hf.2.2.1.real_smul _, hf.2.2.2.1.real_smul _,
    hf.2.2.2.2.1.real_smul _, hf.2.2.2.2.2.real_smul _⟩

theorem cubic (hf : PolynomialDegreeLE D f) :
    PolynomialDegreeLE (3 * D) (fun x => normalizedCubicBlocks (f x)) :=
  ⟨polynomialDegree_cubicSphere hf.1, polynomialDegree_cubicSphere hf.2.1,
    hf.2.2.1.rescaledCubicStiefel _, hf.2.2.2.1.rescaledCubicStiefel _,
    hf.2.2.2.2.1.rescaledCubicStiefel _, hf.2.2.2.2.2.rescaledCubicStiefel _⟩

theorem forward (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x => SlimReverseBlocks.forward (f x)) := by
  have hJ := polynomialDegree_insertResource (ιA := Fin d) (ιB := Fin d) hf.1
  have h := (MatrixPolynomialDegreeLE.const (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)).mul
    ((MatrixPolynomialDegreeLE.const
      (exchangeMatrix (Fin (d * s.1.r * s.1.mA)) (Fin s.1.mA) (Fin (d * s.1.r * s.1.mB))
        (Fin s.1.mB))).mul ((hf.2.2.1.kronecker hf.2.2.2.1).mul hJ))
  exact h.mono (by omega)

theorem reverse (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x => SlimReverseBlocks.reverse (f x)) := by
  have hJ := polynomialDegree_insertResource (ιA := Fin d) (ιB := Fin d) hf.2.1
  exact ((hf.2.2.2.2.1.kronecker hf.2.2.2.2.2).mul hJ).mono (by omega)

theorem overlap (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (6 * D) (fun x => SlimReverseBlocks.overlap (f x)) :=
  (hf.reverse.conjTranspose.mul hf.forward).mono (by omega)

end PolynomialDegreeLE

variable (s : SlimReverseShape d K) (hd : 2 ≤ d)

theorem polynomialDegree_rawOverlap :
    MatrixPolynomialDegreeLE 6 (fun x => overlap (rescaleBlocks (decodeCoordinates s hd x))) := by
  have h := (PolynomialDegreeLE.linear (decodeCoordinates s hd)).rescale.overlap
  simpa only [mul_one] using h

theorem polynomialDegree_extendedOverlap :
    MatrixPolynomialDegreeLE 18 (fun x => extendedOverlap (decodeCoordinates s hd x)) :=
  (PolynomialDegreeLE.linear (decodeCoordinates s hd)).cubic.rescale.overlap

theorem polynomialDegree_coordinateOverlap (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE 18 (fun x => coordinateOverlap s hd x j) :=
  polynomialDegree_normalizedOutputCoordinates (polynomialDegree_extendedOverlap s hd) j

theorem polynomialDegree_rawLeakage : RealPolynomialDegreeLE 12
    (fun x => (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2) :=
  (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2)).sub
    (polynomialDegree_rawOverlap s hd).frobNorm_sq

/-- The normalized cubic overlap, packaged for the fixed polynomial contract. -/
noncomputable def coordinateOverlapPolynomial :
    BoundedPolynomialMap (slimCoordinateBudget K) (2 * d ^ 4) where
  coordinates j := Classical.choose (polynomialDegree_coordinateOverlap s hd j)
  degree_le j :=
    (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd j)).1.trans (by decide)

theorem coordinateOverlapPolynomial_eval (x : RealEuclidean (slimCoordinateBudget K)) :
    (coordinateOverlapPolynomial s hd).eval x = coordinateOverlap s hd x := by
  ext j
  exact (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd j)).2 x

noncomputable def paddingDefect (x : RealEuclidean (slimCoordinateBudget K)) : ℝ := by
  classical
  exact ∑ j, if j ∈ Set.range (coordinateEmbedding s hd) then 0 else x j ^ 2

theorem paddingDefect_eq_zero_iff (x : RealEuclidean (slimCoordinateBudget K)) :
    paddingDefect s hd x = 0 ↔ ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0 := by
  classical
  rw [paddingDefect, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by split <;> positivity)]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h j hj
    simpa only [ite_eq_right hj, sq_eq_zero_iff] using h j
  · intro h j
    by_cases hj : j ∈ Set.range (coordinateEmbedding s hd)
    · simp only [ite_eq_left hj]
    · simp only [ite_eq_right hj, h j hj, zero_pow (by decide : 2 ≠ 0)]

theorem polynomialDegree_paddingDefect : RealPolynomialDegreeLE 2 (paddingDefect s hd) := by
  classical
  apply RealPolynomialDegreeLE.sum Finset.univ
  intro j _
  by_cases hj : j ∈ Set.range (coordinateEmbedding s hd)
  · simpa only [ite_eq_left hj] using (RealPolynomialDegreeLE.const 0).mono (by decide : 0 ≤ 2)
  · simpa only [ite_eq_right hj] using (RealPolynomialDegreeLE.coord j).sq

/-- Two sphere, four Gram, and one padding equation. -/
noncomputable def witnessEquations (i : Fin 7) (x : RealEuclidean (slimCoordinateBudget K)) : ℝ :=
  let z := decodeCoordinates s hd x
  ![sphereDefect z.1, sphereDefect z.2.1,
    gramDefectSq (d * s.1.r : ℝ) z.2.2.1, gramDefectSq (d * s.1.r : ℝ) z.2.2.2.1,
    gramDefectSq (d * frozenSupport d K : ℝ) z.2.2.2.2.1,
    gramDefectSq (d * frozenSupport d K : ℝ) z.2.2.2.2.2,
    paddingDefect s hd x] i

theorem polynomialDegree_witnessEquations (i : Fin 7) :
    RealPolynomialDegreeLE 12 (witnessEquations s hd i) := by
  have hb := PolynomialDegreeLE.linear (decodeCoordinates s hd)
  have hη := (polynomialDegree_sqNorm hb.1).sub (RealPolynomialDegreeLE.const 1)
  have hg := (polynomialDegree_sqNorm hb.2.1).sub (RealPolynomialDegreeLE.const 1)
  fin_cases i
  · exact hη.mono (by decide)
  · exact hg.mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.2.2 _).mono (by decide)
  · exact (polynomialDegree_paddingDefect s hd).mono (by decide)

theorem witnessEquations_zero_iff (x : RealEuclidean (slimCoordinateBudget K)) :
    (∀ i, witnessEquations s hd i x = 0) ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd x)) ∧
        ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0 := by
  have hdr : 0 ≤ (d * s.1.r : ℝ) := by positivity
  have hdK : 0 ≤ (d * frozenSupport d K : ℝ) := by positivity
  simp [witnessEquations, Fin.forall_fin_succ, sphereDefect_eq_zero_iff,
    gramDefectSq_eq_zero_iff _ hdr, gramDefectSq_eq_zero_iff _ hdK,
    paddingDefect_eq_zero_iff, IsValid, rescaleBlocks, and_assoc]

noncomputable def witnessInequality (δ : ℝ) (x : RealEuclidean (slimCoordinateBudget K)) : ℝ :=
  (d : ℝ) ^ 2 * δ ^ 2 - ((d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2)

theorem polynomialDegree_witnessInequality (δ : ℝ) :
    RealPolynomialDegreeLE 12 (witnessInequality s hd δ) :=
  (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2 * δ ^ 2)).sub (polynomialDegree_rawLeakage s hd)

/-- Polynomial witness source: the exact eight-constraint slim source in the fixed polynomial format. -/
noncomputable def witnessFormat (δ : ℝ) : PolynomialBasicClosedFormat (slimCoordinateBudget K) where
  numEquations := 7
  numInequalities := 1
  constraint_count := by decide
  equations i := Classical.choose (polynomialDegree_witnessEquations s hd i)
  inequalities _ := Classical.choose (polynomialDegree_witnessInequality s hd δ)
  equations_degree i :=
    (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).1.trans (by decide)
  inequalities_degree _ :=
    (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).1.trans (by decide)

theorem witnessFormat_equation_eval (δ : ℝ) (i : Fin 7) (x : RealEuclidean (slimCoordinateBudget K)) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).equations i) =
      witnessEquations s hd i x :=
  (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).2 x

theorem witnessFormat_inequality_eval (δ : ℝ) (i : Fin 1)
    (x : RealEuclidean (slimCoordinateBudget K)) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).inequalities i) =
      witnessInequality s hd δ x :=
  (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).2 x

theorem mem_witnessFormat_source_iff (δ : ℝ) (x : RealEuclidean (slimCoordinateBudget K)) :
    x ∈ (witnessFormat s hd δ).source ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd x)) ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) ∧
      (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2 ≤
        (d : ℝ) ^ 2 * δ ^ 2 := by
  change ((∀ i : Fin 7, MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).equations i) = 0) ∧
    (∀ i : Fin 1, 0 ≤ MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).inequalities i))) ↔ _
  constructor
  · rintro ⟨he, hi⟩
    have he' : ∀ i, witnessEquations s hd i x = 0 := by
      intro i
      rw [← witnessFormat_equation_eval s hd δ i x]
      exact he i
    obtain ⟨hx, hpad⟩ := (witnessEquations_zero_iff s hd x).mp he'
    have hb := hi 0
    rw [witnessFormat_inequality_eval] at hb
    exact ⟨hx, hpad, sub_nonneg.mp hb⟩
  · rintro ⟨hx, hpad, hdef⟩
    refine ⟨?_, ?_⟩
    · intro i
      rw [witnessFormat_equation_eval]
      exact (witnessEquations_zero_iff s hd x).mpr ⟨hx, hpad⟩ i
    · intro i
      rw [witnessFormat_inequality_eval]
      exact sub_nonneg.mpr hdef

theorem norm_mem_witnessFormat_source (δ : ℝ) {x : RealEuclidean (slimCoordinateBudget K)}
    (hx : x ∈ (witnessFormat s hd δ).source) : ‖x‖ = Real.sqrt 6 := by
  obtain ⟨hv, hp, _⟩ := (mem_witnessFormat_source_iff s hd δ x).mp hx
  exact norm_padded_valid_eq_sqrt_six s hd hv hp

theorem isCompact_witnessFormat_source (δ : ℝ) : IsCompact (witnessFormat s hd δ).source := by
  apply Metric.isCompact_of_isClosed_isBounded (witnessFormat s hd δ).isClosed_source
  exact (isBounded_iff_forall_norm_le).mpr
    ⟨Real.sqrt 6, fun x hx => (norm_mem_witnessFormat_source s hd δ hx).le⟩

theorem witnessFormat_source_subset_ball (δ : ℝ) :
    (witnessFormat s hd δ).source ⊆ Metric.closedBall 0 3 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, norm_mem_witnessFormat_source s hd δ hx]
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ)), Real.sqrt_nonneg (6 : ℝ)]

/-- Every valid slim witness with the leakage bound lies in the source; its normalized overlap
is a polynomial value. -/
theorem exists_mem_witnessFormat_source (δ : ℝ) {x : SlimReverseBlocks s} (hx : IsValid x)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ y ∈ (witnessFormat s hd δ).source,
      (coordinateOverlapPolynomial s hd).eval y = normalizedOutputCoordinates d (overlap x) := by
  obtain ⟨y, hy, hp, _, hraw⟩ := exists_normalized_coordinate_witness s hd hx
  have hv : IsValid (rescaleBlocks (decodeCoordinates s hd y)) := hy.symm ▸ hx
  have hs : y ∈ (witnessFormat s hd δ).source :=
    (mem_witnessFormat_source_iff s hd δ y).mpr ⟨hv, hp, by rw [hy]; exact hdef⟩
  refine ⟨y, hs, ?_⟩
  rw [coordinateOverlapPolynomial_eval, coordinateOverlap_eq_raw s hd hv]
  exact hraw

noncomputable def thickenedWitnessFormat (δ : ℝ) :
    PolynomialBasicClosedFormat (slimCoordinateBudget K + 2 * d ^ 4) :=
  (witnessFormat s hd δ).thicken (2 * d ^ 4) (by change 7 + 1 + 1 ≤ 20; decide)

noncomputable def thickenedWitnessPolynomial (c : ℝ) :
    BoundedPolynomialMap (slimCoordinateBudget K + 2 * d ^ 4) (2 * d ^ 4) :=
  (coordinateOverlapPolynomial s hd).thicken c

theorem thickenedWitnessFormat_constraint_count (δ : ℝ) :
    (thickenedWitnessFormat s hd δ).numEquations +
      (thickenedWitnessFormat s hd δ).numInequalities = 9 := rfl

theorem thickenedWitnessPolynomial_degree (c : ℝ) (j) :
    ((thickenedWitnessPolynomial s hd c).coordinates j).totalDegree ≤ 18 :=
  (coordinateOverlapPolynomial s hd).thicken_degree c (by decide)
    (fun i => (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd i)).1) j

theorem isCompact_thickenedWitnessFormat_source (δ : ℝ) :
    IsCompact (thickenedWitnessFormat s hd δ).source :=
  (witnessFormat s hd δ).isCompact_thicken_source _
    (fun _ hx => (norm_mem_witnessFormat_source s hd δ hx).le)

theorem thickenedWitnessFormat_source_radius (δ : ℝ) :
    (thickenedWitnessFormat s hd δ).source ⊆ Metric.closedBall 0 3 :=
  (witnessFormat s hd δ).thicken_source_radius _
    (fun _ hx => (norm_mem_witnessFormat_source s hd δ hx).le)

theorem hasFDerivAt_thickenedWitnessPolynomial (c : ℝ)
    (z : RealEuclidean (slimCoordinateBudget K + 2 * d ^ 4)) :
    HasFDerivAt (thickenedWitnessPolynomial s hd c).eval
      (thickenedLinearMap (fderiv ℝ (coordinateOverlapPolynomial s hd).eval
        (euclideanProductCoordinates _ _ z).fst) c) z := by
  apply BoundedPolynomialMap.hasFDerivAt_thicken
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact ((contDiff_coordinateOverlap s hd).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- Compact slim witness targets at normalized distance `ρ`. -/
def witnessTargets (δ ρ : ℝ) : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ x ∈ (witnessFormat s hd δ).source,
    dist (normalizedOutputCoordinates d (U : Matrix _ _ ℂ))
      ((coordinateOverlapPolynomial s hd).eval x) ≤ ρ}

theorem continuous_coordinateOverlapPolynomial : Continuous (coordinateOverlapPolynomial s hd).eval := by
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact (contDiff_coordinateOverlap s hd).continuous

theorem isCompact_witnessTargets (δ ρ : ℝ) : IsCompact (witnessTargets s hd δ ρ) := by
  have hc : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      RealEuclidean (slimCoordinateBudget K) =>
        dist (normalizedOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd).eval z.2)) :=
    (((normalizedOutputCoordinates d).toContinuousLinearMap).continuous.comp
      (continuous_subtype_val.comp continuous_fst)).dist
        ((continuous_coordinateOverlapPolynomial s hd).comp continuous_snd)
  have hi : IsCompact ((Set.univ ×ˢ (witnessFormat s hd δ).source) ∩
      {z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × RealEuclidean (slimCoordinateBudget K) |
        dist (normalizedOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd).eval z.2) ≤ ρ}) :=
    (isCompact_univ.prod (isCompact_witnessFormat_source s hd δ)).inter_right
      (isClosed_le hc continuous_const)
  have hp := hi.image continuous_fst
  convert hp using 1
  ext U
  simp [witnessTargets]

theorem measurableSet_witnessTargets (δ ρ : ℝ) : MeasurableSet (witnessTargets s hd δ ρ) :=
  (isCompact_witnessTargets s hd δ ρ).isClosed.measurableSet

end SlimReverseBlocks

set_option maxHeartbeats 800000 in
/-- Polynomial witness coverage: near SWAP, pure score reachability at `0 ≤ e ≤ 1/16` is covered by the finite
family of compact slim witness targets at normalized distance `√(21 e / 2)`. -/
theorem swapNeighborhood_inter_pureReachable_subset_slimWitnessTargets {d K : ℕ} (hd : 2 ≤ d)
    {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 16) :
    swapNeighborhood d ∩ pureReachable d K e ⊆ ⋃ s : SlimReverseShape d K,
      SlimReverseBlocks.witnessTargets s hd (Real.sqrt (21 / 2 * e)) (Real.sqrt (21 / 2 * e)) := by
  rintro U ⟨hUS, t, P, hP, hscore⟩
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨s, x, hx, hdist⟩ := P.exists_slim_reverse_witness hd hUS hP he0 he hscore
  obtain ⟨hHU, -, -, hdef⟩ := hx.approximation (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (by positivity) hdist
  have hdef' : (d : ℝ) ^ 2 - ‖SlimReverseBlocks.overlap x‖ ^ 2 ≤
      (d : ℝ) ^ 2 * Real.sqrt (21 / 2 * e) ^ 2 := by
    simpa only [mul_pow] using hdef
  obtain ⟨y, hy, hyeval⟩ := SlimReverseBlocks.exists_mem_witnessFormat_source s hd _ hx hdef'
  refine Set.mem_iUnion.mpr ⟨s, y, hy, ?_⟩
  rw [hyeval, dist_eq_norm, ← map_sub, norm_normalizedOutputCoordinates hd0, norm_sub_rev,
    div_le_iff₀ hdR]
  linarith

theorem swapNeighborhood_inter_mixedReachable_subset_slimWitnessTargets {d K : ℕ} (hd : 2 ≤ d)
    {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 16) :
    swapNeighborhood d ∩ mixedReachable d K e ⊆ ⋃ s : SlimReverseShape d K,
      SlimReverseBlocks.witnessTargets s hd (Real.sqrt (21 / 2 * e)) (Real.sqrt (21 / 2 * e)) := by
  rw [mixedReachable_eq_pureReachable]
  exact swapNeighborhood_inter_pureReachable_subset_slimWitnessTargets hd he0 he

end NLQCLean
