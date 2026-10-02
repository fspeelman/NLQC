import NLQCLean.Approx.PVMWitnessCoordinates
import NLQCLean.Approx.PVMPolynomialDegree
import NLQCLean.Approx.PolynomialWitnessFamily

/-!
# Exact fixed-format polynomial PVM witness domain

Seven equations and one inequality encode every
individual flag normalization, four isometries, zero padding and leakage.
The raw overlap has degree six. The blockwise cubic extension and its ambient
Jacobian estimates are separate subsequent obligations.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

namespace PVMReverseBlocks

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

theorem polynomialDegree_rawOverlap :
    MatrixPolynomialDegreeLE 6 (fun x => overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) := by
  have h := (PolynomialDegreeLE.linear (decodeCoordinates s hd hfloor hP)).rescale.overlap
  simpa only [mul_one] using h

theorem polynomialDegree_coordinateRawOverlap (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE 6 (fun x => coordinateRawOverlap s hd hfloor hP x j) :=
  polynomialDegree_overlapOutputCoordinates (polynomialDegree_rawOverlap s hd hfloor hP) j

theorem polynomialDegree_rawLeakage : RealPolynomialDegreeLE 12
    (fun x => (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))‖ ^ 2) :=
  (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2)).sub
    (polynomialDegree_rawOverlap s hd hfloor hP).frobNorm_sq

/-- The raw overlap polynomial, with the prescribed degree bound. -/
noncomputable def coordinateRawOverlapPolynomial :
    BoundedPolynomialMap (P) (2 * d ^ 4) where
  coordinates j := Classical.choose (polynomialDegree_coordinateRawOverlap s hd hfloor hP j)
  degree_le j := (Classical.choose_spec (polynomialDegree_coordinateRawOverlap s hd hfloor hP j)).1.trans (by decide)

theorem coordinateRawOverlapPolynomial_eval (x : RealEuclidean P) :
    (coordinateRawOverlapPolynomial s hd hfloor hP).eval x = coordinateRawOverlap s hd hfloor hP x := by
  ext j
  exact (Classical.choose_spec (polynomialDegree_coordinateRawOverlap s hd hfloor hP j)).2 x

/-- One sum of squares enforces every dummy coordinate to be zero. -/
noncomputable def paddingDefect (x : RealEuclidean P) : ℝ := by
  classical
  exact ∑ j, if j ∈ Set.range (coordinateEmbedding s hd hfloor hP) then 0 else x j ^ 2

theorem paddingDefect_eq_zero_iff (x : RealEuclidean P) :
    paddingDefect s hd hfloor hP x = 0 ↔ ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor hP), x j = 0 := by
  classical
  rw [paddingDefect, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by split <;> positivity)]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h j hj
    simpa only [ite_eq_right hj, sq_eq_zero_iff] using h j
  · intro h j
    by_cases hj : j ∈ Set.range (coordinateEmbedding s hd hfloor hP)
    · simp only [ite_eq_left hj]
    · simp only [ite_eq_right hj, h j hj, zero_pow (by decide : 2 ≠ 0)]

theorem polynomialDegree_paddingDefect : RealPolynomialDegreeLE 2 (paddingDefect s hd hfloor hP) := by
  classical
  apply RealPolynomialDegreeLE.sum Finset.univ
  intro j _
  by_cases hj : j ∈ Set.range (coordinateEmbedding s hd hfloor hP)
  · simpa only [ite_eq_left hj] using (RealPolynomialDegreeLE.const 0).mono (by decide : 0 ≤ 2)
  · simpa only [ite_eq_right hj] using (RealPolynomialDegreeLE.coord j).sq

/-- One resource sphere, one sum of individual garbage sphere defects,
four Gram defects, and one padding equation. -/
noncomputable def witnessEquations (i : Fin 7) (x : RealEuclidean P) : ℝ :=
  let z := decodeCoordinates s hd hfloor hP x
  ![sphereDefect z.1, pvmGarbageDefect (d ^ 2 : ℝ) z.2.1,
    gramDefectSq (d * s.1.r : ℝ) z.2.2.1, gramDefectSq (d * s.1.r : ℝ) z.2.2.2.1,
    gramDefectSq (s.supportSize : ℝ) z.2.2.2.2.1, gramDefectSq (s.supportSize : ℝ) z.2.2.2.2.2,
    paddingDefect s hd hfloor hP x] i

theorem polynomialDegree_witnessEquations (i : Fin 7) : RealPolynomialDegreeLE 12 (witnessEquations s hd hfloor hP i) := by
  have hb := PolynomialDegreeLE.linear (decodeCoordinates s hd hfloor hP)
  have hη := (polynomialDegree_sqNorm hb.1).sub (RealPolynomialDegreeLE.const 1)
  have hg := polynomialDegree_pvmGarbageDefect hb.2.1 (d ^ 2 : ℝ)
  fin_cases i
  · exact hη.mono (by decide)
  · exact hg.mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.2.1 _).mono (by decide)
  · exact (polynomialDegree_gramDefectSq hb.2.2.2.2.2 _).mono (by decide)
  · exact (polynomialDegree_paddingDefect s hd hfloor hP).mono (by decide)

set_option maxHeartbeats 1000000 in
theorem witnessEquations_zero_iff (x : RealEuclidean P) :
    (∀ i, witnessEquations s hd hfloor hP i x = 0) ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x)) ∧
        ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor hP), x j = 0 := by
  have hdr : 0 ≤ (d * s.1.r : ℝ) := by positivity
  have hS : 0 ≤ (s.supportSize : ℝ) := by positivity
  have hD : 0 ≤ (d ^ 2 : ℝ) := by positivity
  simp [witnessEquations, Fin.forall_fin_succ, sphereDefect_eq_zero_iff,
    gramDefectSq_eq_zero_iff _ hdr, gramDefectSq_eq_zero_iff _ hS, pvmGarbageDefect_eq_zero_iff _ hD,
    paddingDefect_eq_zero_iff, IsValid, rescaleBlocks, and_assoc]

/-- The sole weak inequality, oriented as a nonnegative polynomial. -/
noncomputable def witnessInequality (δ : ℝ) (x : RealEuclidean P) : ℝ :=
  (d : ℝ) ^ 2 * δ ^ 2 - ((d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))‖ ^ 2)

theorem polynomialDegree_witnessInequality (δ : ℝ) : RealPolynomialDegreeLE 12 (witnessInequality s hd hfloor hP δ) :=
  (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2 * δ ^ 2)).sub (polynomialDegree_rawLeakage s hd hfloor hP)

/-- The eight-constraint source in the fixed polynomial format. -/
noncomputable def witnessFormat (δ : ℝ) : PolynomialBasicClosedFormat (P) where
  numEquations := 7
  numInequalities := 1
  constraint_count := by decide
  equations i := Classical.choose (polynomialDegree_witnessEquations s hd hfloor hP i)
  inequalities _ := Classical.choose (polynomialDegree_witnessInequality s hd hfloor hP δ)
  equations_degree i := (Classical.choose_spec (polynomialDegree_witnessEquations s hd hfloor hP i)).1.trans (by decide)
  inequalities_degree _ := (Classical.choose_spec (polynomialDegree_witnessInequality s hd hfloor hP δ)).1.trans (by decide)

theorem witnessFormat_constraint_count (δ : ℝ) :
    (witnessFormat s hd hfloor hP δ).numEquations +
      (witnessFormat s hd hfloor hP δ).numInequalities = 8 := rfl

theorem witnessFormat_equations_degree_le (δ : ℝ) (i : Fin 7) :
    ((witnessFormat s hd hfloor hP δ).equations i).totalDegree ≤ 12 :=
  (Classical.choose_spec (polynomialDegree_witnessEquations s hd hfloor hP i)).1

theorem witnessFormat_inequalities_degree_le (δ : ℝ) (i : Fin 1) :
    ((witnessFormat s hd hfloor hP δ).inequalities i).totalDegree ≤ 12 :=
  (Classical.choose_spec (polynomialDegree_witnessInequality s hd hfloor hP δ)).1

theorem witnessFormat_equation_eval (δ : ℝ) (i : Fin 7) (x : RealEuclidean P) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd hfloor hP δ).equations i) = witnessEquations s hd hfloor hP i x :=
  (Classical.choose_spec (polynomialDegree_witnessEquations s hd hfloor hP i)).2 x

theorem witnessFormat_inequality_eval (δ : ℝ) (i : Fin 1) (x : RealEuclidean P) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd hfloor hP δ).inequalities i) = witnessInequality s hd hfloor hP δ x :=
  (Classical.choose_spec (polynomialDegree_witnessInequality s hd hfloor hP δ)).2 x

theorem mem_witnessFormat_source_iff (δ : ℝ) (x : RealEuclidean P) :
    x ∈ (witnessFormat s hd hfloor hP δ).source ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x)) ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd hfloor hP), x j = 0) ∧
      (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd hfloor hP x))‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2 := by
  change ((∀ i : Fin 7, MvPolynomial.eval (fun j => x j) ((witnessFormat s hd hfloor hP δ).equations i) = 0) ∧
    (∀ i : Fin 1, 0 ≤ MvPolynomial.eval (fun j => x j) ((witnessFormat s hd hfloor hP δ).inequalities i))) ↔ _
  constructor
  · rintro ⟨he, hi⟩
    have he' : ∀ i, witnessEquations s hd hfloor hP i x = 0 := by
      intro i
      rw [← witnessFormat_equation_eval s hd hfloor hP δ i x]
      exact he i
    obtain ⟨hx, hpad⟩ := (witnessEquations_zero_iff s hd hfloor hP x).mp he'
    have hb := hi 0
    rw [witnessFormat_inequality_eval] at hb
    exact ⟨hx, hpad, sub_nonneg.mp hb⟩
  · rintro ⟨hx, hpad, hdef⟩
    refine ⟨?_, ?_⟩
    · intro i
      rw [witnessFormat_equation_eval]
      exact (witnessEquations_zero_iff s hd hfloor hP x).mpr ⟨hx, hpad⟩ i
    · intro i
      rw [witnessFormat_inequality_eval]
      exact sub_nonneg.mpr hdef

theorem norm_mem_witnessFormat_source (δ : ℝ) {x : RealEuclidean P}
    (hx : x ∈ (witnessFormat s hd hfloor hP δ).source) : ‖x‖ = Real.sqrt 6 := by
  obtain ⟨hv, hp, _⟩ := (mem_witnessFormat_source_iff s hd hfloor hP δ x).mp hx
  exact norm_padded_valid_eq_sqrt_six s hd hfloor hP hv hp

theorem isCompact_witnessFormat_source (δ : ℝ) : IsCompact (witnessFormat s hd hfloor hP δ).source := by
  apply Metric.isCompact_of_isClosed_isBounded (witnessFormat s hd hfloor hP δ).isClosed_source
  exact (isBounded_iff_forall_norm_le).mpr ⟨Real.sqrt 6, fun x hx => (norm_mem_witnessFormat_source s hd hfloor hP δ hx).le⟩

theorem witnessFormat_source_subset_ball (δ : ℝ) :
    (witnessFormat s hd hfloor hP δ).source ⊆ Metric.closedBall 0 3 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, norm_mem_witnessFormat_source s hd hfloor hP δ hx]
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ)), Real.sqrt_nonneg (6 : ℝ)]

/-- Every valid raw witness satisfying the leakage bound lies in this exact
polynomial family after normalization; the polynomial image is unchanged. -/
theorem exists_mem_witnessFormat_source (δ : ℝ) {x : PVMReverseBlocks s} (hx : IsValid x)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ y ∈ (witnessFormat s hd hfloor hP δ).source,
      (coordinateRawOverlapPolynomial s hd hfloor hP).eval y = overlapOutputCoordinates d (overlap x) := by
  obtain ⟨y, hy, hp, _, hraw⟩ := exists_normalized_coordinate_witness s hd hfloor hP hx
  have hv : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP y)) := hy.symm ▸ hx
  have hs : y ∈ (witnessFormat s hd hfloor hP δ).source :=
    (mem_witnessFormat_source_iff s hd hfloor hP δ y).mpr ⟨hv, hp, by rw [hy]; exact hdef⟩
  refine ⟨y, hs, ?_⟩
  rw [coordinateRawOverlapPolynomial_eval]
  exact hraw

/-- A valid physical reverse witness supplies a point of the exact polynomial
source with the same overlap error in real Euclidean output coordinates. -/
theorem exists_mem_witnessFormat_source_approximation (δ : ℝ)
    {x : PVMReverseBlocks s} (hx : IsValid x)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2)
    (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hclose : ‖overlap x - T‖ ≤ (d : ℝ) * δ) :
    ∃ y ∈ (witnessFormat s hd hfloor hP δ).source,
      ‖(coordinateRawOverlapPolynomial s hd hfloor hP).eval y - overlapOutputCoordinates d T‖ ≤
        (d : ℝ) * δ := by
  obtain ⟨y, hy, he⟩ := exists_mem_witnessFormat_source s hd hfloor hP δ hx hdef
  refine ⟨y, hy, ?_⟩
  rw [he, ← map_sub, norm_overlapOutputCoordinates]
  exact hclose

end PVMReverseBlocks
end NLQCLean
