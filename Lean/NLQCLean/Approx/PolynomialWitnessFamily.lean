import NLQCLean.Approx.WitnessPolynomialDegree
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The exact basic closed polynomial witness source

Seven polynomial equations encode two unit vectors, four normalized
isometries, and zero padding; one inequality bounds scalar leakage. The
source is exactly the intended witness set, compact with radius sqrt(6).
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem RealPolynomialDegreeLE.continuous {a D : ℕ} {f : RealEuclidean a → ℝ}
    (hf : RealPolynomialDegreeLE D f) : Continuous f := by
  obtain ⟨p, _, he⟩ := hf
  exact (p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin a => ℝ))).congr he

theorem PolynomialBasicClosedFormat.isClosed_source {a : ℕ} (F : PolynomialBasicClosedFormat a) :
    IsClosed F.source := by
  have hc (p : MvPolynomial (Fin a) ℝ) :
      Continuous (fun x : RealEuclidean a => MvPolynomial.eval (fun i => x i) p) :=
    p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin a => ℝ))
  unfold PolynomialBasicClosedFormat.source
  rw [Set.ofPred_and]
  simp only [Set.ofPred_forall]
  exact (isClosed_iInter (fun i => isClosed_eq (hc (F.equations i)) continuous_const)).inter
    (isClosed_iInter (fun i => isClosed_le continuous_const (hc (F.inequalities i))))

noncomputable def sphereDefect {ι : Type*} [Fintype ι] (z : ι → ℂ) : ℝ := sqNorm z - 1

theorem sphereDefect_eq_zero_iff {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    sphereDefect z = 0 ↔ IsUnitVector z := by
  simp only [sphereDefect, sub_eq_zero, IsUnitVector, sqNorm]

noncomputable def gramDefectSq {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (n : ℝ) (W : Matrix m k ℂ) : ℝ :=
  ‖n • (Wᴴ * W) - 1‖ ^ 2

theorem gramDefectSq_eq_zero_iff {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (n : ℝ) (hn : 0 ≤ n) (W : Matrix m k ℂ) :
    gramDefectSq n W = 0 ↔ IsIsometry (Real.sqrt n • W) := by
  rw [gramDefectSq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, isIsometry_sqrt_smul_iff n hn]

theorem polynomialDegree_gramDefectSq {a D : ℕ} {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] {f : RealEuclidean a → Matrix m k ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (n : ℝ) :
    RealPolynomialDegreeLE (4 * D) (fun x => gramDefectSq n (f x)) := by
  have h := (((hf.conjTranspose.mul hf).real_smul n).sub (MatrixPolynomialDegreeLE.const 1)).frobNorm_sq
  exact h.mono (by omega)

namespace ReverseBlocks

variable {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d)

/-- One sum of squares enforces every dummy coordinate to be zero. -/
noncomputable def paddingDefect (x : RealEuclidean (witnessCoordinateBudget d K)) : ℝ := by
  classical
  exact ∑ j, if j ∈ Set.range (coordinateEmbedding s hd) then 0 else x j ^ 2

theorem paddingDefect_eq_zero_iff (x : RealEuclidean (witnessCoordinateBudget d K)) :
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
noncomputable def witnessEquations (i : Fin 7) (x : RealEuclidean (witnessCoordinateBudget d K)) : ℝ :=
  let z := decodeCoordinates s hd x
  ![sphereDefect z.1, sphereDefect z.2.1,
    gramDefectSq (d * s.r : ℝ) z.2.2.1, gramDefectSq (d * s.r : ℝ) z.2.2.2.1,
    gramDefectSq (d * K : ℝ) z.2.2.2.2.1, gramDefectSq (d * K : ℝ) z.2.2.2.2.2,
    paddingDefect s hd x] i

theorem polynomialDegree_witnessEquations (i : Fin 7) : RealPolynomialDegreeLE 12 (witnessEquations s hd i) := by
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

theorem witnessEquations_zero_iff (x : RealEuclidean (witnessCoordinateBudget d K)) :
    (∀ i, witnessEquations s hd i x = 0) ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd x)) ∧
        ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0 := by
  have hdr : 0 ≤ (d * s.r : ℝ) := by positivity
  have hdK : 0 ≤ (d * K : ℝ) := by positivity
  simp [witnessEquations, Fin.forall_fin_succ, sphereDefect_eq_zero_iff,
    gramDefectSq_eq_zero_iff _ hdr, gramDefectSq_eq_zero_iff _ hdK,
    paddingDefect_eq_zero_iff, IsValid, rescaleBlocks, and_assoc]

/-- The sole weak inequality, oriented as a nonnegative polynomial. -/
noncomputable def witnessInequality (δ : ℝ) (x : RealEuclidean (witnessCoordinateBudget d K)) : ℝ :=
  (d : ℝ) ^ 2 * δ ^ 2 - ((d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2)

theorem polynomialDegree_witnessInequality (δ : ℝ) : RealPolynomialDegreeLE 12 (witnessInequality s hd δ) :=
  (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2 * δ ^ 2)).sub (polynomialDegree_rawLeakage s hd)

/-- The eight-constraint source in the fixed polynomial format. -/
noncomputable def witnessFormat (δ : ℝ) : PolynomialBasicClosedFormat (witnessCoordinateBudget d K) where
  numEquations := 7
  numInequalities := 1
  constraint_count := by decide
  equations i := Classical.choose (polynomialDegree_witnessEquations s hd i)
  inequalities _ := Classical.choose (polynomialDegree_witnessInequality s hd δ)
  equations_degree i := (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).1.trans (by decide)
  inequalities_degree _ := (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).1.trans (by decide)

theorem witnessFormat_equation_eval (δ : ℝ) (i : Fin 7) (x : RealEuclidean (witnessCoordinateBudget d K)) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).equations i) = witnessEquations s hd i x :=
  (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).2 x

theorem witnessFormat_inequality_eval (δ : ℝ) (i : Fin 1) (x : RealEuclidean (witnessCoordinateBudget d K)) :
    MvPolynomial.eval (fun j => x j) ((witnessFormat s hd δ).inequalities i) = witnessInequality s hd δ x :=
  (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).2 x

theorem mem_witnessFormat_source_iff (δ : ℝ) (x : RealEuclidean (witnessCoordinateBudget d K)) :
    x ∈ (witnessFormat s hd δ).source ↔
      IsValid (rescaleBlocks (decodeCoordinates s hd x)) ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) ∧
      (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2 := by
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

theorem norm_mem_witnessFormat_source (δ : ℝ) {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd δ).source) : ‖x‖ = Real.sqrt 6 := by
  obtain ⟨hv, hp, _⟩ := (mem_witnessFormat_source_iff s hd δ x).mp hx
  exact norm_padded_valid_eq_sqrt_six s hd hv hp

theorem isCompact_witnessFormat_source (δ : ℝ) : IsCompact (witnessFormat s hd δ).source := by
  apply Metric.isCompact_of_isClosed_isBounded (witnessFormat s hd δ).isClosed_source
  exact (isBounded_iff_forall_norm_le).mpr ⟨Real.sqrt 6, fun x hx => (norm_mem_witnessFormat_source s hd δ hx).le⟩

theorem witnessFormat_source_subset_ball (δ : ℝ) :
    (witnessFormat s hd δ).source ⊆ Metric.closedBall 0 3 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, norm_mem_witnessFormat_source s hd δ hx]
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ)), Real.sqrt_nonneg (6 : ℝ)]

/-- Every valid raw witness satisfying the leakage bound lies in this exact
polynomial family after normalization; the polynomial image is unchanged. -/
theorem exists_mem_witnessFormat_source (δ : ℝ) {x : ReverseBlocks s} (hx : IsValid x)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ y ∈ (witnessFormat s hd δ).source,
      (coordinateOverlapPolynomial s hd).eval y = overlapOutputCoordinates d (overlap x) := by
  obtain ⟨y, hy, hp, _, hraw⟩ := exists_normalized_coordinate_witness s hd hx
  have hv : IsValid (rescaleBlocks (decodeCoordinates s hd y)) := hy.symm ▸ hx
  have hs : y ∈ (witnessFormat s hd δ).source :=
    (mem_witnessFormat_source_iff s hd δ y).mpr ⟨hv, hp, by rw [hy]; exact hdef⟩
  refine ⟨y, hs, ?_⟩
  rw [coordinateOverlapPolynomial_eval, coordinateOverlap_eq_raw s hd hv]
  exact hraw

/-- Euclidean rank/error bounds for the evaluated polynomial map on
the exact basic closed source.  -/
theorem witnessFormat_ambient_rank_error (hd2 : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean (witnessCoordinateBudget d K)} (hx : x ∈ (witnessFormat s hd δ).source) :
    ∃ T R : RealEuclidean (witnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlapPolynomial s hd).eval x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 4 * d ^ 2 - 3 ∧
      ‖fderiv ℝ (coordinateOverlapPolynomial s hd).eval x‖ ≤ (witnessCoordinateBudget d K : ℝ) ∧
      ‖R‖ ≤ δ * witnessCoordinateBudget d K := by
  obtain ⟨hv, _, hdef⟩ := (mem_witnessFormat_source_iff s hd δ x).mp hx
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact exists_coordinateOverlap_rank_error_decomposition s hd hd2 hv hδ hdef

end ReverseBlocks
end NLQCLean
