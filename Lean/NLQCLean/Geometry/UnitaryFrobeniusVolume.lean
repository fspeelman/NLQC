import NLQCLean.Geometry.ScaledUnitaryNormalVolume
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The intrinsic Frobenius volume of the unitary group (`lem:normal-volume`)

`Vol_F U(n)` is the `N`-dimensional Euclidean Hausdorff measure `μHE[N]`, `N = |n|²`, of the
unitary group in Frobenius coordinates. With `D = |n|`:

* `(√D/256)^N ω_N ≤ Vol_F U(n)`;
* `(1/1024)^N ω_N t^N Vol_F U(n) μ(S) ≤ Vol_{2N}(U_t(S))` for Borel `S` and `0 < t ≤ √D/64`.

On the operator-small skew sector the Cayley map satisfies
`½‖A − B‖ ≤ ‖c(A) − c(B)‖ ≤ 8‖A − B‖`, by `c(A) − c(B) = 2(1−A)⁻¹(A−B)(1−B)⁻¹`. The pulled-back
Hausdorff measure is left invariant and finite, hence `Vol_F U(n)` times Haar measure;
comparing it with the operator-normal chart on one Cayley cap gives the tube inequality.
-/

namespace NLQCLean

open Matrix MeasureTheory Metric
open scoped Matrix.Norms.Frobenius ENNReal NNReal

section CayleyLipschitz

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem frobNorm_inv_one_sub_mul_le {A : Matrix n n ℂ} (hA : opNorm A ≤ 1 / 2)
    (X : Matrix n n ℂ) : ‖(1 - A)⁻¹ * X‖ ≤ 2 * ‖X‖ := by
  have hi := isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num))
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hi
  set Y := (1 - A)⁻¹ * X with hY
  have hXY : (1 - A) * Y = X := by
    rw [hY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hsplit : Y = X + A * Y := by rw [← hXY]; noncomm_ring
  have hAY : ‖A * Y‖ ≤ 1 / 2 * ‖Y‖ :=
    (frobNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h := norm_add_le X (A * Y)
  rw [← hsplit] at h
  linarith

theorem frobNorm_mul_inv_one_sub_le {A : Matrix n n ℂ} (hA : opNorm A ≤ 1 / 2)
    (X : Matrix n n ℂ) : ‖X * (1 - A)⁻¹‖ ≤ 2 * ‖X‖ := by
  have hi := isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num))
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hi
  set Y := X * (1 - A)⁻¹ with hY
  have hXY : Y * (1 - A) = X := by
    rw [hY, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  have hsplit : Y = X + Y * A := by rw [← hXY]; noncomm_ring
  have hYA : ‖Y * A‖ ≤ ‖Y‖ * (1 / 2) :=
    (frobNorm_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  have h := norm_add_le X (Y * A)
  rw [← hsplit] at h
  linarith

/-- The Cayley difference identity `c(A) − c(B) = 2(1−A)⁻¹(A−B)(1−B)⁻¹`. -/
theorem matrixCayley_sub {A B : Matrix n n ℂ} (hA : IsUnit (1 - A)) (hB : IsUnit (1 - B)) :
    matrixCayley A - matrixCayley B = (2 : ℝ) • ((1 - A)⁻¹ * (A - B) * (1 - B)⁻¹) := by
  have hdA := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hdB := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hiA : (1 - A)⁻¹ * (1 - A) = 1 := Matrix.nonsing_inv_mul _ hdA
  have hiB : (1 - B) * (1 - B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdB
  have hmid : (1 - A)⁻¹ * (A - B) * (1 - B)⁻¹ = (1 - A)⁻¹ - (1 - B)⁻¹ := by
    calc (1 - A)⁻¹ * (A - B) * (1 - B)⁻¹
        = (1 - A)⁻¹ * ((1 - B) * (1 - B)⁻¹) - ((1 - A)⁻¹ * (1 - A)) * (1 - B)⁻¹ := by
          noncomm_ring
      _ = _ := by rw [hiA, hiB]; noncomm_ring
  rw [matrixCayley_eq_two_inv_sub_one A hA, matrixCayley_eq_two_inv_sub_one B hB, hmid,
    smul_sub]
  abel

/-- The Cayley map is `8`-Lipschitz on the operator half-ball, in Frobenius norm. -/
theorem norm_matrixCayley_sub_le {A B : Matrix n n ℂ} (hA : opNorm A ≤ 1 / 2)
    (hB : opNorm B ≤ 1 / 2) : ‖matrixCayley A - matrixCayley B‖ ≤ 8 * ‖A - B‖ := by
  rw [matrixCayley_sub (isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num)))
    (isUnit_one_sub_of_opNorm_lt_one (hB.trans_lt (by norm_num))), norm_smul]
  have h1 := frobNorm_mul_inv_one_sub_le hB ((1 - A)⁻¹ * (A - B))
  have h2 := frobNorm_inv_one_sub_mul_le hA (A - B)
  rw [Real.norm_two]
  nlinarith [norm_nonneg ((1 - A)⁻¹ * (A - B) * (1 - B)⁻¹)]

/-- Conversely the Cayley map expands Frobenius distances by at least `½` there. -/
theorem norm_sub_le_two_mul_matrixCayley_sub {A B : Matrix n n ℂ} (hA : opNorm A ≤ 1 / 2)
    (hB : opNorm B ≤ 1 / 2) : ‖A - B‖ ≤ 2 * ‖matrixCayley A - matrixCayley B‖ := by
  have hiA := isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num))
  have hiB := isUnit_one_sub_of_opNorm_lt_one (hB.trans_lt (by norm_num))
  have hdA := (Matrix.isUnit_iff_isUnit_det _).mp hiA
  have hdB := (Matrix.isUnit_iff_isUnit_det _).mp hiB
  set M := (1 - A)⁻¹ * (A - B) * (1 - B)⁻¹ with hM
  have hback : A - B = (1 - A) * M * (1 - B) := by
    have e1 : (1 - A) * (1 - A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdA
    have e2 : (1 - B)⁻¹ * (1 - B) = 1 := Matrix.nonsing_inv_mul _ hdB
    calc A - B = ((1 - A) * (1 - A)⁻¹) * (A - B) * ((1 - B)⁻¹ * (1 - B)) := by
          rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (1 - A) * M * (1 - B) := by rw [hM]; simp only [Matrix.mul_assoc]
  have h2A := opNorm_one_sub_le_two (hA.trans (by norm_num))
  have h2B := opNorm_one_sub_le_two (hB.trans (by norm_num))
  have hle : ‖A - B‖ ≤ 4 * ‖M‖ := by
    rw [hback, Matrix.mul_assoc]
    calc ‖(1 - A) * (M * (1 - B))‖ ≤ opNorm (1 - A) * ‖M * (1 - B)‖ := frobNorm_mul_le _ _
      _ ≤ 2 * (‖M‖ * 2) := by
          gcongr
          exact (frobNorm_mul_le' _ _).trans (mul_le_mul_of_nonneg_left h2B (norm_nonneg _))
      _ = 4 * ‖M‖ := by ring
  rw [matrixCayley_sub hiA hiB, norm_smul, Real.norm_two]
  linarith

end CayleyLipschitz

section Hausdorff

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A `K`-Lipschitz map multiplies `μHE[d]` by at most `K^d`. -/
theorem euclideanHausdorffMeasure_image_le_of_lipschitzOnWith {K : ℝ≥0} {f : X → Y} {s : Set X}
    (h : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  have h1 := h.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)
  rw [ENNReal.rpow_natCast] at h1
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  calc _ ≤ _ * ((K : ℝ≥0∞) ^ d * μH[d] s) := by gcongr
    _ = _ := by ring

/-- A map that expands distances by at least `1/K` on `s` multiplies `μHE[d]` by at least
`K^(-d)`. -/
theorem euclideanHausdorffMeasure_le_of_expand [Nonempty X] {K : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : ∀ a ∈ s, ∀ b ∈ s, dist a b ≤ K * dist (f a) (f b)) (d : ℕ) :
    μHE[d] s ≤ (K : ℝ≥0∞) ^ d * μHE[d] (f '' s) := by
  have hinj : Set.InjOn f s := fun a ha b hb hab => by
    have h := hf a ha b hb
    rw [hab, dist_self, mul_zero] at h
    exact dist_le_zero.mp h
  have hL : LipschitzOnWith K (Function.invFunOn f s) (f '' s) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn hb]
    exact hf a ha b hb
  have h := euclideanHausdorffMeasure_image_le_of_lipschitzOnWith hL d
  rwa [hinj.invFunOn_image le_rfl] at h

end Hausdorff

section Volume

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Frobenius coordinates of a unitary. -/
noncomputable def unitaryFrobeniusEmbedding (U : Matrix.unitaryGroup n ℂ) :
    EuclideanSpace ℝ ((n × n) × Fin 2) :=
  matrixFrobeniusCoordinates n n (U : Matrix n n ℂ)

theorem continuous_unitaryFrobeniusEmbedding : Continuous (unitaryFrobeniusEmbedding n) :=
  (matrixFrobeniusCoordinates n n).continuous.comp continuous_subtype_val

theorem measurableEmbedding_unitaryFrobeniusEmbedding :
    MeasurableEmbedding (unitaryFrobeniusEmbedding n) :=
  ((continuous_unitaryFrobeniusEmbedding n).isClosedEmbedding
    ((matrixFrobeniusCoordinates n n).injective.comp Subtype.val_injective)).measurableEmbedding

/-- **`Vol_F U(n)`**: the intrinsic `|n|²`-dimensional volume of the unitary group in the
Frobenius norm, the Euclidean Hausdorff measure of its image in Frobenius coordinates. -/
noncomputable def unitaryFrobeniusVolume : ℝ≥0∞ :=
  μHE[Fintype.card n ^ 2] (Set.range (unitaryFrobeniusEmbedding n))

/-- The intrinsic Frobenius measure on the unitary group. -/
noncomputable def unitaryFrobeniusMeasure : Measure (Matrix.unitaryGroup n ℂ) :=
  (μHE[Fintype.card n ^ 2] : Measure (EuclideanSpace ℝ ((n × n) × Fin 2))).comap
    (unitaryFrobeniusEmbedding n)

theorem unitaryFrobeniusMeasure_apply (S : Set (Matrix.unitaryGroup n ℂ)) :
    unitaryFrobeniusMeasure n S =
      μHE[Fintype.card n ^ 2] (unitaryFrobeniusEmbedding n '' S) :=
  (measurableEmbedding_unitaryFrobeniusEmbedding n).comap_apply _ S

theorem unitaryFrobeniusMeasure_univ :
    unitaryFrobeniusMeasure n Set.univ = unitaryFrobeniusVolume n := by
  rw [unitaryFrobeniusMeasure_apply, Set.image_univ]
  rfl

variable {n}

theorem unitaryFrobeniusEmbedding_mul (U V : Matrix.unitaryGroup n ℂ) :
    unitaryFrobeniusEmbedding n (U * V) =
      unitaryLeftEuclidean U (unitaryFrobeniusEmbedding n V) := by
  rw [unitaryFrobeniusEmbedding, unitaryFrobeniusEmbedding, unitaryLeftEuclidean_coordinates]
  rfl

instance isMulLeftInvariant_unitaryFrobeniusMeasure :
    (unitaryFrobeniusMeasure n).IsMulLeftInvariant := by
  apply (forall_measure_preimage_mul_iff _).mp
  intro U S _
  rw [unitaryFrobeniusMeasure_apply, unitaryFrobeniusMeasure_apply]
  have himage : unitaryFrobeniusEmbedding n '' ((fun V => U * V) ⁻¹' S) =
      (unitaryLeftEuclidean U).symm '' (unitaryFrobeniusEmbedding n '' S) := by
    ext y
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact ⟨unitaryFrobeniusEmbedding n (U * V), ⟨_, hV, rfl⟩, by
        rw [unitaryFrobeniusEmbedding_mul, LinearIsometryEquiv.symm_apply_apply]⟩
    · rintro ⟨_, ⟨W, hW, rfl⟩, rfl⟩
      refine ⟨U⁻¹ * W, ?_, ?_⟩
      · show U * (U⁻¹ * W) ∈ S
        rwa [mul_inv_cancel_left]
      · rw [eq_comm, LinearIsometryEquiv.symm_apply_eq, ← unitaryFrobeniusEmbedding_mul,
          mul_inv_cancel_left]
  rw [himage, (unitaryLeftEuclidean U).symm.isometry.euclideanHausdorffMeasure_image]

/-! ### The Cayley cap -/

/-- The closed operator-small skew sector of Frobenius radius `R`. -/
def closedSkewSector (R : ℝ) : Set (SkewFrobenius n) :=
  {A | opNorm (A : Matrix n n ℂ) ≤ 1 / 2 ∧ ‖A‖ ≤ R}

/-- The Cayley map of a skew-Hermitian matrix, in Frobenius coordinates. -/
noncomputable def skewCayleyEuclidean (A : SkewFrobenius n) :
    EuclideanSpace ℝ ((n × n) × Fin 2) :=
  matrixFrobeniusCoordinates n n (matrixCayley (A : Matrix n n ℂ))

omit [DecidableEq n] in
theorem skew_adjoint (A : SkewFrobenius n) : (A : Matrix n n ℂ)ᴴ = -(A : Matrix n n ℂ) :=
  skewAdjoint.mem_iff.mp A.2

theorem dist_skewCayleyEuclidean (A B : SkewFrobenius n) :
    dist (skewCayleyEuclidean A) (skewCayleyEuclidean B) =
      ‖matrixCayley (A : Matrix n n ℂ) - matrixCayley (B : Matrix n n ℂ)‖ := by
  rw [dist_eq_norm, skewCayleyEuclidean, skewCayleyEuclidean, ← map_sub,
    LinearIsometryEquiv.norm_map]

theorem dist_skewFrobenius (A B : SkewFrobenius n) :
    dist A B = ‖(A : Matrix n n ℂ) - (B : Matrix n n ℂ)‖ := by
  rw [dist_eq_norm]
  rfl

theorem lipschitzOnWith_skewCayleyEuclidean (R : ℝ) :
    LipschitzOnWith 8 skewCayleyEuclidean (closedSkewSector (n := n) R) :=
  LipschitzOnWith.of_dist_le_mul fun A hA B hB => by
    rw [dist_skewCayleyEuclidean, dist_skewFrobenius]
    exact_mod_cast norm_matrixCayley_sub_le hA.1 hB.1

theorem dist_le_two_mul_dist_skewCayleyEuclidean (R : ℝ) :
    ∀ A ∈ closedSkewSector (n := n) R, ∀ B ∈ closedSkewSector (n := n) R,
      dist A B ≤ ((2 : ℝ≥0) : ℝ) * dist (skewCayleyEuclidean A) (skewCayleyEuclidean B) :=
  fun A hA B hB => by
    rw [dist_skewCayleyEuclidean, dist_skewFrobenius]
    exact_mod_cast norm_sub_le_two_mul_matrixCayley_sub hA.1 hB.1

theorem isCompact_closedSkewSector (R : ℝ) : IsCompact (closedSkewSector (n := n) R) := by
  have hc : IsClosed (closedSkewSector (n := n) R) :=
    (isClosed_le ((continuous_opNorm n n).comp continuous_subtype_val) continuous_const).inter
      (isClosed_le continuous_norm continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hc ((isBounded_closedBall (x := 0) (r := R)).subset ?_)
  intro A hA
  rw [mem_closedBall, dist_zero_right]
  exact hA.2

theorem continuousOn_skewCayleyEuclidean (R : ℝ) :
    ContinuousOn skewCayleyEuclidean (closedSkewSector (n := n) R) := by
  intro A hA
  have hi := isUnit_one_sub_of_opNorm_lt_one (hA.1.trans_lt (by norm_num))
  have hcont : ContinuousAt (fun B : SkewFrobenius n => matrixCayley (B : Matrix n n ℂ)) A :=
    (hasFDerivAt_matrixCayley _ hi).continuousAt.comp continuous_subtype_val.continuousAt
  exact ((matrixFrobeniusCoordinates n n).continuous.continuousAt.comp hcont).continuousWithinAt

theorem skewCayleyEuclidean_mem_range (A : SkewFrobenius n) (hA : opNorm (A : Matrix n n ℂ) ≤ 1 / 2) :
    skewCayleyEuclidean A ∈ Set.range (unitaryFrobeniusEmbedding n) := by
  have hi := isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num))
  exact ⟨⟨matrixCayley (A : Matrix n n ℂ),
    Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_matrixCayley _ (skew_adjoint A) hi)⟩, rfl⟩

/-- The unitaries `c(A)` with `A` in the closed skew sector. -/
def cayleyCap (R : ℝ) : Set (Matrix.unitaryGroup n ℂ) :=
  unitaryFrobeniusEmbedding n ⁻¹' (skewCayleyEuclidean '' closedSkewSector R)

theorem image_cayleyCap (R : ℝ) :
    unitaryFrobeniusEmbedding n '' cayleyCap R = skewCayleyEuclidean '' closedSkewSector R :=
  Set.image_preimage_eq_of_subset (by
    rintro _ ⟨A, hA, rfl⟩
    exact skewCayleyEuclidean_mem_range A hA.1)

theorem measurableSet_cayleyCap (R : ℝ) : MeasurableSet (cayleyCap (n := n) R) :=
  ((isCompact_closedSkewSector R).image_of_continuousOn
    (continuousOn_skewCayleyEuclidean R)).isClosed.measurableSet.preimage
      (continuous_unitaryFrobeniusEmbedding n).measurable

omit [DecidableEq n] in
theorem finrank_skewFrobenius : Module.finrank ℝ (SkewFrobenius n) = Fintype.card n ^ 2 :=
  (finrank_adjoint_matrix_spaces n).2

theorem euclideanHausdorffMeasure_skewFrobenius :
    (μHE[Fintype.card n ^ 2] : Measure (SkewFrobenius n)) = volume := by
  rw [← finrank_skewFrobenius]
  exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume

/-- Upper bound for the cap: `Vol_F(cap) ≤ 8^N vol(sector)`. -/
theorem unitaryFrobeniusMeasure_cayleyCap_le (R : ℝ) :
    unitaryFrobeniusMeasure n (cayleyCap R) ≤
      (8 : ℝ≥0∞) ^ (Fintype.card n ^ 2) * volume (closedSkewSector (n := n) R) := by
  rw [unitaryFrobeniusMeasure_apply, image_cayleyCap, ← euclideanHausdorffMeasure_skewFrobenius]
  have h := euclideanHausdorffMeasure_image_le_of_lipschitzOnWith
    (lipschitzOnWith_skewCayleyEuclidean (n := n) R) (Fintype.card n ^ 2)
  simpa using h

/-- Lower bound for the cap: `vol(sector) ≤ 2^N Vol_F(cap)`. -/
theorem volume_closedSkewSector_le (R : ℝ) :
    volume (closedSkewSector (n := n) R) ≤
      (2 : ℝ≥0∞) ^ (Fintype.card n ^ 2) * unitaryFrobeniusMeasure n (cayleyCap R) := by
  rw [unitaryFrobeniusMeasure_apply, image_cayleyCap, ← euclideanHausdorffMeasure_skewFrobenius]
  have h := euclideanHausdorffMeasure_le_of_expand
    (dist_le_two_mul_dist_skewCayleyEuclidean (n := n) R) (Fintype.card n ^ 2)
  simpa using h

/-! ### A neighbourhood of the identity inside the cap -/

/-- Every unitary within Frobenius distance `min(1/2, R)` of the identity is `c(A)` for a
skew-Hermitian `A` with `‖A‖_op ≤ 1/2` and `‖A‖_F ≤ R`: take `A = 1 − Q⁻¹`, `Q = (1 + U)/2`. -/
theorem ball_one_subset_cayleyCap {R : ℝ} :
    {U : Matrix.unitaryGroup n ℂ | ‖(U : Matrix n n ℂ) - 1‖ < min (1 / 2) R} ⊆ cayleyCap R := by
  intro U hU
  simp only [Set.mem_ofPred_eq, lt_min_iff] at hU
  obtain ⟨hU2, hUR⟩ := hU
  set V : Matrix n n ℂ := (U : Matrix n n ℂ) with hV
  have hVH : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hHV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  set B : Matrix n n ℂ := (2 : ℂ)⁻¹ • (1 - V) with hB
  have hBn : ‖B‖ = 2⁻¹ * ‖V - 1‖ := by
    rw [hB, norm_smul, ← norm_neg (1 - V), neg_sub]
    norm_num
  have hBop : opNorm B ≤ 1 / 2 :=
    (opNorm_le_frobNorm B).trans (by rw [hBn]; linarith [norm_nonneg (V - 1)])
  set Q : Matrix n n ℂ := 1 - B with hQ
  have hQu : IsUnit Q := isUnit_one_sub_of_opNorm_lt_one (hBop.trans_lt (by norm_num))
  have hQd := (Matrix.isUnit_iff_isUnit_det _).mp hQu
  have h2Q : (1 : Matrix n n ℂ) + V = (2 : ℂ) • Q := by
    rw [hQ, hB]
    module
  set A : Matrix n n ℂ := 1 - Q⁻¹ with hA
  -- skewness
  have hQH : Qᴴ = Vᴴ * Q := by
    have hst : star (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by simp
    rw [hQ, hB, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hst, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_sub, hVH,
      Matrix.mul_one]
    module
  have hVHinv : (Vᴴ)⁻¹ = V := Matrix.inv_eq_left_inv hHV
  have hQinvU : Q⁻¹ * V = (2 : ℂ) • 1 - Q⁻¹ := by
    have h : Q⁻¹ * ((2 : ℂ) • Q) = (2 : ℂ) • 1 := by
      rw [Matrix.mul_smul, Matrix.nonsing_inv_mul _ hQd]
    rw [← h2Q, Matrix.mul_add, Matrix.mul_one] at h
    rw [← h]
    abel
  have hskew : Aᴴ = -A := by
    rw [hA, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_nonsing_inv,
      hQH, Matrix.mul_inv_rev, hVHinv, hQinvU]
    module
  -- the Cayley image is `U`
  have hcay : matrixCayley A = V := by
    have h1A : 1 - A = Q⁻¹ := by rw [hA]; abel
    rw [matrixCayley, h1A, Matrix.nonsing_inv_nonsing_inv _ hQd, hA]
    have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQd
    calc (1 + (1 - Q⁻¹)) * Q = Q + Q - Q⁻¹ * Q := by noncomm_ring
      _ = (2 : ℂ) • Q - 1 := by rw [hQQ, two_smul]
      _ = V := by rw [← h2Q]; abel
  -- the norms
  have hAeq : A = -B * Q⁻¹ := by
    have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQd
    calc A = Q * Q⁻¹ - Q⁻¹ := by rw [hA, hQQ]
      _ = -B * Q⁻¹ := by rw [hQ]; noncomm_ring
  have hAn : ‖A‖ ≤ ‖V - 1‖ := by
    rw [hAeq, hQ]
    calc ‖-B * (1 - B)⁻¹‖ ≤ 2 * ‖-B‖ := frobNorm_mul_inv_one_sub_le hBop (-B)
      _ = ‖V - 1‖ := by rw [norm_neg, hBn]; ring
  have hAop : opNorm A ≤ 1 / 2 := (opNorm_le_frobNorm A).trans (by linarith)
  let A' : SkewFrobenius n := ⟨A, skewAdjoint.mem_iff.mpr hskew⟩
  refine ⟨A', ⟨hAop, ?_⟩, ?_⟩
  · change ‖A‖ ≤ R
    linarith
  · change matrixFrobeniusCoordinates n n (matrixCayley A) = matrixFrobeniusCoordinates n n V
    rw [hcay]

theorem isOpen_ball_one_unitary (r : ℝ) :
    IsOpen {U : Matrix.unitaryGroup n ℂ | ‖(U : Matrix n n ℂ) - 1‖ < r} :=
  isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const

/-! ### Finiteness and the Haar identity -/

theorem unitaryFrobeniusMeasure_cayleyCap_lt_top (R : ℝ) :
    unitaryFrobeniusMeasure n (cayleyCap R) < ∞ := by
  refine (unitaryFrobeniusMeasure_cayleyCap_le R).trans_lt (ENNReal.mul_lt_top (by simp) ?_)
  have hsub : closedSkewSector (n := n) R ⊆ Metric.ball 0 (|R| + 1) := fun A hA => by
    rw [mem_ball, dist_zero_right]
    linarith [hA.2, le_abs_self R]
  refine (measure_mono hsub).trans_lt ?_
  rw [volume_skew_ball n _ (by positivity)]
  exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top

theorem unitaryFrobeniusVolume_lt_top : unitaryFrobeniusVolume n < ∞ := by
  classical
  set O : Matrix.unitaryGroup n ℂ → Set (Matrix.unitaryGroup n ℂ) :=
    fun W => (fun V => W⁻¹ * V) ⁻¹' {U | ‖(U : Matrix n n ℂ) - 1‖ < min (1 / 2) 1} with hO
  have hOopen : ∀ W, IsOpen (O W) := fun W =>
    (isOpen_ball_one_unitary _).preimage (continuous_const_mul _)
  have hOcover : Set.univ ⊆ ⋃ W, O W := fun W _ =>
    Set.mem_iUnion.mpr ⟨W, by simp [hO]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOopen hOcover
  have hOle : ∀ W, unitaryFrobeniusMeasure n (O W) ≤ unitaryFrobeniusMeasure n (cayleyCap 1) := by
    intro W
    rw [hO, measure_preimage_mul]
    exact measure_mono ball_one_subset_cayleyCap
  rw [← unitaryFrobeniusMeasure_univ]
  calc unitaryFrobeniusMeasure n Set.univ ≤ unitaryFrobeniusMeasure n (⋃ W ∈ t, O W) :=
        measure_mono ht
    _ ≤ ∑ W ∈ t, unitaryFrobeniusMeasure n (O W) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _W ∈ t, unitaryFrobeniusMeasure n (cayleyCap 1) := Finset.sum_le_sum fun W _ => hOle W
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (by simp) (unitaryFrobeniusMeasure_cayleyCap_lt_top 1)

instance isFiniteMeasure_unitaryFrobeniusMeasure : IsFiniteMeasure (unitaryFrobeniusMeasure n) :=
  ⟨by rw [unitaryFrobeniusMeasure_univ]; exact unitaryFrobeniusVolume_lt_top⟩

/-- The intrinsic Frobenius measure is `Vol_F U(n)` times probability Haar measure. -/
theorem unitaryFrobeniusMeasure_eq_smul :
    unitaryFrobeniusMeasure n = unitaryFrobeniusVolume n • unitaryHaar n := by
  rw [← unitaryFrobeniusMeasure_univ]
  exact unitary_invariant_measure_eq_smul n _

theorem unitaryFrobeniusMeasure_apply_eq_mul (S : Set (Matrix.unitaryGroup n ℂ)) :
    unitaryFrobeniusMeasure n S = unitaryFrobeniusVolume n * unitaryHaar n S := by
  conv_lhs => rw [unitaryFrobeniusMeasure_eq_smul]
  rfl

theorem unitaryHaar_cayleyCap_pos {R : ℝ} (hR : 0 < R) : 0 < unitaryHaar n (cayleyCap R) := by
  refine lt_of_lt_of_le ?_ (measure_mono ball_one_subset_cayleyCap)
  exact (isOpen_ball_one_unitary _).measure_pos _ ⟨1, by simp [lt_min_iff, hR]⟩

/-! ### Comparison with the operator-normal chart -/

/-- The chart image lies in the operator-normal measure of the Cayley cap. -/
theorem strong_chart_image_volume_le_cayleyCap (s : ℝ) :
    volume (normalCayleyEuclidean n '' opAdjointChartDomain n s) ≤
      unitaryOpNormalMeasure n s (cayleyCap (Real.sqrt (Fintype.card n) / 64)) := by
  rw [unitaryOpNormalMeasure_apply n s (measurableSet_cayleyCap _)]
  apply measure_mono
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨⟨hQop, hQ⟩, hAop, hAR⟩ := (mem_opAdjointChartDomain_iff s z).mp hz
  let U : Matrix.unitaryGroup n ℂ := ⟨matrixCayley (normalSkewCoordinate n z),
    Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_matrixCayley _
      (normalSkewCoordinate_adjoint z) (isUnit_one_sub_of_opNorm_lt_one (hAop.trans_lt (by norm_num))))⟩
  refine ⟨(U, ⟨normalHermitianCoordinate n z, normalHermitianCoordinate_adjoint z, hQop⟩),
    ⟨?_, hQ⟩, rfl⟩
  exact ⟨((adjointSumEuclidean n).symm z).snd, ⟨hAop, hAR.le⟩, rfl⟩

theorem strongNormalLowerFactor_le_cayleyCap {s : ℝ} (hs : 0 < s)
    (hsD : s ≤ Real.sqrt (Fintype.card n) / 64) :
    strongNormalLowerFactor n s ≤
      unitaryOpNormalMeasure n s (cayleyCap (Real.sqrt (Fintype.card n) / 64)) := by
  have hdom : MeasurableSet (opAdjointChartDomain n s) := measurableSet_opAdjointChartDomain s
  have hcv := lintegral_abs_det_fderiv_eq_addHaar_image volume hdom
    (fun z hz => (hasFDerivAt_normalCayleyEuclidean_of_isUnit z
      (isUnit_one_sub_of_opNorm_lt_one
        (((mem_opAdjointChartDomain_iff s z).mp hz).2.1.trans_lt (by norm_num)))).hasFDerivWithinAt)
    (normalCayleyEuclidean_injectiveOn_op s)
  refine le_trans ?_ (hcv.le.trans (strong_chart_image_volume_le_cayleyCap s))
  calc strongNormalLowerFactor n s ≤
        ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) * volume (opAdjointChartDomain n s) := by
        unfold strongNormalLowerFactor
        gcongr
        exact strongNormalDomain_volume_ge n hs hsD
    _ = ∫⁻ _z in opAdjointChartDomain n s, ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) := by
        rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    _ ≤ ∫⁻ z in opAdjointChartDomain n s,
        ENNReal.ofReal |(normalCayleyEuclideanDerivative n z).det| := by
        apply setLIntegral_mono' hdom
        intro z hz
        obtain ⟨⟨hQ, -⟩, hA, -⟩ := (mem_opAdjointChartDomain_iff s z).mp hz
        exact ENNReal.ofReal_le_ofReal (normalCayleyEuclidean_det_lower_of_opNorm z hA hQ)

/-! ### `lem:normal-volume` -/

omit [DecidableEq n] in
theorem one_le_card_sq [Nonempty n] : 1 ≤ Fintype.card n ^ 2 :=
  Nat.one_le_pow _ _ Fintype.card_pos

/-- **`lem:normal-volume`, group volume.** `Vol_F U(n) ≥ (√D/256)^N ω_N`, `D = |n|`, `N = D²`. -/
theorem unitaryFrobeniusVolume_ge [Nonempty n] :
    ENNReal.ofReal ((Real.sqrt (Fintype.card n) / 256) ^ (Fintype.card n ^ 2)) *
        euclideanUnitBallVolume (Fintype.card n ^ 2) ≤ unitaryFrobeniusVolume n := by
  set N := Fintype.card n ^ 2 with hN
  set R := Real.sqrt (Fintype.card n) / 64 with hR
  have hR0 : 0 < R := by
    rw [hR]; have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    positivity
  have hN1 : 1 ≤ N := one_le_card_sq
  -- `½ R^N ω ≤ vol(sector) ≤ 2^N Vol_F(cap) ≤ 2^N Vol_F`
  have hball := volume_ball_le_two_mul_skewOperatorSector n hR0 le_rfl
  rw [volume_skew_ball n R hR0] at hball
  have hsec : volume (skewOperatorSector n R) ≤ volume (closedSkewSector (n := n) R) :=
    measure_mono fun A hA => ⟨hA.1, by
      have h := hA.2; rw [mem_ball, dist_zero_right] at h; exact h.le⟩
  have hcap : unitaryFrobeniusMeasure n (cayleyCap R) ≤ unitaryFrobeniusVolume n := by
    rw [← unitaryFrobeniusMeasure_univ]; exact measure_mono (Set.subset_univ _)
  have hchain : ENNReal.ofReal R ^ N * euclideanUnitBallVolume N ≤
      2 * ((2 : ℝ≥0∞) ^ N * unitaryFrobeniusVolume n) :=
    hball.trans (mul_le_mul_right (hsec.trans ((volume_closedSkewSector_le R).trans
      (mul_le_mul_right hcap _))) 2)
  have hω : euclideanUnitBallVolume N ≠ ∞ := measure_ball_lt_top.ne
  -- `2^N · 2 · (R/4)^N ≤ R^N`
  have hreal : (2 : ℝ) ^ N * (2 * (R / 4) ^ N) ≤ R ^ N := by
    have h4 : (2 : ℝ) ^ N * (2 * (R / 4) ^ N) = 2 * (R ^ N / 2 ^ N) := by
      rw [div_pow, show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
      field_simp
    rw [h4]
    have h2N : (2 : ℝ) ≤ 2 ^ N := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN1
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hR0 N]
  have htarget : (Real.sqrt (Fintype.card n) / 256) = R / 4 := by rw [hR]; ring
  rw [htarget]
  have h2ne : (2 : ℝ≥0∞) ^ N * 2 ≠ 0 := by positivity
  have h2top : (2 : ℝ≥0∞) ^ N * 2 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  refine (ENNReal.mul_le_mul_iff_right h2ne h2top).mp ?_
  calc (2 : ℝ≥0∞) ^ N * 2 * (ENNReal.ofReal ((R / 4) ^ N) * euclideanUnitBallVolume N)
      = ENNReal.ofReal ((2 : ℝ) ^ N * (2 * (R / 4) ^ N)) * euclideanUnitBallVolume N := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (R ^ N) * euclideanUnitBallVolume N := by
        gcongr
    _ = ENNReal.ofReal R ^ N * euclideanUnitBallVolume N := by
        rw [ENNReal.ofReal_pow hR0.le]
    _ ≤ 2 * ((2 : ℝ≥0∞) ^ N * unitaryFrobeniusVolume n) := hchain
    _ = (2 : ℝ≥0∞) ^ N * 2 * unitaryFrobeniusVolume n := by ring

/-- The operator-normal mass dominates the intrinsic volume:
`(1/1024)^N ω_N t^N Vol_F U(n) ≤ M(t)` for `0 < t ≤ √D/64`. -/
theorem unitaryFrobeniusVolume_le_unitaryOpNormalMeasure [Nonempty n] {t : ℝ} (ht : 0 < t)
    (htD : t ≤ Real.sqrt (Fintype.card n) / 64) :
    ENNReal.ofReal ((1 / 1024 : ℝ) ^ (Fintype.card n ^ 2)) *
        euclideanUnitBallVolume (Fintype.card n ^ 2) * ENNReal.ofReal t ^ (Fintype.card n ^ 2) *
        unitaryFrobeniusVolume n ≤ unitaryOpNormalMeasure n t Set.univ := by
  set N := Fintype.card n ^ 2 with hN
  set R := Real.sqrt (Fintype.card n) / 64 with hR
  have hR0 : 0 < R := ht.trans_le htD
  have hN1 : 1 ≤ N := one_le_card_sq
  set ω := euclideanUnitBallVolume N with hω
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set a := unitaryHaar n (cayleyCap R) with ha
  have ha0 : a ≠ 0 := (unitaryHaar_cayleyCap_pos hR0).ne'
  have hatop : a ≠ ∞ := measure_ne_top _ _
  -- `Vol_F · a ≤ 8^N (2R)^N ω`
  have hcapU : unitaryFrobeniusVolume n * a ≤
      (8 : ℝ≥0∞) ^ N * (ENNReal.ofReal (2 * R) ^ N * ω) := by
    rw [← unitaryFrobeniusMeasure_apply_eq_mul]
    refine (unitaryFrobeniusMeasure_cayleyCap_le R).trans (mul_le_mul_right ?_ _)
    rw [← volume_skew_ball n (2 * R) (by positivity)]
    exact measure_mono fun A hA => by
      rw [mem_ball, dist_zero_right]; linarith [hA.2]
  -- `strongNormalLowerFactor ≤ M(t) · a`
  have hcapM : strongNormalLowerFactor n t ≤ unitaryOpNormalMeasure n t Set.univ * a := by
    refine (strongNormalLowerFactor_le_cayleyCap ht htD).trans_eq ?_
    rw [ha]
    simpa only [Measure.smul_apply, smul_eq_mul] using
      congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ (cayleyCap R))
        (unitaryOpNormalMeasure_eq_smul n t)
  -- the real constants: `(1/1024)^N 8^N (2R)^N ≤ (1/16)^N · ¼ · R^N`
  have hreal : (1 / 1024 : ℝ) ^ N * (8 ^ N * (2 * R) ^ N) ≤
      (1 / 16 : ℝ) ^ N * ((1 / 2) * (1 / 2) * R ^ N) := by
    have hl : (1 / 1024 : ℝ) ^ N * (8 ^ N * (2 * R) ^ N) = (1 / 16) ^ N * ((1 / 4) ^ N * R ^ N) := by
      rw [← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]; ring_nf
    rw [hl]
    gcongr
    calc (1 / 4 : ℝ) ^ N ≤ (1 / 4) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN1
      _ = 1 / 2 * (1 / 2) := by norm_num
  have hkey : ENNReal.ofReal ((1 / 1024 : ℝ) ^ N) * ω * ENNReal.ofReal t ^ N *
      ((8 : ℝ≥0∞) ^ N * (ENNReal.ofReal (2 * R) ^ N * ω)) ≤ strongNormalLowerFactor n t := by
    unfold strongNormalLowerFactor
    rw [← hN, ← hR, ← hω]
    have e8 : (8 : ℝ≥0∞) ^ N = ENNReal.ofReal ((8 : ℝ) ^ N) := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    have e2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have hpow : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ^ N = ENNReal.ofReal (x ^ N) :=
      fun x hx => (ENNReal.ofReal_pow hx N).symm
    rw [e8, e2, hpow (2 * R) (by positivity), hpow R hR0.le, hpow t ht.le]
    calc ENNReal.ofReal ((1 / 1024 : ℝ) ^ N) * ω * ENNReal.ofReal (t ^ N) *
          (ENNReal.ofReal ((8 : ℝ) ^ N) * (ENNReal.ofReal ((2 * R) ^ N) * ω))
        = ENNReal.ofReal ((1 / 1024 : ℝ) ^ N * (8 ^ N * (2 * R) ^ N)) *
            (ENNReal.ofReal (t ^ N) * ω * ω) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ N * ((1 / 2) * (1 / 2) * R ^ N)) *
            (ENNReal.ofReal (t ^ N) * ω * ω) := by gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
  refine (ENNReal.mul_le_mul_iff_left ha0 hatop).mp ?_
  calc ENNReal.ofReal ((1 / 1024 : ℝ) ^ N) * ω * ENNReal.ofReal t ^ N *
        unitaryFrobeniusVolume n * a
      = ENNReal.ofReal ((1 / 1024 : ℝ) ^ N) * ω * ENNReal.ofReal t ^ N *
          (unitaryFrobeniusVolume n * a) := by ring
    _ ≤ ENNReal.ofReal ((1 / 1024 : ℝ) ^ N) * ω * ENNReal.ofReal t ^ N *
          ((8 : ℝ≥0∞) ^ N * (ENNReal.ofReal (2 * R) ^ N * ω)) := by gcongr
    _ ≤ strongNormalLowerFactor n t := hkey
    _ ≤ _ := hcapM

/-- **`lem:normal-volume`, tube inequality.** For every Borel `S` and `0 < t ≤ √D/64`,
`(1/1024)^N ω_N t^N Vol_F U(n) μ(S) ≤ Vol_{2N}(U_t(S))`. -/
theorem volume_unitaryFrobeniusTube_ge [Nonempty n] {t : ℝ} (ht : 0 < t)
    (htD : t ≤ Real.sqrt (Fintype.card n) / 64) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    ENNReal.ofReal ((1 / 1024 : ℝ) ^ (Fintype.card n ^ 2)) *
        euclideanUnitBallVolume (Fintype.card n ^ 2) * ENNReal.ofReal t ^ (Fintype.card n ^ 2) *
        unitaryFrobeniusVolume n * unitaryHaar n S ≤ volume (unitaryFrobeniusTube n t S) :=
  (mul_le_mul_left (unitaryFrobeniusVolume_le_unitaryOpNormalMeasure ht htD) _).trans
    (unitaryOpNormalMeasure_total_mul_haar_le_tube n t hS)

end Volume

end NLQCLean
