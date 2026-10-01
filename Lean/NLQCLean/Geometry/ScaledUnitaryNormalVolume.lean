import NLQCLean.Geometry.OperatorNormalMeasure
import NLQCLean.Geometry.HermitianOperatorSector

/-!
# Dimension-correct normal volume and the strong Haar tube lower bound

The Cayley normal chart `(A,Q) ↦ c(A)(I+Q)` is restricted to
the product of the operator-small sectors

  `{Q = Qᴴ : ‖Q‖_F < s, ‖Q‖_op ≤ 1/2} × {A = −Aᴴ : ‖A‖_F < √D/64, ‖A‖_op ≤ 1/2}`.

Under operator cutoffs the chart is injective and expands every vector by `1/4`, so its
Jacobian is at least `16^(−N)`. Equal-dimensional change of variables on this Borel domain,
together with their volume bounds, gives the total mass of the operator-normal measure and hence, for every
Borel `S` and `0 < s ≤ √D/64`,

  `16^(−N) · (½ s^N ω_N) · (½ (√D/64)^N ω_N) · μ(S) ≤ vol(Tube_s(S))`.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped ENNReal

section L2

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

theorem isUnit_one_sub_of_opNorm_lt_one {A : Matrix n n ℂ} (hA : opNorm A < 1) :
    IsUnit (1 - A) :=
  isUnit_one_sub_of_norm_lt_one (show ‖A‖ < 1 from hA)

end L2

open scoped Matrix.Norms.Frobenius

section Velocity

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem opNorm_one_sub_le_two {A : Matrix n n ℂ} (hA : opNorm A ≤ 1) : opNorm (1 - A) ≤ 2 := by
  have h1 : opNorm (1 : Matrix n n ℂ) ≤ 1 := (isIsometry_one (n := n) (𝕜 := ℂ)).opNorm_le_one
  have h2 : opNorm (-A) = opNorm A := by
    simpa using opNorm_smul_real (-1) A
  calc opNorm (1 - A) = opNorm (1 + -A) := by rw [sub_eq_add_neg]
    _ ≤ opNorm 1 + opNorm (-A) := opNorm_add_le _ _
    _ ≤ 2 := by rw [h2]; linarith

/-- The Cayley derivative expands by one half under an operator cutoff. -/
theorem half_norm_le_matrixCayleyDerivative_of_opNorm (A B : Matrix n n ℂ)
    (hA : opNorm A ≤ 1 / 2) :
    (1 / 2 : ℝ) * ‖B‖ ≤ ‖matrixCayleyDerivative A B‖ := by
  have hi := isUnit_one_sub_of_opNorm_lt_one (hA.trans_lt (by norm_num))
  have hc := matrixCayleyDerivative_cancel A B hi
  have h2 := opNorm_one_sub_le_two (hA.trans (by norm_num))
  have h₁ : ‖(1 - A) * matrixCayleyDerivative A B‖ ≤ 2 * ‖matrixCayleyDerivative A B‖ :=
    (frobNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have h₂ : ‖(1 - A) * matrixCayleyDerivative A B * (1 - A)‖ ≤
      ‖(1 - A) * matrixCayleyDerivative A B‖ * 2 :=
    (frobNorm_mul_le' _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  rw [hc, norm_smul] at h₂
  norm_num at h₂
  linarith

/-- The one-quarter expansion of the normal Cayley velocity under operator cutoffs. -/
theorem quarter_norm_le_normalCayleyVelocity_of_opNorm (A Q B S : Matrix n n ℂ)
    (hA : Aᴴ = -A) (hB : Bᴴ = -B) (hS : Sᴴ = S)
    (hAn : opNorm A ≤ 1 / 2) (hQn : opNorm Q ≤ 1 / 2) :
    (1 / 4 : ℝ) * ‖S + B‖ ≤ ‖normalCayleyVelocity A Q B S‖ := by
  let C := matrixCayley A
  let L := Cᴴ * matrixCayleyDerivative A B
  let V := normalCayleyVelocity A Q B S
  have hi := isUnit_one_sub_of_opNorm_lt_one (hAn.trans_lt (by norm_num))
  have hC : IsIsometry C := isIsometry_matrixCayley A hA hi
  have hCH : IsIsometry Cᴴ := by
    change (Cᴴ)ᴴ * Cᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff'.mpr hC).2
  have hL : Lᴴ = -L := matrixCayleyDerivative_left_skew A B hA hB hi
  have hLn : ‖L‖ = ‖matrixCayleyDerivative A B‖ := hCH.frobNorm_mul_eq _
  have hVn : ‖Cᴴ * V‖ = ‖V‖ := hCH.frobNorm_mul_eq _
  have hLV : Cᴴ * V = S + L + L * Q := by
    have h : Cᴴ * V = L + S + L * Q := normalCayleyVelocity_left A Q B S hC
    rwa [add_comm L S] at h
  have horth := norm_add_hermitian_skew_sq S L hS hL
  have hinput := norm_add_hermitian_skew_sq S B hS hB
  have hle : ‖L‖ ≤ ‖S + L‖ := by nlinarith [norm_nonneg (S + L), sq_nonneg ‖S‖]
  have hsmall : ‖L * Q‖ ≤ (1 / 2 : ℝ) * ‖L‖ :=
    (frobNorm_mul_le' _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hQn (norm_nonneg L)])
  have hperturb : ‖S + L‖ ≤ ‖V‖ + (1 / 2 : ℝ) * ‖L‖ := by
    calc
      _ = ‖Cᴴ * V - L * Q‖ := by rw [hLV, add_sub_cancel_right]
      _ ≤ ‖Cᴴ * V‖ + ‖L * Q‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hVn]; exact add_le_add le_rfl hsmall
  have hhalf : (1 / 2 : ℝ) * ‖B‖ ≤ ‖L‖ := by
    rw [hLn]
    exact half_norm_le_matrixCayleyDerivative_of_opNorm A B hAn
  have hsum : (1 / 2 : ℝ) * ‖S + B‖ ≤ ‖S + L‖ := by
    have hsq : ((1 / 2 : ℝ) * ‖B‖) ^ 2 ≤ ‖L‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    nlinarith [norm_nonneg (S + L), norm_nonneg (S + B), sq_nonneg ‖S‖]
  linarith

end Velocity

section Chart

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The operator-limited chart domain in ambient orthogonal coordinates. -/
def opAdjointChartDomain (s : ℝ) : Set (EuclideanSpace ℝ ((n × n) × Fin 2)) :=
  (adjointSumEuclidean n) ''
    (WithLp.ofLp ⁻¹' (hermitianOperatorSector n s ×ˢ
      skewOperatorSector n (Real.sqrt (Fintype.card n) / 64)))

omit [DecidableEq n] in
/-- The Borel instance of `AdjointEuclideanCoordinates`, read for the subtype topology. -/
theorem opensMeasurableSpace_hermitianFrobenius : OpensMeasurableSpace (HermitianFrobenius n) :=
  @BorelSpace.opensMeasurable _ _ _ (hermitianFrobeniusBorelSpace n)

omit [DecidableEq n] in
theorem opensMeasurableSpace_skewFrobenius : OpensMeasurableSpace (SkewFrobenius n) :=
  @BorelSpace.opensMeasurable _ _ _ (skewFrobeniusBorelSpace n)

theorem measurableSet_hermitianOperatorSector (R : ℝ) :
    MeasurableSet (hermitianOperatorSector n R) := by
  have := opensMeasurableSpace_hermitianFrobenius n
  exact (isClosed_le ((continuous_opNorm n n).comp continuous_subtype_val)
    continuous_const).measurableSet.inter measurableSet_ball

theorem measurableSet_skewOperatorSector (R : ℝ) :
    MeasurableSet (skewOperatorSector n R) := by
  have := opensMeasurableSpace_skewFrobenius n
  exact (isClosed_le ((continuous_opNorm n n).comp continuous_subtype_val)
    continuous_const).measurableSet.inter measurableSet_ball

variable {n}

theorem mem_opAdjointChartDomain_iff (s : ℝ) (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    z ∈ opAdjointChartDomain n s ↔
      (opNorm (normalHermitianCoordinate n z) ≤ 1 / 2 ∧ ‖normalHermitianCoordinate n z‖ < s) ∧
      (opNorm (normalSkewCoordinate n z) ≤ 1 / 2 ∧
        ‖normalSkewCoordinate n z‖ < Real.sqrt (Fintype.card n) / 64) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (opNorm (((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).fst : Matrix n n ℂ) ≤
        1 / 2 ∧ ‖(((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).fst : Matrix n n ℂ)‖ < s) ∧
      (opNorm (((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).snd : Matrix n n ℂ) ≤
        1 / 2 ∧ ‖(((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).snd : Matrix n n ℂ)‖ <
          Real.sqrt (Fintype.card n) / 64)
    rw [LinearIsometryEquiv.symm_apply_apply]
    simp only [Set.mem_preimage, Set.mem_prod, hermitianOperatorSector, skewOperatorSector,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] at hx
    exact hx
  · intro hz
    refine ⟨(adjointSumEuclidean n).symm z, ?_, (adjointSumEuclidean n).apply_symm_apply z⟩
    change (opNorm (((adjointSumEuclidean n).symm z).fst : Matrix n n ℂ) ≤ 1 / 2 ∧
        ‖(((adjointSumEuclidean n).symm z).fst : Matrix n n ℂ)‖ < s) ∧
      (opNorm (((adjointSumEuclidean n).symm z).snd : Matrix n n ℂ) ≤ 1 / 2 ∧
        ‖(((adjointSumEuclidean n).symm z).snd : Matrix n n ℂ)‖ <
          Real.sqrt (Fintype.card n) / 64) at hz
    simp only [Set.mem_preimage, Set.mem_prod, hermitianOperatorSector, skewOperatorSector,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    exact hz

theorem measurableSet_opAdjointChartDomain (s : ℝ) :
    MeasurableSet (opAdjointChartDomain n s) := by
  classical
  rw [show opAdjointChartDomain n s = {z | (opNorm (normalHermitianCoordinate n z) ≤ 1 / 2 ∧
      ‖normalHermitianCoordinate n z‖ < s) ∧ (opNorm (normalSkewCoordinate n z) ≤ 1 / 2 ∧
        ‖normalSkewCoordinate n z‖ < Real.sqrt (Fintype.card n) / 64)} from
    Set.ext (mem_opAdjointChartDomain_iff s)]
  have hH := (normalHermitianCoordinate n).continuous
  have hK := (normalSkewCoordinate n).continuous
  exact ((isClosed_le ((continuous_opNorm n n).comp hH) continuous_const).measurableSet.inter
      (isOpen_lt (continuous_norm.comp hH) continuous_const).measurableSet).inter
    ((isClosed_le ((continuous_opNorm n n).comp hK) continuous_const).measurableSet.inter
      (isOpen_lt (continuous_norm.comp hK) continuous_const).measurableSet)

theorem hasFDerivAt_normalCayleyEuclidean_of_isUnit
    (z : EuclideanSpace ℝ ((n × n) × Fin 2)) (hz : IsUnit (1 - normalSkewCoordinate n z)) :
    HasFDerivAt (normalCayleyEuclidean n) (normalCayleyEuclideanDerivative n z) z := by
  have hc := (hasFDerivAt_matrixCayley (normalSkewCoordinate n z) hz).comp z
    (normalSkewCoordinate n).hasFDerivAt
  have hh := (hasFDerivAt_const (1 : Matrix n n ℂ) z).add (normalHermitianCoordinate n).hasFDerivAt
  have h := (matrixFrobeniusCoordinates n n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z
    (hc.mul' hh)
  change HasFDerivAt (normalCayleyEuclidean n) _ z at h
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change matrixFrobeniusCoordinates n n
    (matrixCayley (normalSkewCoordinate n z) * (0 + normalHermitianCoordinate n v) +
      matrixCayleyDerivative (normalSkewCoordinate n z) (normalSkewCoordinate n v) *
        (1 + normalHermitianCoordinate n z)) = _
  rw [zero_add, add_comm]
  rfl

theorem normalCayleyEuclidean_det_lower_of_opNorm (z : EuclideanSpace ℝ ((n × n) × Fin 2))
    (hA : opNorm (normalSkewCoordinate n z) ≤ 1 / 2)
    (hQ : opNorm (normalHermitianCoordinate n z) ≤ 1 / 2) :
    (1 / 16 : ℝ) ^ (Fintype.card n ^ 2) ≤ |(normalCayleyEuclideanDerivative n z).det| := by
  have hexp : ∀ v, (1 / 4 : ℝ) * ‖v‖ ≤ ‖normalCayleyEuclideanDerivative n z v‖ := fun v => by
    rw [normalCayleyEuclideanDerivative_apply, LinearIsometryEquiv.norm_map]
    have h := quarter_norm_le_normalCayleyVelocity_of_opNorm
      (normalSkewCoordinate n z) (normalHermitianCoordinate n z)
      (normalSkewCoordinate n v) (normalHermitianCoordinate n v)
      (normalSkewCoordinate_adjoint z) (normalSkewCoordinate_adjoint v)
      (normalHermitianCoordinate_adjoint v) hA hQ
    rwa [normalHermitianCoordinate_add_skew, LinearIsometryEquiv.norm_map] at h
  have h := pow_le_abs_det_of_expansion (normalCayleyEuclideanDerivative n z).toLinearMap
    (by norm_num : (0 : ℝ) < 1 / 4) hexp
  have hd : Module.finrank ℝ (EuclideanSpace ℝ ((n × n) × Fin 2)) = 2 * (Fintype.card n ^ 2) := by
    simp [finrank_euclideanSpace, Fintype.card_prod, pow_two, mul_comm]
  rw [hd, pow_mul] at h
  norm_num at h
  exact h

theorem normalCayleyEuclidean_injectiveOn_op (s : ℝ) :
    Set.InjOn (normalCayleyEuclidean n) (opAdjointChartDomain n s) := by
  intro z hz w hw he
  obtain ⟨⟨hzQ, -⟩, hzA, -⟩ := (mem_opAdjointChartDomain_iff s z).mp hz
  obtain ⟨⟨hwQ, -⟩, hwA, -⟩ := (mem_opAdjointChartDomain_iff s w).mp hw
  have hzi := isUnit_one_sub_of_opNorm_lt_one (hzA.trans_lt (by norm_num))
  have hwi := isUnit_one_sub_of_opNorm_lt_one (hwA.trans_lt (by norm_num))
  have he' := (matrixFrobeniusCoordinates n n).injective he
  have h := (unitary_opNormal_eq_iff
    (matrixCayley (normalSkewCoordinate n z)) (matrixCayley (normalSkewCoordinate n w))
    (normalHermitianCoordinate n z) (normalHermitianCoordinate n w)
    (isIsometry_matrixCayley _ (normalSkewCoordinate_adjoint z) hzi)
    (isIsometry_matrixCayley _ (normalSkewCoordinate_adjoint w) hwi)
    (normalHermitianCoordinate_adjoint z) (normalHermitianCoordinate_adjoint w)
    hzQ hwQ).mp he'
  have hA := matrixCayley_injectiveOn hzi hwi h.1
  apply (matrixFrobeniusCoordinates n n).symm.injective
  rw [← normalHermitianCoordinate_add_skew, ← normalHermitianCoordinate_add_skew,
    hA, h.2]

variable (n)

/-- The explicit strong normal-volume factor. -/
noncomputable def strongNormalLowerFactor (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) *
    ((2⁻¹ * (ENNReal.ofReal s ^ (Fintype.card n ^ 2) * euclideanUnitBallVolume (Fintype.card n ^ 2))) *
      (2⁻¹ * (ENNReal.ofReal (Real.sqrt (Fintype.card n) / 64) ^ (Fintype.card n ^ 2) *
        euclideanUnitBallVolume (Fintype.card n ^ 2))))

theorem strongNormalDomain_volume_ge {s : ℝ} (hs : 0 < s)
    (hsD : s ≤ Real.sqrt (Fintype.card n) / 64) :
    (2⁻¹ * (ENNReal.ofReal s ^ (Fintype.card n ^ 2) * euclideanUnitBallVolume (Fintype.card n ^ 2))) *
      (2⁻¹ * (ENNReal.ofReal (Real.sqrt (Fintype.card n) / 64) ^ (Fintype.card n ^ 2) *
        euclideanUnitBallVolume (Fintype.card n ^ 2))) ≤ volume (opAdjointChartDomain n s) := by
  have hR : 0 < Real.sqrt (Fintype.card n) / 64 := hs.trans_le hsD
  rw [opAdjointChartDomain, volume_adjointSumEuclidean_image,
    (WithLp.volume_preserving_ofLp (HermitianFrobenius n) (SkewFrobenius n)).measure_preimage
      ((measurableSet_hermitianOperatorSector n s).prod
        (measurableSet_skewOperatorSector n _)).nullMeasurableSet]
  change _ ≤ (volume.prod volume) (hermitianOperatorSector n s ×ˢ
    skewOperatorSector n (Real.sqrt (Fintype.card n) / 64))
  rw [Measure.prod_prod]
  have half : ∀ {B S : ℝ≥0∞}, B ≤ 2 * S → 2⁻¹ * B ≤ S := fun {B S} h => by
    calc 2⁻¹ * B ≤ 2⁻¹ * (2 * S) := by gcongr
      _ = S := by rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hH := volume_ball_le_two_mul_hermitianOperatorSector n hs hsD
  rw [volume_hermitian_ball n s hs] at hH
  have hK := volume_ball_le_two_mul_skewOperatorSector n hR le_rfl
  rw [volume_skew_ball n _ hR] at hK
  exact mul_le_mul' (half hH) (half hK)

/-- The Cayley image of the strong domain lies in the operator-normal measure. -/
theorem strong_chart_image_volume_le_unitaryOpNormalMeasure (s : ℝ) :
    volume (normalCayleyEuclidean n '' opAdjointChartDomain n s) ≤
      unitaryOpNormalMeasure n s Set.univ := by
  rw [unitaryOpNormalMeasure_apply n s MeasurableSet.univ]
  apply measure_mono
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨⟨hQop, hQ⟩, hAop, -⟩ := (mem_opAdjointChartDomain_iff s z).mp hz
  let U : Matrix.unitaryGroup n ℂ := ⟨matrixCayley (normalSkewCoordinate n z),
    Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_matrixCayley _
      (normalSkewCoordinate_adjoint z) (isUnit_one_sub_of_opNorm_lt_one (hAop.trans_lt (by norm_num))))⟩
  exact ⟨(U, ⟨normalHermitianCoordinate n z, normalHermitianCoordinate_adjoint z, hQop⟩),
    ⟨Set.mem_univ _, hQ⟩, rfl⟩

/-- Total mass of the operator-normal measure. -/
theorem strongNormalLowerFactor_le_total {s : ℝ} (hs : 0 < s)
    (hsD : s ≤ Real.sqrt (Fintype.card n) / 64) :
    strongNormalLowerFactor n s ≤ unitaryOpNormalMeasure n s Set.univ := by
  have hdom : MeasurableSet (opAdjointChartDomain n s) := measurableSet_opAdjointChartDomain s
  have hcv := lintegral_abs_det_fderiv_eq_addHaar_image volume hdom
    (fun z hz => (hasFDerivAt_normalCayleyEuclidean_of_isUnit z
      (isUnit_one_sub_of_opNorm_lt_one
        (((mem_opAdjointChartDomain_iff s z).mp hz).2.1.trans_lt (by norm_num)))).hasFDerivWithinAt)
    (normalCayleyEuclidean_injectiveOn_op s)
  refine le_trans ?_ (hcv.le.trans (strong_chart_image_volume_le_unitaryOpNormalMeasure n s))
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

/-- The dimension-correct Haar tube lower bound, `0 < s ≤ √D/64`, every Borel `S`. -/
theorem unitaryHaar_tube_volume_lower_strong {s : ℝ} (hs : 0 < s)
    (hsD : s ≤ Real.sqrt (Fintype.card n) / 64) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    strongNormalLowerFactor n s * unitaryHaar n S ≤ volume (unitaryFrobeniusTube n s S) :=
  (mul_le_mul_left (strongNormalLowerFactor_le_total n hs hsD) _).trans
    (unitaryOpNormalMeasure_total_mul_haar_le_tube n s hS)

end Chart

end NLQCLean
