import NLQCLean.Geometry.UnitaryCayley
import NLQCLean.Geometry.AdjointEuclideanCoordinates

/-!
# The equal-dimensional normal Cayley chart

Combine the Cayley derivative with the Hermitian normal factor.
The chart is expressed in the orthogonal Euclidean coordinates whose
domain volume is computed in orthonormal coordinates.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Topology _root_.ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The algebraic differential of `(A,Q) ↦ c(A)(I+Q)`. -/
noncomputable def normalCayleyVelocity (A Q B S : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixCayleyDerivative A B * (1 + Q) + matrixCayley A * S

theorem normalCayleyVelocity_left (A Q B S : Matrix n n ℂ)
    (hC : IsIsometry (matrixCayley A)) :
    (matrixCayley A)ᴴ * normalCayleyVelocity A Q B S =
      (matrixCayley A)ᴴ * matrixCayleyDerivative A B + S +
        ((matrixCayley A)ᴴ * matrixCayleyDerivative A B) * Q := by
  have h := hC.conjTranspose_mul_self
  calc
    _ = (matrixCayley A)ᴴ * matrixCayleyDerivative A B +
        ((matrixCayley A)ᴴ * matrixCayley A) * S +
          ((matrixCayley A)ᴴ * matrixCayleyDerivative A B) * Q := by
      unfold normalCayleyVelocity
      noncomm_ring
    _ = _ := by rw [h, Matrix.one_mul]

/-- One-quarter expansion in the orthogonal input norm. -/
theorem quarter_norm_le_normalCayleyVelocity (A Q B S : Matrix n n ℂ)
    (hA : Aᴴ = -A) (hB : Bᴴ = -B) (hS : Sᴴ = S)
    (hAn : ‖A‖ < 1) (hQn : ‖Q‖ ≤ 1 / 2) :
    (1 / 4 : ℝ) * ‖S + B‖ ≤ ‖normalCayleyVelocity A Q B S‖ := by
  let C := matrixCayley A
  let L := Cᴴ * matrixCayleyDerivative A B
  let V := normalCayleyVelocity A Q B S
  have hi := isUnit_one_sub_matrix_of_norm_lt_one A hAn
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
  have hsmall : ‖L * Q‖ ≤ (1 / 2 : ℝ) * ‖L‖ := by
    calc
      _ ≤ ‖L‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hQn (norm_nonneg L)]
  have hperturb : ‖S + L‖ ≤ ‖V‖ + (1 / 2 : ℝ) * ‖L‖ := by
    calc
      _ = ‖Cᴴ * V - L * Q‖ := by rw [hLV, add_sub_cancel_right]
      _ ≤ ‖Cᴴ * V‖ + ‖L * Q‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hVn]; exact add_le_add le_rfl hsmall
  have hhalf : (1 / 2 : ℝ) * ‖B‖ ≤ ‖L‖ := by
    rw [hLn]
    exact half_norm_le_matrixCayleyDerivative A B hAn
  have hsum : (1 / 2 : ℝ) * ‖S + B‖ ≤ ‖S + L‖ := by
    have hsq : ((1 / 2 : ℝ) * ‖B‖) ^ 2 ≤ ‖L‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    nlinarith [norm_nonneg (S + L), norm_nonneg (S + B), sq_nonneg ‖S‖]
  linarith

/-- The Hermitian coordinate of the orthogonal Euclidean decomposition. -/
noncomputable def normalHermitianCoordinate (n : Type*) [Fintype n] :
    EuclideanSpace ℝ ((n × n) × Fin 2) →L[ℝ] Matrix n n ℂ :=
  (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.comp
    ((WithLp.fstL 2 ℝ (HermitianFrobenius n) (SkewFrobenius n)).comp
      (adjointSumEuclidean n).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The skew-Hermitian coordinate of the orthogonal Euclidean decomposition. -/
noncomputable def normalSkewCoordinate (n : Type*) [Fintype n] :
    EuclideanSpace ℝ ((n × n) × Fin 2) →L[ℝ] Matrix n n ℂ :=
  (skewAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.comp
    ((WithLp.sndL 2 ℝ (HermitianFrobenius n) (SkewFrobenius n)).comp
      (adjointSumEuclidean n).symm.toContinuousLinearEquiv.toContinuousLinearMap)

omit [DecidableEq n] in
theorem normalHermitianCoordinate_adjoint (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    (normalHermitianCoordinate n z)ᴴ = normalHermitianCoordinate n z :=
  ((adjointSumEuclidean n).symm z).fst.property

omit [DecidableEq n] in
theorem normalSkewCoordinate_adjoint (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    (normalSkewCoordinate n z)ᴴ = -(normalSkewCoordinate n z) :=
  ((adjointSumEuclidean n).symm z).snd.property

omit [DecidableEq n] in
theorem normalHermitianCoordinate_add_skew (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    normalHermitianCoordinate n z + normalSkewCoordinate n z =
      (matrixFrobeniusCoordinates n n).symm z := by
  apply (matrixFrobeniusCoordinates n n).injective
  change (adjointSumEuclidean n) ((adjointSumEuclidean n).symm z) =
    (matrixFrobeniusCoordinates n n) ((matrixFrobeniusCoordinates n n).symm z)
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem mem_adjointChartDomain_iff (s : ℝ) (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    z ∈ adjointChartDomain n s ↔
      ‖normalHermitianCoordinate n z‖ < s ∧ ‖normalSkewCoordinate n z‖ < 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ‖(((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).fst : Matrix n n ℂ)‖ < s ∧
      ‖(((adjointSumEuclidean n).symm ((adjointSumEuclidean n) x)).snd : Matrix n n ℂ)‖ < 1
    rw [LinearIsometryEquiv.symm_apply_apply]
    simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_ball, dist_zero_right] at hx
    exact hx
  · intro hz
    refine ⟨(adjointSumEuclidean n).symm z, ?_, (adjointSumEuclidean n).apply_symm_apply z⟩
    change ‖(((adjointSumEuclidean n).symm z).fst : Matrix n n ℂ)‖ < s ∧
      ‖(((adjointSumEuclidean n).symm z).snd : Matrix n n ℂ)‖ < 1 at hz
    simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_ball, dist_zero_right]
    exact hz

/-- The normal Cayley chart as an endomorphism of the ambient real Euclidean space. -/
noncomputable def normalCayleyEuclidean (n : Type*) [Fintype n] [DecidableEq n]
    (z : EuclideanSpace ℝ ((n × n) × Fin 2)) : EuclideanSpace ℝ ((n × n) × Fin 2) :=
  matrixFrobeniusCoordinates n n
    (matrixCayley (normalSkewCoordinate n z) * (1 + normalHermitianCoordinate n z))

/-- The derivative in exactly the same Euclidean source and target. -/
noncomputable def normalCayleyEuclideanDerivative (n : Type*) [Fintype n] [DecidableEq n]
    (z : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    EuclideanSpace ℝ ((n × n) × Fin 2) →L[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) :=
  (matrixFrobeniusCoordinates n n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip (1 + normalHermitianCoordinate n z)).comp
      ((matrixCayleyDerivative (normalSkewCoordinate n z)).comp (normalSkewCoordinate n))) +
      ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (matrixCayley (normalSkewCoordinate n z))).comp
        (normalHermitianCoordinate n)))

theorem normalCayleyEuclideanDerivative_apply
    (z v : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    normalCayleyEuclideanDerivative n z v = matrixFrobeniusCoordinates n n
      (normalCayleyVelocity (normalSkewCoordinate n z) (normalHermitianCoordinate n z)
        (normalSkewCoordinate n v) (normalHermitianCoordinate n v)) := rfl

theorem hasFDerivAt_normalCayleyEuclidean
    (z : EuclideanSpace ℝ ((n × n) × Fin 2)) (hz : ‖normalSkewCoordinate n z‖ < 1) :
    HasFDerivAt (normalCayleyEuclidean n) (normalCayleyEuclideanDerivative n z) z := by
  have hc := (hasFDerivAt_matrixCayley (normalSkewCoordinate n z)
    (isUnit_one_sub_matrix_of_norm_lt_one _ hz)).comp z (normalSkewCoordinate n).hasFDerivAt
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

theorem quarter_norm_le_normalCayleyEuclideanDerivative
    (z v : EuclideanSpace ℝ ((n × n) × Fin 2))
    (hz : ‖normalSkewCoordinate n z‖ < 1) (hQ : ‖normalHermitianCoordinate n z‖ ≤ 1 / 2) :
    (1 / 4 : ℝ) * ‖v‖ ≤ ‖normalCayleyEuclideanDerivative n z v‖ := by
  rw [normalCayleyEuclideanDerivative_apply, LinearIsometryEquiv.norm_map]
  have h := quarter_norm_le_normalCayleyVelocity
    (normalSkewCoordinate n z) (normalHermitianCoordinate n z)
    (normalSkewCoordinate n v) (normalHermitianCoordinate n v)
    (normalSkewCoordinate_adjoint z) (normalSkewCoordinate_adjoint v)
    (normalHermitianCoordinate_adjoint v) hz hQ
  rwa [normalHermitianCoordinate_add_skew, LinearIsometryEquiv.norm_map] at h

theorem contDiffAt_normalCayleyEuclidean
    (z : EuclideanSpace ℝ ((n × n) × Fin 2)) (hz : ‖normalSkewCoordinate n z‖ < 1) :
    ContDiffAt ℝ ∞ (normalCayleyEuclidean n) z := by
  exact (matrixFrobeniusCoordinates n n).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp z
    (((contDiffAt_matrixCayley (normalSkewCoordinate n z)
      (isUnit_one_sub_matrix_of_norm_lt_one _ hz)).comp z
      (normalSkewCoordinate n).contDiff.contDiffAt).mul
        (contDiffAt_const.add (normalHermitianCoordinate n).contDiff.contDiffAt))

theorem normalCayleyEuclidean_injectiveOn (s : ℝ) (hs : s ≤ 1 / 2) :
    Set.InjOn (normalCayleyEuclidean n) (adjointChartDomain n s) := by
  intro z hz w hw he
  obtain ⟨hzQ, hzA⟩ := (mem_adjointChartDomain_iff s z).mp hz
  obtain ⟨hwQ, hwA⟩ := (mem_adjointChartDomain_iff s w).mp hw
  have hzi := isUnit_one_sub_matrix_of_norm_lt_one _ hzA
  have hwi := isUnit_one_sub_matrix_of_norm_lt_one _ hwA
  have he' := (matrixFrobeniusCoordinates n n).injective he
  have h := (unitary_normal_eq_iff
    (matrixCayley (normalSkewCoordinate n z)) (matrixCayley (normalSkewCoordinate n w))
    (normalHermitianCoordinate n z) (normalHermitianCoordinate n w)
    (isIsometry_matrixCayley _ (normalSkewCoordinate_adjoint z) hzi)
    (isIsometry_matrixCayley _ (normalSkewCoordinate_adjoint w) hwi)
    (normalHermitianCoordinate_adjoint z) (normalHermitianCoordinate_adjoint w)
    (hzQ.le.trans hs) (hwQ.le.trans hs)).mp he'
  have hA := matrixCayley_injectiveOn hzi hwi h.1
  apply (matrixFrobeniusCoordinates n n).symm.injective
  rw [← normalHermitianCoordinate_add_skew, ← normalHermitianCoordinate_add_skew,
    hA, h.2]

end NLQCLean
