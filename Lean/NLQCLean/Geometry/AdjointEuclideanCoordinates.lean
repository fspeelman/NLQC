import NLQCLean.Geometry.RealFrobeniusInner
import NLQCLean.LinearAlgebra.AdjointDimension
import NLQCLean.Geometry.PolynomialImageVolumeHypothesis

/-!
# Orthogonal adjoint coordinates and volume

The Hermitian and skew-Hermitian halves carry their real
Frobenius inner products. Addition is an isometry from their Hilbert direct
sum, and carries their product Lebesgue measure to ambient Euclidean volume.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

abbrev HermitianFrobenius (n : Type*) [Fintype n] :=
  ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))

abbrev SkewFrobenius (n : Type*) [Fintype n] :=
  ↥(skewAdjoint.submodule ℝ (Matrix n n ℂ))

variable (n : Type*) [Fintype n]

noncomputable instance hermitianFrobeniusMeasurableSpace :
    MeasurableSpace (HermitianFrobenius n) := borel _
instance hermitianFrobeniusBorelSpace :
    @BorelSpace (HermitianFrobenius n)
      (inferInstance : NormedAddCommGroup (HermitianFrobenius n)).toUniformSpace.toTopologicalSpace
      (hermitianFrobeniusMeasurableSpace n) := by
  exact ⟨rfl⟩
noncomputable instance skewFrobeniusMeasurableSpace :
    MeasurableSpace (SkewFrobenius n) := borel _
instance skewFrobeniusBorelSpace :
    @BorelSpace (SkewFrobenius n)
      (inferInstance : NormedAddCommGroup (SkewFrobenius n)).toUniformSpace.toTopologicalSpace
      (skewFrobeniusMeasurableSpace n) := by
  exact ⟨rfl⟩

instance hermitianFrobeniusSigmaFinite : SigmaFinite (volume : Measure (HermitianFrobenius n)) :=
  inferInstanceAs (SigmaFinite (stdOrthonormalBasis ℝ (HermitianFrobenius n)).toBasis.addHaar)
instance skewFrobeniusSigmaFinite : SigmaFinite (volume : Measure (SkewFrobenius n)) :=
  inferInstanceAs (SigmaFinite (stdOrthonormalBasis ℝ (SkewFrobenius n)).toBasis.addHaar)

/-- Addition of the two adjoint halves, using the l2 direct-sum norm. -/
noncomputable def adjointSumFrobenius :
    WithLp 2 (HermitianFrobenius n × SkewFrobenius n) ≃ₗᵢ[ℝ] Matrix n n ℂ where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ _).trans
    (StarModule.decomposeProdAdjoint ℝ (Matrix n n ℂ)).symm
  norm_map' x := by
    have h := norm_add_hermitian_skew_sq
      (x.fst : Matrix n n ℂ) (x.snd : Matrix n n ℂ) x.fst.property x.snd.property
    have hnorm := WithLp.prod_norm_sq_eq_of_L2 x
    change ‖x‖ ^ 2 = ‖(x.fst : Matrix n n ℂ)‖ ^ 2 + ‖(x.snd : Matrix n n ℂ)‖ ^ 2 at hnorm
    change ‖(x.fst : Matrix n n ℂ) + (x.snd : Matrix n n ℂ)‖ = ‖x‖
    nlinarith [norm_nonneg ((x.fst : Matrix n n ℂ) + (x.snd : Matrix n n ℂ)),
      norm_nonneg x]

theorem adjointSumFrobenius_apply
    (x : WithLp 2 (HermitianFrobenius n × SkewFrobenius n)) :
    adjointSumFrobenius n x = (x.fst : Matrix n n ℂ) + (x.snd : Matrix n n ℂ) := rfl

/-- Orthogonal adjoint coordinates in the normal map's Euclidean entry space. -/
noncomputable def adjointSumEuclidean :
    WithLp 2 (HermitianFrobenius n × SkewFrobenius n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ ((n × n) × Fin 2) :=
  (adjointSumFrobenius n).trans (matrixFrobeniusCoordinates n n)

theorem measurePreserving_adjointSumEuclidean :
    MeasurePreserving (adjointSumEuclidean n) volume volume :=
  (adjointSumEuclidean n).measurePreserving

/-- The ordinary product measure has exactly the required normalization,
even though its ordinary product norm is not the Hilbert direct-sum norm. -/
theorem measurePreserving_adjointPairEuclidean :
    MeasurePreserving
      (fun x : HermitianFrobenius n × SkewFrobenius n =>
        matrixFrobeniusCoordinates n n ((x.1 : Matrix n n ℂ) + (x.2 : Matrix n n ℂ)))
      (volume.prod volume) volume :=
  (measurePreserving_adjointSumEuclidean n).comp
    (WithLp.volume_preserving_toLp (HermitianFrobenius n) (SkewFrobenius n))

/-- Normalized ball volume, including zero-dimensional spaces, at positive radius. -/
theorem volume_ball_eq_euclideanUnitBallVolume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball (0 : E) r) =
      ENNReal.ofReal r ^ Module.finrank ℝ E *
        euclideanUnitBallVolume (Module.finrank ℝ E) := by
  rw [Measure.addHaar_ball_of_pos volume (0 : E) hr, ENNReal.ofReal_pow hr.le]
  congr 1
  have h := (stdOrthonormalBasis ℝ E).repr.measurePreserving.measure_preimage
    (s := Metric.ball 0 1) measurableSet_ball.nullMeasurableSet
  simpa only [LinearIsometryEquiv.preimage_ball, map_zero, euclideanUnitBallVolume] using h

theorem volume_hermitian_ball (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball (0 : HermitianFrobenius n) r) =
      ENNReal.ofReal r ^ (Fintype.card n ^ 2) * euclideanUnitBallVolume (Fintype.card n ^ 2) := by
  rw [volume_ball_eq_euclideanUnitBallVolume r hr]
  congr 2 <;> exact (finrank_adjoint_matrix_spaces n).1

theorem volume_skew_ball (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball (0 : SkewFrobenius n) r) =
      ENNReal.ofReal r ^ (Fintype.card n ^ 2) * euclideanUnitBallVolume (Fintype.card n ^ 2) := by
  rw [volume_ball_eq_euclideanUnitBallVolume r hr]
  congr 2 <;> exact (finrank_adjoint_matrix_spaces n).2

/-- The chart domain expressed in ambient orthogonal Euclidean coordinates.
The Hermitian radius is s and the skew-Hermitian radius is one. -/
def adjointChartDomain (s : ℝ) : Set (EuclideanSpace ℝ ((n × n) × Fin 2)) :=
  (adjointSumEuclidean n) ''
    (WithLp.ofLp ⁻¹' (Metric.ball (0 : HermitianFrobenius n) s ×ˢ
      Metric.ball (0 : SkewFrobenius n) 1))

theorem isOpen_adjointChartDomain (s : ℝ) : IsOpen (adjointChartDomain n s) :=
  (adjointSumEuclidean n).toHomeomorph.isOpenMap _
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).preimage (WithLp.prod_continuous_ofLp 2 _ _))

theorem volume_adjointSumEuclidean_image
    (S : Set (WithLp 2 (HermitianFrobenius n × SkewFrobenius n))) :
    volume (adjointSumEuclidean n '' S) = volume S := by
  have h := (adjointSumEuclidean n).symm.measurePreserving.measure_preimage_equiv
    (f := (adjointSumEuclidean n).symm.toMeasurableEquiv) S
  convert h using 2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨(adjointSumEuclidean n).symm x, hx, (adjointSumEuclidean n).apply_symm_apply x⟩

/-- The domain volume in orthonormal coordinates. -/
theorem volume_adjointChartDomain (s : ℝ) (hs : 0 < s) :
    volume (adjointChartDomain n s) =
      euclideanUnitBallVolume (Fintype.card n ^ 2) ^ 2 *
        ENNReal.ofReal s ^ (Fintype.card n ^ 2) := by
  rw [adjointChartDomain, volume_adjointSumEuclidean_image]
  rw [(WithLp.volume_preserving_ofLp (HermitianFrobenius n) (SkewFrobenius n)).measure_preimage
    (measurableSet_ball.prod measurableSet_ball).nullMeasurableSet]
  change (volume.prod volume)
    (Metric.ball (0 : HermitianFrobenius n) s ×ˢ Metric.ball (0 : SkewFrobenius n) 1) = _
  rw [Measure.prod_prod, volume_hermitian_ball n s hs, volume_skew_ball n 1 zero_lt_one]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  ring

/-- Comparison of orthonormal-coordinate unit-ball volumes. -/
theorem euclideanUnitBallVolume_twice_le_sq (m : ℕ) :
    euclideanUnitBallVolume (2 * m) ≤ euclideanUnitBallVolume m ^ 2 := by
  let E := WithLp 2 (RealEuclidean m × RealEuclidean m)
  have hdim : Module.finrank ℝ E = 2 * m := by
    rw [(WithLp.linearEquiv 2 ℝ (RealEuclidean m × RealEuclidean m)).finrank_eq,
      Module.finrank_prod]
    simp [RealEuclidean, two_mul]
  calc
    _ = volume (Metric.ball (0 : E) 1) := by
      rw [volume_ball_eq_euclideanUnitBallVolume 1 zero_lt_one, hdim]
      simp
    _ ≤ volume (WithLp.ofLp ⁻¹'
        (Metric.ball (0 : RealEuclidean m) 1 ×ˢ Metric.ball (0 : RealEuclidean m) 1)) := by
      apply measure_mono
      intro x hx
      have hn : ‖x‖ < 1 := by simpa using hx
      exact ⟨by simpa using (WithLp.norm_fst_le (RealEuclidean m) x).trans_lt hn,
        by simpa using (WithLp.norm_snd_le (RealEuclidean m) x).trans_lt hn⟩
    _ = euclideanUnitBallVolume m ^ 2 := by
      rw [(WithLp.volume_preserving_ofLp (RealEuclidean m) (RealEuclidean m)).measure_preimage
        (measurableSet_ball.prod measurableSet_ball).nullMeasurableSet]
      change (volume.prod volume)
        (Metric.ball (0 : RealEuclidean m) 1 ×ˢ Metric.ball (0 : RealEuclidean m) 1) = _
      rw [Measure.prod_prod, pow_two]
      rfl

end NLQCLean
