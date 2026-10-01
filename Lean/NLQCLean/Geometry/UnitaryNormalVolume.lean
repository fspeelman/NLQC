import NLQCLean.Geometry.UnitaryCayleyNormal
import NLQCLean.Geometry.ExpandingDeterminant
import NLQCLean.Geometry.UnitaryNormalMeasure
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Unconditional normal-volume and Haar tube lower bounds

The normal Cayley chart has full real Jacobian at least 16^(-N).
Equal-dimensional change of variables gives a lower bound for the total
normal-image mass. Invariance then gives the Haar tube comparison.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The chart Jacobian, with N equal to the square of the matrix size. -/
theorem normalCayleyEuclidean_det_lower
    (z : EuclideanSpace ℝ ((n × n) × Fin 2))
    (hz : ‖normalSkewCoordinate n z‖ < 1) (hQ : ‖normalHermitianCoordinate n z‖ ≤ 1 / 2) :
    (1 / 16 : ℝ) ^ (Fintype.card n ^ 2) ≤ |(normalCayleyEuclideanDerivative n z).det| := by
  have h := pow_le_abs_det_of_expansion (normalCayleyEuclideanDerivative n z).toLinearMap
    (by norm_num : (0 : ℝ) < 1 / 4)
    (fun v => quarter_norm_le_normalCayleyEuclideanDerivative z v hz hQ)
  have hd : Module.finrank ℝ (EuclideanSpace ℝ ((n × n) × Fin 2)) = 2 * (Fintype.card n ^ 2) := by
    simp [finrank_euclideanSpace, Fintype.card_prod, pow_two, mul_comm]
  rw [hd, pow_mul] at h
  norm_num at h
  exact h

/-- The normalized universal lower factor for the chart volume. -/
noncomputable def normalVolumeLowerFactor (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) *
    euclideanUnitBallVolume (Fintype.card n ^ 2) ^ 2 * ENNReal.ofReal s ^ (Fintype.card n ^ 2)

theorem normalVolumeLowerFactor_le_chart_image {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    normalVolumeLowerFactor n s ≤
      volume (normalCayleyEuclidean n '' adjointChartDomain n s) := by
  have hdom := (isOpen_adjointChartDomain n s).measurableSet
  have hcv := lintegral_abs_det_fderiv_eq_addHaar_image volume hdom
    (fun z hz => (hasFDerivAt_normalCayleyEuclidean z
      ((mem_adjointChartDomain_iff s z).mp hz).2).hasFDerivWithinAt)
    (normalCayleyEuclidean_injectiveOn s hs')
  calc
    _ = ∫⁻ _z in adjointChartDomain n s,
        ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_adjointChartDomain n s hs]
      unfold normalVolumeLowerFactor
      ring
    _ ≤ ∫⁻ z in adjointChartDomain n s,
        ENNReal.ofReal |(normalCayleyEuclideanDerivative n z).det| := by
      apply setLIntegral_mono' hdom
      intro z hz
      obtain ⟨hQ, hA⟩ := (mem_adjointChartDomain_iff s z).mp hz
      exact ENNReal.ofReal_le_ofReal (normalCayleyEuclidean_det_lower n z hA (hQ.le.trans hs'))
    _ = _ := hcv

/-- The Cayley normal image is contained in the normal-image measure. -/
theorem chart_image_volume_le_unitaryNormalMeasure {s : ℝ} (hs : s ≤ 1 / 2) :
    volume (normalCayleyEuclidean n '' adjointChartDomain n s) ≤
      unitaryNormalMeasure n s Set.univ := by
  rw [unitaryNormalMeasure_apply_of_le_half n hs MeasurableSet.univ]
  apply measure_mono
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hQ, hA⟩ := (mem_adjointChartDomain_iff s z).mp hz
  let U : Matrix.unitaryGroup n ℂ := ⟨matrixCayley (normalSkewCoordinate n z),
    Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_matrixCayley _
      (normalSkewCoordinate_adjoint z) (isUnit_one_sub_matrix_of_norm_lt_one _ hA))⟩
  exact ⟨U, Set.mem_univ _, normalHermitianCoordinate n z,
    normalHermitianCoordinate_adjoint z, hQ, rfl⟩

/-- A lower bound for the total normal-image mass. -/
theorem normalVolumeLowerFactor_le_total {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    normalVolumeLowerFactor n s ≤ unitaryNormalMeasure n s Set.univ :=
  (normalVolumeLowerFactor_le_chart_image n hs hs').trans
    (chart_image_volume_le_unitaryNormalMeasure n hs')

omit [DecidableEq n] in
theorem normalVolumeLowerFactor_pos {s : ℝ} (hs : 0 < s) :
    0 < normalVolumeLowerFactor n s := by
  have hball : 0 < euclideanUnitBallVolume (Fintype.card n ^ 2) :=
    Metric.measure_ball_pos volume (0 : RealEuclidean (Fintype.card n ^ 2)) zero_lt_one
  unfold normalVolumeLowerFactor
  positivity

/-- The invariant normal-image measure has strictly positive total mass. -/
theorem unitaryNormalMeasure_total_pos {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    0 < unitaryNormalMeasure n s Set.univ :=
  (normalVolumeLowerFactor_pos n hs).trans_le (normalVolumeLowerFactor_le_total n hs hs')

/-- The open Frobenius s-tube around a set of unitaries, in real matrix-entry coordinates. -/
def unitaryFrobeniusTube (s : ℝ) (S : Set (Matrix.unitaryGroup n ℂ)) :
    Set (EuclideanSpace ℝ ((n × n) × Fin 2)) :=
  {y | ∃ U ∈ S, dist y (matrixFrobeniusCoordinates n n (U : Matrix n n ℂ)) < s}

theorem isOpen_unitaryFrobeniusTube (s : ℝ) (S : Set (Matrix.unitaryGroup n ℂ)) :
    IsOpen (unitaryFrobeniusTube n s S) := by
  have he : unitaryFrobeniusTube n s S =
      ⋃ U ∈ S, Metric.ball (matrixFrobeniusCoordinates n n (U : Matrix n n ℂ)) s := by
    ext y
    simp [unitaryFrobeniusTube, Metric.mem_ball]
  rw [he]
  exact isOpen_iUnion fun U => isOpen_iUnion fun _ => Metric.isOpen_ball

theorem normalImage_subset_unitaryFrobeniusTube (s : ℝ) (S : Set (Matrix.unitaryGroup n ℂ)) :
    normalEuclideanMap n '' {z : UnitaryNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s} ⊆
      unitaryFrobeniusTube n s S := by
  rintro y ⟨z, hz, rfl⟩
  refine ⟨z.1, hz.1, ?_⟩
  rw [dist_eq_norm, norm_normalEuclideanMap_sub]
  exact hz.2

/-- The unconditional normal-tube/Haar comparison in normalized Euclidean volume. -/
theorem unitaryHaar_tube_volume_lower {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S) :
    normalVolumeLowerFactor n s * unitaryHaar n S ≤ volume (unitaryFrobeniusTube n s S) := by
  calc
    _ ≤ unitaryNormalMeasure n s Set.univ * unitaryHaar n S :=
      mul_le_mul_left (normalVolumeLowerFactor_le_total n hs hs') _
    _ = volume (normalEuclideanMap n ''
        {z : UnitaryNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) :=
      (normalImageVolume_eq_total_mul_haar n s hS).symm
    _ ≤ _ := measure_mono (normalImage_subset_unitaryFrobeniusTube n s S)

/-- Expanded source-facing form: N=(card n)^2, and no geometric input occurs. -/
theorem unitaryHaar_tube_volume_lower_explicit {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S) :
    ENNReal.ofReal ((1 / 16 : ℝ) ^ (Fintype.card n ^ 2)) *
      euclideanUnitBallVolume (Fintype.card n ^ 2) ^ 2 *
      ENNReal.ofReal s ^ (Fintype.card n ^ 2) * unitaryHaar n S ≤
        volume (unitaryFrobeniusTube n s S) :=
  unitaryHaar_tube_volume_lower n hs hs' hS

end NLQCLean
