import NLQCLean.Approx.PVMPolynomialWitnessThickening
import NLQCLean.Geometry.UnitaryNormalVolume
import NLQCLean.Geometry.UnitaryWitnessTube
import NLQCLean.Geometry.TransverseTubeArithmetic

/-!
# Conditional PVM polynomial tube estimates

The sole geometric input is the explicit ordinary argument
`PolynomialImageVolumeBound`. All polynomial, radius and Jacobian data are
proved for the witness family before applying that property.
-/

namespace NLQCLean

open MeasureTheory
open scoped ENNReal

namespace PVMReverseBlocks

theorem pvmMotionRank_le_unitaryDimension {d : ℕ} (hd : 2 ≤ d) :
    3 * d ^ 2 - 2 ≤ d ^ 4 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have he : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  rw [he]
  have h : 4 * d ^ 2 ≤ d ^ 2 * d ^ 2 := by nlinarith
  omega

/-- Thickened image volume with the geometry constant displayed. -/
theorem thickenedWitness_image_volume_le_of_budget {C : ℝ}
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {B : ℕ} (hB : PVMReverseShape.AdmissibleBudget s B) (hd2 : 2 ≤ d)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd hfloor hB c).eval '' (thickenedWitnessFormat s hd hfloor hB δ).source) ≤
      ENNReal.ofReal (C ^ (B + 2 * d ^ 4 + 2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((B : ℝ) + c) ^ (3 * d ^ 2 - 2) *
          (δ * B + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))) := by
  have hm : 0 < 2 * d ^ 4 := by positivity
  exact hGeom _ _ (by omega) (by omega) (thickenedWitnessFormat s hd hfloor hB δ)
    (thickenedWitnessPolynomial s hd hfloor hB c)
    (isCompact_thickenedWitnessFormat_source s hd hfloor hB δ)
    (thickenedWitnessFormat_source_radius s hd hfloor hB δ) _ (by positivity)
    (fun _ hz => thickenedWitnessPolynomial_jacobian_le s hd hfloor hB hd2 hδ hδ1 hc hz)

/-- One constant serves every dimension, budget, shape, leakage and tube radius. -/
theorem exists_witness_tube_volume_constant_of_budget (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (B : ℕ)
        (hB : PVMReverseShape.AdmissibleBudget s B), 2 ≤ d →
      ∀ δ c : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < c →
        volume {y : RealEuclidean (2 * d ^ 4) |
          ∃ x ∈ (witnessFormat s hd hfloor hB δ).source,
            dist y ((coordinateOverlapPolynomial s hd hfloor hB).eval x) < c} ≤
        ENNReal.ofReal (C ^ (B + 2 * d ^ 4 + 2 * d ^ 4)) *
          euclideanUnitBallVolume (2 * d ^ 4) *
          ENNReal.ofReal (((B : ℝ) + c) ^ (3 * d ^ 2 - 2) *
            (δ * B + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  refine ⟨C, hC, ?_⟩
  intro d K s hd hfloor B hB hd2 δ c hδ hδ1 hc
  exact (measure_mono ((coordinateOverlapPolynomial s hd hfloor hB).tube_subset_thicken_image
    (witnessFormat s hd hfloor hB δ) (by change 7 + 1 + 1 ≤ 20; decide) hc)).trans
      (thickenedWitness_image_volume_le_of_budget hbound s hd hfloor hB hd2 hδ hδ1 hc.le)

/-- Normal-tube comparison for any image-volume factor `V` of the thickened family:
`μ(S) ≤ 16ᴺ · V · (2P)^t 9ᴺ r^(N−t)`. -/
theorem witness_haar_le_transverse_of_volume {V : ℝ} (hV : 0 ≤ V)
    {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {B : ℕ}
    (hB : PVMReverseShape.AdmissibleBudget s B)
    (hvol : ∀ δ c : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ c →
      volume ((thickenedWitnessPolynomial s hd hfloor hB c).eval ''
          (thickenedWitnessFormat s hd hfloor hB δ).source) ≤
        ENNReal.ofReal V * euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((B : ℝ) + c) ^ (3 * d ^ 2 - 2) *
          (δ * B + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))))
    (hd2 : 2 ≤ d)
    {δ r ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hr' : r ≤ 1 / 2)
    (hδr : δ * B ≤ r) (hρ : ρ ≤ r)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor hB δ).source,
      dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
        ((coordinateOverlapPolynomial s hd hfloor hB).eval x) ≤ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (16 ^ (d ^ 4) * V *
        ((2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) * r ^ (d ^ 4 - (3 * d ^ 2 - 2)))) := by
  let P := B
  let N := d ^ 4
  let t := 3 * d ^ 2 - 2
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast hB.one_le
  have ht : t ≤ N := pvmMotionRank_le_unitaryDimension hd2
  have hJac := thickenedJacobian_le_transverse ht hP
    (by positivity : 0 ≤ δ * P) hδr hr.le hr'
  have htube : unitaryWitnessTube d r S ⊆
      (thickenedWitnessPolynomial s hd hfloor hB (2 * r)).eval ''
        (thickenedWitnessFormat s hd hfloor hB δ).source :=
    (unitaryWitnessTube_subset_imageTube hρ hcover).trans
      ((coordinateOverlapPolynomial s hd hfloor hB).tube_subset_thicken_image
        (witnessFormat s hd hfloor hB δ) (by change 7 + 1 + 1 ≤ 20; decide) (by positivity))
  have hupper := (unitaryHaar_witnessTube_volume_lower d hr hr' hS).trans
    ((measure_mono htube).trans (hvol δ (2 * r) hδ hδ1 (by positivity)))
  have hnormalized : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * euclideanUnitBallVolume N ^ 2 *
      ENNReal.ofReal r ^ N * unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal V * euclideanUnitBallVolume N ^ 2 *
        ENNReal.ofReal (r ^ N * ((2 * (P : ℝ)) ^ t * 9 ^ N * r ^ (N - t))) := by
    refine hupper.trans ?_
    change ENNReal.ofReal V * euclideanUnitBallVolume (2 * N) *
      ENNReal.ofReal (((P : ℝ) + 2 * r) ^ t * (δ * P + 2 * r) ^ (2 * N - t)) ≤ _
    exact mul_le_mul (mul_le_mul_right (euclideanUnitBallVolume_twice_le_sq N) _)
      (ENNReal.ofReal_le_ofReal hJac) zero_le zero_le
  exact (cancel_normal_tube_volume hr hV hnormalized).trans le_rfl

/-- Normal-tube comparison with an explicit universal geometry constant. -/
theorem witness_haar_le_transverse_of_budget {C : ℝ} (hC : 1 ≤ C)
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {B : ℕ} (hB : PVMReverseShape.AdmissibleBudget s B) (hd2 : 2 ≤ d)
    {δ r ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hr' : r ≤ 1 / 2)
    (hδr : δ * B ≤ r) (hρ : ρ ≤ r)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor hB δ).source,
      dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
        ((coordinateOverlapPolynomial s hd hfloor hB).eval x) ≤ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (Real.exp ((144 * C ^ 4) * (B + d ^ 4)) *
        (2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) *
        r ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  have hC0 : 0 ≤ C := by linarith
  have hexp : B + 2 * d ^ 4 + 2 * d ^ 4 = B + 4 * d ^ 4 := by omega
  refine (witness_haar_le_transverse_of_volume (V := C ^ (B + 4 * d ^ 4)) (pow_nonneg hC0 _)
    s hd hfloor hB (fun δ c hδ hδ1 hc => by
      rw [← hexp]; exact thickenedWitness_image_volume_le_of_budget hGeom s hd hfloor hB hd2 hδ hδ1 hc)
    hd2 hδ hδ1 hr hr' hδr hρ hS hcover).trans (ENNReal.ofReal_le_ofReal ?_)
  have hbase := transverse_fixed_base_le_exp hC B (d ^ 4)
  push_cast at hbase
  have hBr : 0 ≤ (2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * r ^ (d ^ 4 - (3 * d ^ 2 - 2)) := by positivity
  calc 16 ^ (d ^ 4) * C ^ (B + 4 * d ^ 4) *
        ((2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) * r ^ (d ^ 4 - (3 * d ^ 2 - 2)))
      = (16 ^ (d ^ 4) * C ^ (B + 4 * d ^ 4) * 9 ^ (d ^ 4)) *
        ((2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * r ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by ring
    _ ≤ Real.exp ((144 * C ^ 4) * (B + d ^ 4)) *
        ((2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * r ^ (d ^ 4 - (3 * d ^ 2 - 2))) :=
        mul_le_mul_of_nonneg_right hbase hBr
    _ = _ := by ring

/-- One Haar constant precedes every witness family and Borel target set. -/
theorem exists_witness_haar_constant_of_budget (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (B : ℕ)
        (hB : PVMReverseShape.AdmissibleBudget s B), 2 ≤ d →
      ∀ δ r ρ : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < r → r ≤ 1 / 2 →
        δ * B ≤ r → ρ ≤ r →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
        (∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor hB δ).source,
          dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
            ((coordinateOverlapPolynomial s hd hfloor hB).eval x) ≤ ρ) →
        unitaryHaar (Fin d × Fin d) S ≤
          ENNReal.ofReal (Real.exp (C * (B + d ^ 4)) *
            (C * (B : ℝ)) ^ (3 * d ^ 2 - 2) *
            (C * r) ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  have hC4 : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC
  have hbig : (2 : ℝ) ≤ 144 * C ^ 4 := by linarith
  refine ⟨144 * C ^ 4, by linarith, ?_⟩
  intro d K s hd hfloor B hB hd2 δ r ρ hδ hδ1 hr hr' hδr hρ S hS hcover
  refine (witness_haar_le_transverse_of_budget hC hbound s hd hfloor hB hd2 hδ hδ1 hr hr' hδr hρ hS hcover).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr; nlinarith

/-- One Haar constant precedes every witness family and Borel target set. -/
theorem exists_witness_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K), 2 ≤ d →
      ∀ δ r ρ : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < r → r ≤ 1 / 2 →
        δ * pvmWitnessCoordinateBudget d K ≤ r → ρ ≤ r →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
        (∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor) δ).source,
          dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
            ((coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval x) ≤ ρ) →
        unitaryHaar (Fin d × Fin d) S ≤
          ENNReal.ofReal (Real.exp (C * (pvmWitnessCoordinateBudget d K + d ^ 4)) *
            (C * (pvmWitnessCoordinateBudget d K : ℝ)) ^ (3 * d ^ 2 - 2) *
            (C * r) ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_witness_haar_constant_of_budget hGeom
  exact ⟨C, hC, fun d K s hd hfloor =>
    hbound d K s hd hfloor _ (PVMReverseShape.admissibleBudget_full s hd hfloor)⟩

end PVMReverseBlocks
end NLQCLean
