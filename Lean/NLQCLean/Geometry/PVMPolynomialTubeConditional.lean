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
theorem thickenedWitness_image_volume_le {C : ℝ}
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (hd2 : 2 ≤ d)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd hfloor c).eval '' (thickenedWitnessFormat s hd hfloor δ).source) ≤
      ENNReal.ofReal (C ^ (pvmWitnessCoordinateBudget d K + 2 * d ^ 4 + 2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((pvmWitnessCoordinateBudget d K : ℝ) + c) ^ (3 * d ^ 2 - 2) *
          (δ * pvmWitnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))) := by
  have hm : 0 < 2 * d ^ 4 := by positivity
  exact hGeom _ _ (by omega) (by omega) (thickenedWitnessFormat s hd hfloor δ)
    (thickenedWitnessPolynomial s hd hfloor c)
    (isCompact_thickenedWitnessFormat_source s hd hfloor δ)
    (thickenedWitnessFormat_source_radius s hd hfloor δ) _ (by positivity)
    (fun _ hz => thickenedWitnessPolynomial_jacobian_le s hd hfloor hd2 hδ hδ1 hc hz)

/-- One constant serves every dimension, budget, shape, leakage and tube radius. -/
theorem exists_witness_tube_volume_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K), 2 ≤ d →
      ∀ δ c : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < c →
        volume {y : RealEuclidean (2 * d ^ 4) |
          ∃ x ∈ (witnessFormat s hd hfloor δ).source,
            dist y ((coordinateOverlapPolynomial s hd hfloor).eval x) < c} ≤
        ENNReal.ofReal (C ^ (pvmWitnessCoordinateBudget d K + 2 * d ^ 4 + 2 * d ^ 4)) *
          euclideanUnitBallVolume (2 * d ^ 4) *
          ENNReal.ofReal (((pvmWitnessCoordinateBudget d K : ℝ) + c) ^ (3 * d ^ 2 - 2) *
            (δ * pvmWitnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  refine ⟨C, hC, ?_⟩
  intro d K s hd hfloor hd2 δ c hδ hδ1 hc
  exact (measure_mono ((coordinateOverlapPolynomial s hd hfloor).tube_subset_thicken_image
    (witnessFormat s hd hfloor δ) (by change 7 + 1 + 1 ≤ 20; decide) hc)).trans
      (thickenedWitness_image_volume_le hbound s hd hfloor hd2 hδ hδ1 hc.le)

/-- Normal-tube comparison with an explicit universal geometry constant. -/
theorem witness_haar_le_transverse {C : ℝ} (hC : 1 ≤ C)
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (hd2 : 2 ≤ d)
    {δ r ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hr' : r ≤ 1 / 2)
    (hδr : δ * pvmWitnessCoordinateBudget d K ≤ r) (hρ : ρ ≤ r)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor δ).source,
      dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
        ((coordinateOverlapPolynomial s hd hfloor).eval x) ≤ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (Real.exp ((144 * C ^ 4) * (pvmWitnessCoordinateBudget d K + d ^ 4)) *
        (2 * (pvmWitnessCoordinateBudget d K : ℝ)) ^ (3 * d ^ 2 - 2) *
        r ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  let P := pvmWitnessCoordinateBudget d K
  let N := d ^ 4
  let t := 3 * d ^ 2 - 2
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast one_le_coordinateBudget s hd
  have ht : t ≤ N := pvmMotionRank_le_unitaryDimension hd2
  have hC0 : 0 ≤ C := by linarith
  have hB := thickenedJacobian_le_transverse ht hP
    (by positivity : 0 ≤ δ * P) hδr hr.le hr'
  have htube : unitaryWitnessTube d r S ⊆
      (thickenedWitnessPolynomial s hd hfloor (2 * r)).eval '' (thickenedWitnessFormat s hd hfloor δ).source :=
    (unitaryWitnessTube_subset_imageTube hρ hcover).trans
      ((coordinateOverlapPolynomial s hd hfloor).tube_subset_thicken_image (witnessFormat s hd hfloor δ)
        (by change 7 + 1 + 1 ≤ 20; decide) (by positivity))
  have hupper := (unitaryHaar_witnessTube_volume_lower d hr hr' hS).trans
    ((measure_mono htube).trans (thickenedWitness_image_volume_le hGeom s hd hfloor hd2 hδ hδ1 (by positivity)))
  have hnormalized : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * euclideanUnitBallVolume N ^ 2 *
      ENNReal.ofReal r ^ N * unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (C ^ (P + 4 * N)) * euclideanUnitBallVolume N ^ 2 *
        ENNReal.ofReal (r ^ N * ((2 * (P : ℝ)) ^ t * 9 ^ N * r ^ (N - t))) := by
    refine hupper.trans ?_
    have hexp : P + 2 * N + 2 * N = P + 4 * N := by omega
    change ENNReal.ofReal (C ^ (P + 2 * N + 2 * N)) * euclideanUnitBallVolume (2 * N) *
      ENNReal.ofReal (((P : ℝ) + 2 * r) ^ t * (δ * P + 2 * r) ^ (2 * N - t)) ≤ _
    rw [hexp]
    exact mul_le_mul (mul_le_mul_right (euclideanUnitBallVolume_twice_le_sq N) _)
      (ENNReal.ofReal_le_ofReal hB) zero_le zero_le
  have hcancel := cancel_normal_tube_volume hr (pow_nonneg hC0 _) hnormalized
  refine hcancel.trans (ENNReal.ofReal_le_ofReal ?_)
  change 16 ^ N * C ^ (P + 4 * N) * ((2 * (P : ℝ)) ^ t * 9 ^ N * r ^ (N - t)) ≤ _
  calc
    _ = (16 ^ N * C ^ (P + 4 * N) * 9 ^ N) * (2 * (P : ℝ)) ^ t * r ^ (N - t) := by ring
    _ ≤ Real.exp ((144 * C ^ 4) * (P + N)) * (2 * (P : ℝ)) ^ t * r ^ (N - t) := by
      gcongr
      exact transverse_fixed_base_le_exp hC P N
    _ = _ := by simp only [P, N, t, Nat.cast_pow]

/-- One Haar constant precedes every witness family and Borel target set. -/
theorem exists_witness_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K), 2 ≤ d →
      ∀ δ r ρ : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < r → r ≤ 1 / 2 →
        δ * pvmWitnessCoordinateBudget d K ≤ r → ρ ≤ r →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
        (∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor δ).source,
          dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
            ((coordinateOverlapPolynomial s hd hfloor).eval x) ≤ ρ) →
        unitaryHaar (Fin d × Fin d) S ≤
          ENNReal.ofReal (Real.exp (C * (pvmWitnessCoordinateBudget d K + d ^ 4)) *
            (C * (pvmWitnessCoordinateBudget d K : ℝ)) ^ (3 * d ^ 2 - 2) *
            (C * r) ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  have hC4 : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC
  have hbig : (2 : ℝ) ≤ 144 * C ^ 4 := by linarith
  refine ⟨144 * C ^ 4, by linarith, ?_⟩
  intro d K s hd hfloor hd2 δ r ρ hδ hδ1 hr hr' hδr hρ S hS hcover
  refine (witness_haar_le_transverse hC hbound s hd hfloor hd2 hδ hδ1 hr hr' hδr hρ hS hcover).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr; nlinarith

end PVMReverseBlocks
end NLQCLean
