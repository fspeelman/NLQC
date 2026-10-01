import NLQCLean.Approx.PolynomialWitnessThickening
import NLQCLean.Geometry.UnitaryNormalVolume
import NLQCLean.Geometry.UnitaryWitnessTube
import NLQCLean.Geometry.TransverseTubeArithmetic

/-!
# Conditional polynomial tube estimates

The sole geometric input is the explicit ordinary argument
`PolynomialImageVolumeBound`. All polynomial, radius and Jacobian data are
proved for the witness family before applying that property.
-/

namespace NLQCLean

open MeasureTheory
open scoped ENNReal

namespace ReverseBlocks

theorem witnessCoordinateBudget_ge_one {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) :
    1 ≤ witnessCoordinateBudget d K := by
  have hk : 0 < K := (Nat.mul_pos (Nat.mul_pos s.resource_pos s.messageA_pos)
    s.messageB_pos).trans_le s.footprint
  have hp : 0 < witnessCoordinateBudget d K := by unfold witnessCoordinateBudget; positivity
  omega

theorem localMotionRank_le_unitaryDimension {d : ℕ} (hd : 2 ≤ d) :
    4 * d ^ 2 - 3 ≤ d ^ 4 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have he : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  rw [he]
  have h : 4 * d ^ 2 ≤ d ^ 2 * d ^ 2 := by nlinarith
  omega

/-- Thickened image volume with the universal geometry constant displayed. -/
theorem thickenedWitness_image_volume_le {C : ℝ}
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) (hd2 : 2 ≤ d)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd c).eval '' (thickenedWitnessFormat s hd δ).source) ≤
      ENNReal.ofReal (C ^ (witnessCoordinateBudget d K + 2 * d ^ 4 + 2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((witnessCoordinateBudget d K : ℝ) + c) ^ (4 * d ^ 2 - 3) *
          (δ * witnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (4 * d ^ 2 - 3))) := by
  have hm : 0 < 2 * d ^ 4 := by positivity
  exact hGeom _ _ (by omega) (by omega) (thickenedWitnessFormat s hd δ)
    (thickenedWitnessPolynomial s hd c)
    (isCompact_thickenedWitnessFormat_source s hd δ)
    (thickenedWitnessFormat_source_radius s hd δ) _ (by positivity)
    (fun _ hz => thickenedWitnessPolynomial_jacobian_le s hd hd2 hδ hδ1 hc hz)

/-- One constant serves every dimension, budget, shape, leakage and tube radius. -/
theorem exists_witness_tube_volume_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : ReverseShape d K) (hd : 0 < d), 2 ≤ d →
      ∀ δ c : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < c →
        volume {y : RealEuclidean (2 * d ^ 4) |
          ∃ x ∈ (witnessFormat s hd δ).source,
            dist y ((coordinateOverlapPolynomial s hd).eval x) < c} ≤
        ENNReal.ofReal (C ^ (witnessCoordinateBudget d K + 2 * d ^ 4 + 2 * d ^ 4)) *
          euclideanUnitBallVolume (2 * d ^ 4) *
          ENNReal.ofReal (((witnessCoordinateBudget d K : ℝ) + c) ^ (4 * d ^ 2 - 3) *
            (δ * witnessCoordinateBudget d K + c) ^ (2 * d ^ 4 - (4 * d ^ 2 - 3))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  refine ⟨C, hC, ?_⟩
  intro d K s hd hd2 δ c hδ hδ1 hc
  exact (measure_mono ((coordinateOverlapPolynomial s hd).tube_subset_thicken_image
    (witnessFormat s hd δ) (by change 7 + 1 + 1 ≤ 20; decide) hc)).trans
      (thickenedWitness_image_volume_le hbound s hd hd2 hδ hδ1 hc.le)

/-- Normal-tube comparison with an explicit universal image-volume constant. -/
theorem witness_haar_le_transverse {C : ℝ} (hC : 1 ≤ C)
    (hGeom : PolynomialImageVolumeBoundWith C)
    {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) (hd2 : 2 ≤ d)
    {δ r ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hr' : r ≤ 1 / 2)
    (hδr : δ * witnessCoordinateBudget d K ≤ r) (hρ : ρ ≤ r)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ (witnessFormat s hd δ).source,
      dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
        ((coordinateOverlapPolynomial s hd).eval x) ≤ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (Real.exp ((144 * C ^ 4) * (witnessCoordinateBudget d K + d ^ 4)) *
        (2 * (witnessCoordinateBudget d K : ℝ)) ^ (4 * d ^ 2 - 3) *
        r ^ (d ^ 4 - (4 * d ^ 2 - 3))) := by
  let P := witnessCoordinateBudget d K
  let N := d ^ 4
  let t := 4 * d ^ 2 - 3
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast witnessCoordinateBudget_ge_one s hd
  have ht : t ≤ N := localMotionRank_le_unitaryDimension hd2
  have hC0 : 0 ≤ C := by linarith
  have hB := thickenedJacobian_le_transverse ht hP
    (by positivity : 0 ≤ δ * P) hδr hr.le hr'
  have htube : unitaryWitnessTube d r S ⊆
      (thickenedWitnessPolynomial s hd (2 * r)).eval '' (thickenedWitnessFormat s hd δ).source :=
    (unitaryWitnessTube_subset_imageTube hρ hcover).trans
      ((coordinateOverlapPolynomial s hd).tube_subset_thicken_image (witnessFormat s hd δ)
        (by change 7 + 1 + 1 ≤ 20; decide) (by positivity))
  have hupper := (unitaryHaar_witnessTube_volume_lower d hr hr' hS).trans
    ((measure_mono htube).trans (thickenedWitness_image_volume_le hGeom s hd hd2 hδ hδ1 (by positivity)))
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

/-- The polynomial witness Haar bound: one constant precedes every witness family and Borel S. -/
theorem exists_witness_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : ReverseShape d K) (hd : 0 < d), 2 ≤ d →
      ∀ δ r ρ : ℝ, 0 ≤ δ → δ ≤ 1 → 0 < r → r ≤ 1 / 2 →
        δ * witnessCoordinateBudget d K ≤ r → ρ ≤ r →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
        (∀ U ∈ S, ∃ x ∈ (witnessFormat s hd δ).source,
          dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
            ((coordinateOverlapPolynomial s hd).eval x) ≤ ρ) →
        unitaryHaar (Fin d × Fin d) S ≤
          ENNReal.ofReal (Real.exp (C * (witnessCoordinateBudget d K + d ^ 4)) *
            (C * (witnessCoordinateBudget d K : ℝ)) ^ (4 * d ^ 2 - 3) *
            (C * r) ^ (d ^ 4 - (4 * d ^ 2 - 3))) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  have hC4 : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC
  have hbig : (2 : ℝ) ≤ 144 * C ^ 4 := by linarith
  refine ⟨144 * C ^ 4, by linarith, ?_⟩
  intro d K s hd hd2 δ r ρ hδ hδ1 hr hr' hδr hρ S hS hcover
  refine (witness_haar_le_transverse hC hbound s hd hd2 hδ hδ1 hr hr' hδr hρ hS hcover).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr; nlinarith

end ReverseBlocks
end NLQCLean
