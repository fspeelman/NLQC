import NLQCLean.Geometry.StrongWitnessBarrierVolume
import NLQCLean.Geometry.PVMPolynomialTubeConditional

/-!
# The PVM witness tube with the actual witness degrees

The thickened PVM witness source has seven equations of degree at most `12`, the leakage
inequality of degree at most `12` and the unit-ball inequality of degree `2`. Its barrier
polynomials therefore have degree at most `40`, and the thickened overlap map has degree at most
`18`. The barrier route with `D = 40` gives the image-volume factor
`2^(P+2N) · 82^(P+4N) · √10^(2N)`, so that

  `μ(S) ≤ 16ᴺ · 2^(P+2N) · 82^(P+4N) · √10^(2N) · (2P)^t 9ᴺ r^(N−t)`,

with `t = 3d² − 2`.
-/

namespace NLQCLean

open MeasureTheory MvPolynomial
open scoped ENNReal

namespace PVMReverseBlocks

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ}
  (hP : PVMReverseShape.AdmissibleBudget s P)

theorem thickenedWitnessFormat_inequalities_degree_sum (δ : ℝ) :
    ∑ j, ((thickenedWitnessFormat s hd hfloor hP δ).inequalities j).totalDegree ≤ 14 := by
  have hw : ∑ j, ((witnessFormat s hd hfloor hP δ).inequalities j).totalDegree ≤ 12 := by
    have hc : (witnessFormat s hd hfloor hP δ).numInequalities = 1 := rfl
    have hle := Finset.sum_le_card_nsmul
      (Finset.univ : Finset (Fin (witnessFormat s hd hfloor hP δ).numInequalities))
      (fun j => ((witnessFormat s hd hfloor hP δ).inequalities j).totalDegree) 12 (fun j _ =>
        (show (Classical.choose (polynomialDegree_witnessInequality s hd hfloor hP δ)).totalDegree
          ≤ 12 from (Classical.choose_spec (polynomialDegree_witnessInequality s hd hfloor hP δ)).1))
    simpa [Finset.card_univ, Fintype.card_fin, hc] using hle
  exact (witnessFormat s hd hfloor hP δ).thicken_inequalities_degree_sum _ _ hw

theorem thickenedWitnessFormat_barrier_degree (δ t : ℝ) :
    ((thickenedWitnessFormat s hd hfloor hP δ).barrier t).totalDegree ≤ 40 :=
  (thickenedWitnessFormat s hd hfloor hP δ).totalDegree_barrier_le_of
    (thickenedWitnessFormat_equations_degree s hd hfloor hP δ)
    (thickenedWitnessFormat_inequalities_degree_sum s hd hfloor hP δ) t

/-- The barrier image-volume bound for the thickened PVM family at the actual degrees. -/
theorem thickenedWitness_image_volume_le_barrier (hd2 : 2 ≤ d) {δ c : ℝ} (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd hfloor hP c).eval ''
        (thickenedWitnessFormat s hd hfloor hP δ).source) ≤
      ENNReal.ofReal ((((2 ^ (P + 2 * d ^ 4) * 82 ^ (P + 4 * d ^ 4) : ℕ)) : ℝ) *
          Real.sqrt 10 ^ (2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((P : ℝ) + c) ^ (3 * d ^ 2 - 2) *
          (δ * P + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2))) := by
  have hnat : 2 ^ (P + 2 * d ^ 4) * (2 * 40 + 2) ^ (P + 2 * d ^ 4 + 2 * d ^ 4) =
      2 ^ (P + 2 * d ^ 4) * 82 ^ (P + 4 * d ^ 4) := by
    congr 2; ring
  have h := volume_image_le_of_barrier_degree (D := 40) (thickenedWitnessFormat s hd hfloor hP δ)
    (thickenedWitnessPolynomial s hd hfloor hP c) (thickenedWitnessFormat_source_radius s hd hfloor hP δ)
    (fun k => (thickenedWitnessPolynomial_degree s hd hfloor hP c k).trans (by norm_num))
    (thickenedWitnessFormat_barrier_degree s hd hfloor hP δ)
    (B := ((P : ℝ) + c) ^ (3 * d ^ 2 - 2) * (δ * P + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2)))
    (by positivity)
    (fun _ hz => thickenedWitnessPolynomial_jacobian_le s hd hfloor hP hd2 hδ hδ1 hc hz)
  rwa [hnat] at h

/-- The PVM tube estimate with the barrier image-volume factor at the actual degrees. -/
theorem witness_haar_le_barrier (hd2 : 2 ≤ d)
    {δ r ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hr' : r ≤ 1 / 2)
    (hδr : δ * P ≤ r) (hρ : ρ ≤ r)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ (witnessFormat s hd hfloor hP δ).source,
      dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
        ((coordinateOverlapPolynomial s hd hfloor hP).eval x) ≤ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (16 ^ (d ^ 4) * ((((2 ^ (P + 2 * d ^ 4) * 82 ^ (P + 4 * d ^ 4) : ℕ)) : ℝ) *
          Real.sqrt 10 ^ (2 * d ^ 4)) *
        ((2 * (P : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) * r ^ (d ^ 4 - (3 * d ^ 2 - 2)))) :=
  witness_haar_le_transverse_of_volume (by positivity) s hd hfloor hP
    (fun _ _ hδ hδ1 hc => thickenedWitness_image_volume_le_barrier s hd hfloor hP hd2 hδ hδ1 hc)
    hd2 hδ hδ1 hr hr' hδr hρ hS hcover

end PVMReverseBlocks

end NLQCLean
