import NLQCLean.ImageVolume.PolynomialImageVolume
import NLQCLean.Geometry.StrongPolynomialTubeConditional

/-!
# The slim witness tube with the actual witness degrees

The thickened slim source has seven equations of degree at most `12`, the leakage
inequality of degree at most `12` and the unit-ball inequality of degree `2`, so its barrier
polynomials have degree at most `2·12 + 14 + 2 = 40`; the thickened overlap map has degree at
most `18`. The barrier route with `D = 40` gives the image-volume factor

  `2^(P+2N) · 82^(P+4N) · √10^(2N)`,  `P = slimCoordinateBudget K`, `N = d⁴`,

in place of `35248^(P+4N)`, and the strong tube estimate becomes

  `μ(S) ≤ 4 · 1024ᴺ · 9ᴺ · 2^(P+2N) · 82^(P+4N) · 10ᴺ · (Λ + 2u)^b u^(N−b)`.
-/

namespace NLQCLean

open MeasureTheory MvPolynomial
open scoped ENNReal

theorem PolynomialBasicClosedFormat.thicken_inequalities_degree_sum {a : ℕ}
    (F : PolynomialBasicClosedFormat a) (m : ℕ) (hcount) {g : ℕ}
    (hg : ∑ j, (F.inequalities j).totalDegree ≤ g) :
    ∑ j, ((F.thicken m hcount).inequalities j).totalDegree ≤ g + 2 := by
  change ∑ j : Fin (F.numInequalities + 1), (Fin.cases (thickeningBallPolynomial a m)
    (fun i => rename (Fin.castAdd m) (F.inequalities i)) j :
      MvPolynomial (Fin (a + m)) ℝ).totalDegree ≤ g + 2
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have h1 := thickeningBallPolynomial_degree a m
  have h2 : ∑ i, (rename (Fin.castAdd m) (F.inequalities i)).totalDegree ≤
      ∑ i, (F.inequalities i).totalDegree :=
    Finset.sum_le_sum fun i _ => totalDegree_rename_le _ _
  omega

namespace SlimReverseBlocks

variable {d K : ℕ} (s : SlimReverseShape d K) (hd : 2 ≤ d)

theorem thickenedWitnessFormat_equations_degree (δ : ℝ) (i) :
    ((thickenedWitnessFormat s hd δ).equations i).totalDegree ≤ 12 :=
  (totalDegree_rename_le _ _).trans
    (Classical.choose_spec (polynomialDegree_witnessEquations s hd i)).1

theorem thickenedWitnessFormat_inequalities_degree_sum (δ : ℝ) :
    ∑ j, ((thickenedWitnessFormat s hd δ).inequalities j).totalDegree ≤ 14 := by
  have hw : ∑ j, ((witnessFormat s hd δ).inequalities j).totalDegree ≤ 12 := by
    have hc : (witnessFormat s hd δ).numInequalities = 1 := rfl
    have hle := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (witnessFormat s hd δ).numInequalities))
      (fun j => ((witnessFormat s hd δ).inequalities j).totalDegree) 12 (fun j _ =>
        (show (Classical.choose (polynomialDegree_witnessInequality s hd δ)).totalDegree ≤ 12 from
          (Classical.choose_spec (polynomialDegree_witnessInequality s hd δ)).1))
    simpa [Finset.card_univ, Fintype.card_fin, hc] using hle
  exact (witnessFormat s hd δ).thicken_inequalities_degree_sum _ _ hw

theorem thickenedWitnessFormat_barrier_degree (δ t : ℝ) :
    ((thickenedWitnessFormat s hd δ).barrier t).totalDegree ≤ 40 :=
  (thickenedWitnessFormat s hd δ).totalDegree_barrier_le_of
    (thickenedWitnessFormat_equations_degree s hd δ)
    (thickenedWitnessFormat_inequalities_degree_sum s hd δ) t

/-- The barrier image-volume bound for the thickened slim family at the actual degrees. -/
theorem strong_thickenedWitness_image_volume_le_barrier {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd c).eval '' (thickenedWitnessFormat s hd δ).source) ≤
      ENNReal.ofReal ((((2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
          82 ^ (slimCoordinateBudget K + 4 * d ^ 4) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((4 + 32 * δ) * Real.sqrt K / d + c) ^ strongUncontrolledRank d *
          (32 * δ * Real.sqrt K / d + c) ^ (2 * d ^ 4 - strongUncontrolledRank d)) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hsq := Real.sqrt_nonneg (K : ℝ)
  have hnat : 2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
      (2 * 40 + 2) ^ (slimCoordinateBudget K + 2 * d ^ 4 + 2 * d ^ 4) =
      2 ^ (slimCoordinateBudget K + 2 * d ^ 4) * 82 ^ (slimCoordinateBudget K + 4 * d ^ 4) := by
    congr 2; ring
  have h := volume_image_le_of_barrier_degree (D := 40) (thickenedWitnessFormat s hd δ)
    (thickenedWitnessPolynomial s hd c) (thickenedWitnessFormat_source_radius s hd δ)
    (fun k => (thickenedWitnessPolynomial_degree s hd c k).trans (by norm_num))
    (thickenedWitnessFormat_barrier_degree s hd δ) (B := ((4 + 32 * δ) * Real.sqrt K / d + c) ^
      strongUncontrolledRank d * (32 * δ * Real.sqrt K / d + c) ^
        (2 * d ^ 4 - strongUncontrolledRank d)) (by positivity)
    (fun z hz => by
      rw [(hasFDerivAt_thickenedWitnessPolynomial s hd c z).fderiv]
      have hx := (((witnessFormat s hd δ).mem_thicken_source _ z).mp hz).1
      obtain ⟨T, R, hdec, hrank, hnorm, hR⟩ := witnessFormat_sharp_rank_error s hd hδ hx
      exact topRealJacobian_thickenedLinearMap_le _ T R hdec (by positivity)
        (by rw [div_le_div_iff_of_pos_right hdR]; nlinarith)
        hc (hnorm.trans (by rw [div_le_div_iff_of_pos_right hdR]; nlinarith)) hR hrank
        (strongUncontrolledRank_le_two_mul hd))
  rwa [hnat] at h

/-- The strong tube estimate with the barrier image-volume factor at the actual degrees. -/
theorem strong_witness_haar_le_barrier {δ ρ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u) (hu' : u ≤ 1 / 64)
    (hlam : 32 * δ * Real.sqrt K / d ≤ u) (hρ : ρ ≤ u)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : S ⊆ witnessTargets s hd δ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal ((4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) *
        ((((2 ^ (slimCoordinateBudget K + 2 * d ^ 4) *
          82 ^ (slimCoordinateBudget K + 4 * d ^ 4) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * d ^ 4))) *
        (((4 + 32 * δ) * Real.sqrt K / d + 2 * u) ^ strongUncontrolledRank d *
        u ^ (d ^ 4 - strongUncontrolledRank d))) :=
  strong_witness_haar_le_of_volume s hd (by positivity)
    (fun _ _ hδ hc => strong_thickenedWitness_image_volume_le_barrier s hd hδ hc)
    hδ hu hu' hlam hρ hS hcover

end SlimReverseBlocks

end NLQCLean
