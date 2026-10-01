import NLQCLean.Bounds.StrongHaarArithmetic
import NLQCLean.Bounds.StrongUnitaryTargets
import NLQCLean.Geometry.StrongPolynomialTubeConditional
import NLQCLean.Geometry.PolynomialImageVolumeFourInputs
import NLQCLean.Models.MixedReachability

/-!
# The restricted strong Haar bound over the full error range

For `d ≥ 2`, `K ≥ D/2` and `0 < e ≤ 1/2`,

  `μ_d(S_d ∩ Reach(d,K,e)) ≤ min 1 (exp(C K²) e^(N/16))`

for pure and finite-mixed score reachability, and the same for the Haar outer measure of the
diamond-reachable sets. In the small-radius regime, at most `K³` compact slim
target families and the strong tube estimate apply; otherwise the right side is at least one.
Mixed score reachability equals pure reachability; diamond transfers by inclusion. The
estimate is claimed only on `S_d ∩ Reach`, never for all targets.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- Near-SWAP score Haar bound from the polynomial image-volume property. -/
theorem exists_strongRestrictedHaarBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_strong_witness_haar_constant hGeom
  refine ⟨68 * C₀ + 21, by linarith, ?_⟩
  intro d K hd hK e he he2
  have hpure : unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
      min 1 (ENNReal.ofReal (Real.exp ((68 * C₀ + 21) * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16))) := by
    refine le_min prob_le_one ?_
    by_cases hcase : e ≤ 1 / 16 ∧
        32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) ≤ 1 / 64
    · obtain ⟨he16, hu⟩ := hcase
      have hd0 : 0 < d := by omega
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hsK := sqrt_div_sq_le_sqrt_one_add (K := K) hd0
      have hx0 : (0 : ℝ) ≤ K / (d : ℝ) ^ 2 := by positivity
      have hw1 : 1 ≤ Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
      have hδ0 : 0 < Real.sqrt (18 * e) := Real.sqrt_pos.mpr (by positivity)
      have hu0 : 0 < 32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by positivity
      have hlam : 32 * Real.sqrt (18 * e) * Real.sqrt K / d ≤
          32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hsK (by positivity)
      have hρ : Real.sqrt (18 * e) ≤ 32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hw1 hδ0.le]
      have hcover := swapNeighborhood_inter_pureReachable_subset_slimWitnessTargets (K := K) hd he.le he16
      have hshape : ∀ s : SlimReverseShape d K,
          unitaryHaar (Fin d × Fin d)
            (SlimReverseBlocks.witnessTargets s hd (Real.sqrt (18 * e)) (Real.sqrt (18 * e))) ≤
          ENNReal.ofReal (Real.exp (C₀ * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
            ((4 + 32 * Real.sqrt (18 * e)) * Real.sqrt K / d +
              2 * (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
                strongUncontrolledRank d *
            (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
              (d ^ 4 - strongUncontrolledRank d)) := fun s =>
        hbound d K s hd _ _ _ hδ0.le hu0 hu hlam hρ _
          (SlimReverseBlocks.measurableSet_witnessTargets s hd _ _) subset_rfl
      have hP : ((slimCoordinateBudget K : ℕ) : ℝ) = 64 * (K : ℝ) ^ 2 := by
        simp [slimCoordinateBudget]
      have hcard : (Fintype.card (SlimReverseShape d K) : ℝ≥0∞) ≤ ENNReal.ofReal ((K : ℝ) ^ 3) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast SlimReverseShape.card_le_cube d K)
      calc unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e)
          ≤ unitaryHaar (Fin d × Fin d) (⋃ s : SlimReverseShape d K,
              SlimReverseBlocks.witnessTargets s hd (Real.sqrt (18 * e)) (Real.sqrt (18 * e))) :=
            measure_mono hcover
        _ ≤ ∑ s : SlimReverseShape d K, unitaryHaar (Fin d × Fin d)
              (SlimReverseBlocks.witnessTargets s hd (Real.sqrt (18 * e)) (Real.sqrt (18 * e))) :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _s : SlimReverseShape d K, ENNReal.ofReal
              (Real.exp (C₀ * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
                ((4 + 32 * Real.sqrt (18 * e)) * Real.sqrt K / d +
                  2 * (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
                    strongUncontrolledRank d *
                (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
                  (d ^ 4 - strongUncontrolledRank d)) :=
            Finset.sum_le_sum fun s _ => hshape s
        _ = (Fintype.card (SlimReverseShape d K) : ℝ≥0∞) * ENNReal.ofReal
              (Real.exp (C₀ * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
                ((4 + 32 * Real.sqrt (18 * e)) * Real.sqrt K / d +
                  2 * (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
                    strongUncontrolledRank d *
                (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
                  (d ^ 4 - strongUncontrolledRank d)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal ((K : ℝ) ^ 3) * ENNReal.ofReal
              (Real.exp (C₀ * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
                ((4 + 32 * Real.sqrt (18 * e)) * Real.sqrt K / d +
                  2 * (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
                    strongUncontrolledRank d *
                (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
                  (d ^ 4 - strongUncontrolledRank d)) := by
            gcongr
        _ = ENNReal.ofReal ((K : ℝ) ^ 3 *
              (Real.exp (C₀ * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
                ((4 + 32 * Real.sqrt (18 * e)) * Real.sqrt K / d +
                  2 * (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2))) ^
                    strongUncontrolledRank d *
                (32 * Real.sqrt (18 * e) * Real.sqrt (1 + K / (d : ℝ) ^ 2)) ^
                  (d ^ 4 - strongUncontrolledRank d))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [hP]
            exact strong_small_radius_arith (by linarith) hd hK
              (eight_mul_strongUncontrolledRank_le hd) he hu
    · exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr
        (one_le_strong_haar_rhs (by linarith) hd hK he hcase))
  refine ⟨hpure, ?_⟩
  rw [mixedReachable_eq_pureReachable]
  exact hpure

/-- Near-SWAP diamond Haar bound: the same restricted bound for the Haar outer measure of diamond reachability. -/
theorem exists_strongRestrictedDiamondHaarBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C := by
  obtain ⟨C, hC, h⟩ := exists_strongRestrictedHaarBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd hK e he he2
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := h d K hd hK e he he2
  exact ⟨(measure_mono (Set.inter_subset_inter_right _
      (pureDiamondReachable_subset_pureReachable K e))).trans hp,
    (measure_mono (Set.inter_subset_inter_right _
      (mixedDiamondReachable_subset_mixedReachable K e))).trans hm⟩

/-- Near-SWAP score Haar bound from the four explicit inputs. -/
theorem exists_strongRestrictedHaarBound_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C :=
  exists_strongRestrictedHaarBound
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Near-SWAP diamond Haar bound from the four explicit inputs. -/
theorem exists_strongRestrictedDiamondHaarBound_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C :=
  exists_strongRestrictedDiamondHaarBound
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

end NLQCLean
