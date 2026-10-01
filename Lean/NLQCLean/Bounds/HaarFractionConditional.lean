import NLQCLean.Approx.ReachableWitnessCover
import NLQCLean.Bounds.HaarAbsorption
import NLQCLean.Bounds.CodimensionArithmetic

/-!
# Conditional Haar bounds for physical reachability

Sum over the proved finite witness cover, then treat both
error regimes and absorb all fixed dimension factors. Every conditional
statement takes the single geometric property explicitly.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

/-- The combined radius rho+lambda, in the ordinary Frobenius norm. -/
noncomputable def witnessTubeRadius (d K : ℕ) (e : ℝ) : ℝ :=
  (d : ℝ) * Real.sqrt (2 * e) + Real.sqrt (2 * e) * witnessCoordinateBudget d K

/-- Finite-family Haar bound in the small-radius regime, before logarithmic absorption. -/
theorem exists_small_radius_reachable_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      witnessTubeRadius d K e ≤ 1 / 2 →
      unitaryHaar (Fin d × Fin d) (pureReachable d K e) ≤
        ENNReal.ofReal (Real.exp (3 * (witnessCoordinateBudget d K : ℝ)) *
          Real.exp (C * (witnessCoordinateBudget d K + (d : ℝ) ^ 4)) *
          (C * (witnessCoordinateBudget d K : ℝ)) ^ (4 * d ^ 2 - 3) *
          (C * witnessTubeRadius d K e) ^ (d ^ 4 - (4 * d ^ 2 - 3))) := by
  obtain ⟨C, hC, hbound⟩ := ReverseBlocks.exists_witness_haar_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd2 e he he' hr'
  have hd : 0 < d := by omega
  have hδ : 0 < Real.sqrt (2 * e) := Real.sqrt_pos.mpr (by linarith)
  have hδ1 : Real.sqrt (2 * e) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨zero_le_one, by nlinarith⟩
  have hr : 0 < witnessTubeRadius d K e := by unfold witnessTubeRadius; positivity
  have hLeak : Real.sqrt (2 * e) * witnessCoordinateBudget d K ≤ witnessTubeRadius d K e := by
    unfold witnessTubeRadius
    exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg d) hδ.le)
  have hρ : (d : ℝ) * Real.sqrt (2 * e) ≤ witnessTubeRadius d K e := by
    unfold witnessTubeRadius
    exact le_add_of_nonneg_right (mul_nonneg hδ.le (Nat.cast_nonneg _))
  let B : ℝ := Real.exp (C * (witnessCoordinateBudget d K + (d : ℝ) ^ 4)) *
    (C * (witnessCoordinateBudget d K : ℝ)) ^ (4 * d ^ 2 - 3) *
      (C * witnessTubeRadius d K e) ^ (d ^ 4 - (4 * d ^ 2 - 3))
  let S := fun s : ReverseShape d K =>
    ReverseBlocks.witnessTargets s hd (Real.sqrt (2 * e)) ((d : ℝ) * Real.sqrt (2 * e))
  have hfamily (s : ReverseShape d K) : unitaryHaar (Fin d × Fin d) (S s) ≤ ENNReal.ofReal B :=
    hbound d K s hd hd2 _ _ _ hδ.le hδ1 hr hr' hLeak hρ (S s)
      (ReverseBlocks.measurableSet_witnessTargets s hd _ _) (fun _ hx => hx)
  have hcard : (Fintype.card (ReverseShape d K) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (3 * (witnessCoordinateBudget d K : ℝ))) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (ReverseShape.card_le_exp_coordinateBudget (K := K) hd)
  calc
    _ ≤ unitaryHaar (Fin d × Fin d) (⋃ s, S s) :=
      measure_mono (pureReachable_subset_witnessTargets hd he.le (by linarith))
    _ ≤ ∑ s, unitaryHaar (Fin d × Fin d) (S s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : ReverseShape d K, ENNReal.ofReal B := Finset.sum_le_sum (fun s _ => hfamily s)
    _ = Fintype.card (ReverseShape d K) * ENNReal.ofReal B := by simp
    _ ≤ ENNReal.ofReal (Real.exp (3 * (witnessCoordinateBudget d K : ℝ))) * ENNReal.ofReal B :=
      mul_le_mul_left hcard _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      dsimp only [B]
      ring

/-- Haar bound: one constant covers both error regimes and pure and finite mixed resources.
The exponent uses real division by two. The sole geometric property remains explicit. -/
theorem exists_haar_fraction_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (pureReachable d K e) ∧ MeasurableSet (mixedReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (pureReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hsmall⟩ := exists_small_radius_reachable_haar_constant hGeom
  refine ⟨512 * C, by linarith, ?_⟩
  intro d K hd _hK hquarter e he he'
  let P : ℝ := witnessCoordinateBudget d K
  let N : ℕ := d ^ 4
  let t : ℕ := 4 * d ^ 2 - 3
  have hP : 1 ≤ P := one_le_coordinateBudget_of_quarter hd hquarter
  have hNP : (N : ℝ) ≤ P := by
    simpa only [N, Nat.cast_pow] using witnessDimension_le_coordinateBudget hd hquarter
  have hlog : (N : ℝ) * (1 + Real.log P) ≤ 2 * P := by
    simpa only [N, Nat.cast_pow] using witnessDimension_mul_one_add_log_le hd hquarter
  have ht : t ≤ N := ReverseBlocks.localMotionRank_le_unitaryDimension hd
  have hr : 0 ≤ witnessTubeRadius d K e := by unfold witnessTubeRadius; positivity
  have hrFine : witnessTubeRadius d K e ≤ 2 * Real.sqrt 2 * P * Real.sqrt e :=
    freezing_radius_le hd hquarter he.le
  have hrCoarse : witnessTubeRadius d K e ≤ 4 * P * Real.sqrt e := by
    refine hrFine.trans ?_
    gcongr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hbound : unitaryHaar (Fin d × Fin d) (pureReachable d K e) ≤
      ENNReal.ofReal (Real.exp (16 * C * P) * Real.exp (((N - t : ℕ) : ℝ) / 2 * Real.log e)) := by
    by_cases hrad : witnessTubeRadius d K e ≤ 1 / 2
    · refine (hsmall d K hd e he he' hrad).trans (ENNReal.ofReal_le_ofReal ?_)
      simpa only [N, Nat.cast_pow] using
        small_radius_prefactor_le ht hC hP hNP hlog he hr hrCoarse
    · have hone := one_le_large_radius_rhs (Nat.sub_le N t) hC hP hNP hlog he
        (by linarith : e ≤ 1) (lt_of_not_ge hrad) hrFine
      exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone)
  have hexp : 16 * C * P = (512 * C) * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
    dsimp only [P, witnessCoordinateBudget]
    push_cast
    ring
  have heq : Real.exp (16 * C * P) * Real.exp (((N - t : ℕ) : ℝ) / 2 * Real.log e) =
      Real.exp ((512 * C) * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((unitaryCodimension d : ℝ) / 2) := by
    rw [hexp, Real.rpow_def_of_pos he]
    congr 1
    congr 1
    change (((unitaryCodimension d : ℕ) : ℝ) / 2) * Real.log e =
      Real.log e * ((unitaryCodimension d : ℝ) / 2)
    ring
  rw [heq] at hbound
  refine ⟨measurableSet_pureReachable d K e, measurableSet_mixedReachable d K e,
    le_min prob_le_one hbound, ?_⟩
  rw [mixedReachable_eq_pureReachable]
  exact le_min prob_le_one hbound

end NLQCLean
