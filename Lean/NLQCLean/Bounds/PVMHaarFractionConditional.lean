import NLQCLean.Approx.PVMReachableWitnessCover
import NLQCLean.Bounds.PVMHaarArithmetic
import NLQCLean.Bounds.HaarAbsorption
import NLQCLean.Bounds.CodimensionArithmetic
import NLQCLean.Geometry.PVMPolynomialTubeConditional
import NLQCLean.Geometry.UnitaryHaarInverse

/-!
# Conditional PVM Haar bounds for physical reachability

Sum over the proved finite inverse witness cover, transport Haar
measure through inversion, then treat both error regimes and absorb all fixed
dimension factors. Every conditional statement takes the single geometric
property explicitly.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

/-- Finite-family Haar estimate in the small-radius regime, before absorption. -/
theorem exists_small_radius_pvm_reachable_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → (d : ℝ) ^ 2 / 4 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      pvmWitnessTubeRadius d K e ≤ 1 / 2 →
      unitaryHaar (Fin d × Fin d) (purePVMReachable d K e) ≤
        ENNReal.ofReal (Real.exp (3 * (pvmWitnessCoordinateBudget d K : ℝ)) *
          Real.exp (C * (pvmWitnessCoordinateBudget d K + (d : ℝ) ^ 4)) *
          (C * (pvmWitnessCoordinateBudget d K : ℝ)) ^ (3 * d ^ 2 - 2) *
          (C * pvmWitnessTubeRadius d K e) ^ (d ^ 4 - (3 * d ^ 2 - 2))) := by
  obtain ⟨C, hC, hbound⟩ := PVMReverseBlocks.exists_witness_haar_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd2 hquarter e he he' hr'
  have hd : 0 < d := by omega
  have hfloor : d ^ 2 ≤ 4 * K := by
    exact_mod_cast (show (d : ℝ) ^ 2 ≤ 4 * K by linarith)
  have hδ : 0 < 2 * Real.sqrt e := by positivity
  have hr : 0 < pvmWitnessTubeRadius d K e := by unfold pvmWitnessTubeRadius; positivity
  have hLeak : (2 * Real.sqrt e) * pvmWitnessCoordinateBudget d K ≤
      pvmWitnessTubeRadius d K e := by
    unfold pvmWitnessTubeRadius
    exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg d) hδ.le)
  have hρ : 2 * (d : ℝ) * Real.sqrt e ≤ pvmWitnessTubeRadius d K e := by
    unfold pvmWitnessTubeRadius
    calc
      _ = (d : ℝ) * (2 * Real.sqrt e) := by ring
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hδ.le (Nat.cast_nonneg _))
  have hP : (1 : ℝ) ≤ pvmWitnessCoordinateBudget d K :=
    pvm_one_le_coordinateBudget_of_quarter hd2 hquarter
  -- The small-radius condition, not ε ≤ 1/2, gives δ = 2√ε ≤ 1.
  have hδ1 : 2 * Real.sqrt e ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hP hδ.le
    have h2 : 0 ≤ (d : ℝ) * (2 * Real.sqrt e) := by positivity
    unfold pvmWitnessTubeRadius at hr'
    linarith
  let B : ℝ := Real.exp (C * (pvmWitnessCoordinateBudget d K + (d : ℝ) ^ 4)) *
    (C * (pvmWitnessCoordinateBudget d K : ℝ)) ^ (3 * d ^ 2 - 2) *
      (C * pvmWitnessTubeRadius d K e) ^ (d ^ 4 - (3 * d ^ 2 - 2))
  let S := fun s : PVMReverseShape d K =>
    PVMReverseBlocks.witnessTargets s hd hfloor (2 * Real.sqrt e) (2 * (d : ℝ) * Real.sqrt e)
  have hfamily (s : PVMReverseShape d K) :
      unitaryHaar (Fin d × Fin d) (S s) ≤ ENNReal.ofReal B :=
    hbound d K s hd hfloor hd2 _ _ _ hδ.le hδ1 hr hr' hLeak hρ (S s)
      (PVMReverseBlocks.measurableSet_witnessTargets s hd hfloor _ _) (fun _ hx => hx)
  have hcard : (Fintype.card (PVMReverseShape d K) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (3 * (pvmWitnessCoordinateBudget d K : ℝ))) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (PVMReverseShape.card_le_exp_coordinateBudget (K := K) hd)
  have hcover := purePVMReachable_subset_inv_witnessTargets hd hfloor he.le he'
  calc
    _ ≤ unitaryHaar (Fin d × Fin d) (Inv.inv ⁻¹' ⋃ s, S s) := measure_mono hcover
    _ = unitaryHaar (Fin d × Fin d) (⋃ s, S s) := unitaryHaar_preimage_inv _ _
    _ ≤ ∑ s, unitaryHaar (Fin d × Fin d) (S s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : PVMReverseShape d K, ENNReal.ofReal B :=
      Finset.sum_le_sum (fun s _ => hfamily s)
    _ = Fintype.card (PVMReverseShape d K) * ENNReal.ofReal B := by simp
    _ ≤ ENNReal.ofReal (Real.exp (3 * (pvmWitnessCoordinateBudget d K : ℝ))) *
        ENNReal.ofReal B := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      dsimp only [B]
      ring

/-- PVM Haar bound / one constant covers both error regimes and pure and finite mixed resources.
The exponent uses real division by two. The sole geometric property remains explicit. -/
theorem exists_pvm_haar_fraction_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (purePVMReachable d K e) ∧ MeasurableSet (mixedPVMReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (purePVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedPVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hsmall⟩ := exists_small_radius_pvm_reachable_haar_constant hGeom
  refine ⟨16384 * C, by linarith, ?_⟩
  intro d K hd _hK hquarter e he he'
  have hP : (1 : ℝ) ≤ pvmWitnessCoordinateBudget d K :=
    pvm_one_le_coordinateBudget_of_quarter hd hquarter
  have hNP : ((d ^ 4 : ℕ) : ℝ) ≤ pvmWitnessCoordinateBudget d K := by
    simpa only [Nat.cast_pow] using pvm_fourth_power_le_coordinateBudget hd hquarter
  have hlog : ((d ^ 4 : ℕ) : ℝ) * (1 + Real.log (pvmWitnessCoordinateBudget d K : ℝ)) ≤
      2 * pvmWitnessCoordinateBudget d K := by
    simpa only [Nat.cast_pow] using pvm_witnessDimension_mul_one_add_log_le hd hquarter
  have ht : 3 * d ^ 2 - 2 ≤ d ^ 4 := PVMReverseBlocks.pvmMotionRank_le_unitaryDimension hd
  have hr : 0 ≤ pvmWitnessTubeRadius d K e := by unfold pvmWitnessTubeRadius; positivity
  have hrCoarse : pvmWitnessTubeRadius d K e ≤
      4 * (pvmWitnessCoordinateBudget d K : ℝ) * Real.sqrt e :=
    pvm_witnessTubeRadius_le hd hquarter he.le
  have hbound : unitaryHaar (Fin d × Fin d) (purePVMReachable d K e) ≤
      ENNReal.ofReal (Real.exp (16 * C * pvmWitnessCoordinateBudget d K) *
        Real.exp (((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) / 2 * Real.log e)) := by
    by_cases hrad : pvmWitnessTubeRadius d K e ≤ 1 / 2
    · refine (hsmall d K hd hquarter e he he' hrad).trans (ENNReal.ofReal_le_ofReal ?_)
      simpa only [Nat.cast_pow] using
        small_radius_prefactor_le ht hC hP hNP hlog he hr hrCoarse
    · have hone := pvm_one_le_large_radius_rhs (Nat.sub_le (d ^ 4) (3 * d ^ 2 - 2))
        hC hP hNP hlog he (by linarith : e ≤ 1) (lt_of_not_ge hrad) hrCoarse
      exact prob_le_one.trans
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone)
  have hexp : 16 * C * (pvmWitnessCoordinateBudget d K : ℝ) =
      (16384 * C) * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
    unfold pvmWitnessCoordinateBudget
    push_cast
    ring
  have heq : Real.exp (16 * C * pvmWitnessCoordinateBudget d K) *
        Real.exp (((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) / 2 * Real.log e) =
      Real.exp ((16384 * C) * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((pvmCodimension d : ℝ) / 2) := by
    rw [hexp, Real.rpow_def_of_pos he, pvmCodimension]
    congr 2
    ring
  rw [heq] at hbound
  refine ⟨measurableSet_purePVMReachable d K e, measurableSet_mixedPVMReachable d K e,
    le_min prob_le_one hbound, ?_⟩
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact le_min prob_le_one hbound

end NLQCLean
