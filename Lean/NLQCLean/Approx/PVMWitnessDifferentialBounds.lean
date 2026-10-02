import NLQCLean.Approx.PVMWitnessVelocityBounds
import NLQCLean.Approx.WitnessDifferentialBounds

/-!
# PVM raw ambient derivative and residual bounds

The normalized velocity bound gives Frobenius differential size
at most the fixed coordinate budget. Leakage controls the cross-Gram
residual for every ambient direction, before the cubic projection.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

theorem pvm_witness_speedConstant_le_budget {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) :
    (d : ℝ) * Real.sqrt (10 * d * K : ℝ) ≤ (pvmWitnessCoordinateBudget d K : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdK : (2 : ℝ) ≤ d * K := by
    simpa using mul_le_mul hdR hKR (by norm_num) (by positivity : 0 ≤ (d : ℝ))
  have hs : Real.sqrt (10 * d * K : ℝ) ≤ 10 * d * K :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hk2 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (d : ℝ) * (10 * d * K) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg d)
    _ = 10 * (d : ℝ) ^ 2 * K := by ring
    _ ≤ 10 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ ≤ 1024 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (K : ℝ))]
    _ = _ := by simp [pvmWitnessCoordinateBudget]

namespace PVMReverseBlocks

variable {d K : ℕ} {s : PVMReverseShape d K}

theorem IsValid.frobNorm_overlapVelocity_le {x : PVMReverseBlocks s} (hx : IsValid x) (v : PVMReverseBlocks s) :
    ‖overlapVelocity x v‖ ≤ (d : ℝ) * (opNorm (forwardVelocity x v) + opNorm (reverseVelocity x v)) := by
  have h := (frobNorm_le_sqrt_card_mul_opNorm (overlapVelocity x v)).trans
    (mul_le_mul_of_nonneg_left
      (opNorm_crossGramVelocity_le hx.isIsometry_forward hx.isIsometry_reverse
        (forwardVelocity x v) (reverseVelocity x v)) (Real.sqrt_nonneg _))
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Real.sqrt_mul_self (Nat.cast_nonneg d)] using h

/-- Raw ambient derivative bound in rescaled directions, before cubic projection. -/
theorem IsValid.norm_fderiv_overlap_rescaled_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) (v : PVMReverseBlocks s) :
    ‖fderiv ℝ overlap x (rescaleBlocks v)‖ ≤
      ((d : ℝ) * Real.sqrt (10 * d * K : ℝ)) * euclideanNorm v := by
  rw [fderiv_overlap_apply]
  have h := (hx.frobNorm_overlapVelocity_le (rescaleBlocks v)).trans
    (mul_le_mul_of_nonneg_left (hx.rescaled_speed_le_sqrt_ten hd hfloor v) (Nat.cast_nonneg d))
  simpa only [mul_assoc] using h

theorem IsValid.norm_fderiv_overlap_rescaled_le_budget {x : PVMReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)
    (v : PVMReverseBlocks s) :
    ‖fderiv ℝ overlap x (rescaleBlocks v)‖ ≤ (P : ℝ) * euclideanNorm v :=
  (hx.norm_fderiv_overlap_rescaled_le hd hfloor v).trans
    (mul_le_mul_of_nonneg_right hP.2 (euclideanNorm_nonneg v))

/-- The residual is small for every ambient velocity when the witness has
small scalar leakage. No tangent premise is needed for this norm estimate. -/
theorem IsValid.norm_rescaled_residual_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) (v : PVMReverseBlocks s) :
    ‖crossGramResidual (forward x) (reverse x)
      (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))‖ ≤
        (δ * ((d : ℝ) * Real.sqrt (10 * d * K : ℝ))) * euclideanNorm v := by
  have hbase := norm_crossGramResidual_le_of_defect_sq (forward x) (reverse x)
    (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))
    hx.isIsometry_forward hx.isIsometry_reverse (mul_nonneg (Nat.cast_nonneg d) hδ)
    (L := (d : ℝ) * δ)
  have he : (Fintype.card (Fin d × Fin d) : ℝ) - ‖(reverse x)ᴴ * forward x‖ ^ 2 ≤
      ((d : ℝ) * δ) ^ 2 := by
    have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
    rw [hD, mul_pow]
    exact hdef
  have h := (hbase he).trans (mul_le_mul_of_nonneg_left (hx.rescaled_speed_le_sqrt_ten hd hfloor v)
    (mul_nonneg (Nat.cast_nonneg d) hδ))
  exact h.trans_eq (by ring)

theorem IsValid.norm_rescaled_residual_le_budget {x : PVMReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) (v : PVMReverseBlocks s) :
    ‖crossGramResidual (forward x) (reverse x)
      (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))‖ ≤
        (δ * P) * euclideanNorm v :=
  (hx.norm_rescaled_residual_le hd hfloor hδ hdef v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP.2 hδ) (euclideanNorm_nonneg v))

end PVMReverseBlocks
end NLQCLean
