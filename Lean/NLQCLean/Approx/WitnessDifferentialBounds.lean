import NLQCLean.Rigidity.ReverseWitnessCalculus
import NLQCLean.Approx.WitnessVelocityBounds

/-!
# Quantitative bounds for the raw ambient derivative

The Frobenius output costs sqrt(D)=d, while the rescaled
input uses the explicit block Euclidean norm. The common integral coordinate
budget is fixed to P=32 d² K². Composing with the cubic projection and
realizing common Euclidean coordinates are subsequent steps.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem frobNorm_le_sqrt_card_mul_opNorm {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    ‖A‖ ≤ Real.sqrt (Fintype.card n : ℝ) * opNorm A := by
  have hI : ‖(1 : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n : ℝ) := by
    have hs : ‖(1 : Matrix n n ℂ)‖ ^ 2 = (Fintype.card n : ℝ) := by
      have h := frobInner_self_of_isometry (isIsometry_one (n := n) (𝕜 := ℂ))
      rw [frobInner_self_eq_norm_sq] at h
      exact_mod_cast h
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  have h := frobNorm_mul_le A (1 : Matrix n n ℂ)
  simpa only [Matrix.mul_one, hI, mul_comm] using h

theorem opNorm_crossGramVelocity_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A B : Matrix m n ℂ} (hA : IsIsometry A) (hB : IsIsometry B) (A' B' : Matrix m n ℂ) :
    opNorm (crossGramVelocity A B A' B') ≤ opNorm A' + opNorm B' := by
  have hleft : opNorm (B'ᴴ * A) ≤ opNorm B' := by
    simpa only [opNorm_conjTranspose] using opNorm_mul_isometry_le B'ᴴ hA
  have hright : opNorm (Bᴴ * A') ≤ opNorm A' :=
    (opNorm_mul_le Bᴴ A').trans (by
      simpa only [opNorm_conjTranspose, one_mul] using
        mul_le_mul_of_nonneg_right hB.opNorm_le_one (opNorm_nonneg A'))
  exact (opNorm_add_le _ _).trans (by linarith)

/-- The fixed natural coordinate budget for the polynomial witness family, with C1=32. -/
def witnessCoordinateBudget (d K : ℕ) : ℕ := 32 * d ^ 2 * K ^ 2

theorem witness_speedConstant_le_budget {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) :
    (d : ℝ) * Real.sqrt (5 * d * K : ℝ) ≤ (witnessCoordinateBudget d K : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdK : (2 : ℝ) ≤ d * K := by
    simpa using mul_le_mul hdR hKR (by norm_num) (by positivity : 0 ≤ (d : ℝ))
  have hs : Real.sqrt (5 * d * K : ℝ) ≤ 5 * d * K :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hk2 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (d : ℝ) * (5 * d * K) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg d)
    _ = 5 * (d : ℝ) ^ 2 * K := by ring
    _ ≤ 5 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ ≤ 32 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (K : ℝ))]
    _ = _ := by simp [witnessCoordinateBudget]

theorem ReverseShape.one_le_budget {d K : ℕ} (s : ReverseShape d K) : 1 ≤ K :=
  (mul_pos (mul_pos s.resource_pos s.messageA_pos) s.messageB_pos).trans_le s.footprint

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

theorem IsValid.frobNorm_overlapVelocity_le {x : ReverseBlocks s} (hx : IsValid x) (v : ReverseBlocks s) :
    ‖overlapVelocity x v‖ ≤ (d : ℝ) * (opNorm (forwardVelocity x v) + opNorm (reverseVelocity x v)) := by
  have h := (frobNorm_le_sqrt_card_mul_opNorm (overlapVelocity x v)).trans
    (mul_le_mul_of_nonneg_left
      (opNorm_crossGramVelocity_le hx.isIsometry_forward hx.isIsometry_reverse
        (forwardVelocity x v) (reverseVelocity x v)) (Real.sqrt_nonneg _))
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Real.sqrt_mul_self (Nat.cast_nonneg d)] using h

/-- Raw ambient derivative bound in rescaled directions, before cubic projection. -/
theorem IsValid.norm_fderiv_overlap_rescaled_le {x : ReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (v : ReverseBlocks s) :
    ‖fderiv ℝ overlap x (rescaleBlocks v)‖ ≤
      ((d : ℝ) * Real.sqrt (5 * d * K : ℝ)) * euclideanNorm v := by
  rw [fderiv_overlap_apply]
  have h := (hx.frobNorm_overlapVelocity_le (rescaleBlocks v)).trans
    (mul_le_mul_of_nonneg_left (hx.rescaled_speed_le_sqrt_five hd v) (Nat.cast_nonneg d))
  simpa only [mul_assoc] using h

theorem IsValid.norm_fderiv_overlap_rescaled_le_budget {x : ReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (v : ReverseBlocks s) :
    ‖fderiv ℝ overlap x (rescaleBlocks v)‖ ≤ (witnessCoordinateBudget d K : ℝ) * euclideanNorm v :=
  (hx.norm_fderiv_overlap_rescaled_le hd v).trans
    (mul_le_mul_of_nonneg_right (witness_speedConstant_le_budget hd s.one_le_budget) (euclideanNorm_nonneg v))

/-- The residual is small for every ambient velocity when the witness has
small scalar leakage. No tangent premise is needed for this norm estimate. -/
theorem IsValid.norm_rescaled_residual_le {x : ReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) (v : ReverseBlocks s) :
    ‖crossGramResidual (forward x) (reverse x)
      (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))‖ ≤
        (δ * ((d : ℝ) * Real.sqrt (5 * d * K : ℝ))) * euclideanNorm v := by
  have hbase := norm_crossGramResidual_le_of_defect_sq (forward x) (reverse x)
    (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))
    hx.isIsometry_forward hx.isIsometry_reverse (mul_nonneg (Nat.cast_nonneg d) hδ)
    (L := (d : ℝ) * δ)
  have he : (Fintype.card (Fin d × Fin d) : ℝ) - ‖(reverse x)ᴴ * forward x‖ ^ 2 ≤
      ((d : ℝ) * δ) ^ 2 := by
    have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
    rw [hD, mul_pow]
    exact hdef
  have h := (hbase he).trans (mul_le_mul_of_nonneg_left (hx.rescaled_speed_le_sqrt_five hd v)
    (mul_nonneg (Nat.cast_nonneg d) hδ))
  exact h.trans_eq (by ring)

theorem IsValid.norm_rescaled_residual_le_budget {x : ReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) (v : ReverseBlocks s) :
    ‖crossGramResidual (forward x) (reverse x)
      (forwardVelocity x (rescaleBlocks v)) (reverseVelocity x (rescaleBlocks v))‖ ≤
        (δ * witnessCoordinateBudget d K) * euclideanNorm v :=
  (hx.norm_rescaled_residual_le hd hδ hdef v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (witness_speedConstant_le_budget hd s.one_le_budget) hδ)
      (euclideanNorm_nonneg v))

end ReverseBlocks
end NLQCLean
