import NLQCLean.Approx.NormalizedCubicWitness
import NLQCLean.Geometry.LocalMotionRank

/-!
# Ambient rank and error bounds for the cubic witness extension

The local term is a real-linear map
constructed from the actual ambient derivative. Its complement is the
explicit cross-Gram leakage residual after cubic projection. All norm
bounds use the Euclidean block norm and the Frobenius output norm.
-/

namespace NLQCLean
namespace ReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : ReverseShape d K}

/-- The globally defined cubic extension of the normalized overlap. -/
noncomputable def extendedOverlap (x : ReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  overlap (rescaleBlocks (normalizedCubicBlocks x))

theorem contDiff_extendedOverlap : ContDiff ℝ ∞ (extendedOverlap : ReverseBlocks s → _) := by
  let L := (rescaleBlocks (s := s)).toContinuousLinearMap
  exact contDiff_overlap.comp (L.contDiff.comp contDiff_normalizedCubicBlocks)

theorem extendedOverlap_eq_overlap {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    extendedOverlap x = overlap (rescaleBlocks x) := by
  rw [extendedOverlap, normalizedCubicBlocks_eq_self hx hd]

theorem fderiv_extendedOverlap_apply {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : ReverseBlocks s) :
    fderiv ℝ extendedOverlap x v =
      overlapVelocity (rescaleBlocks x)
        (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := by
  let L := (rescaleBlocks (s := s)).toContinuousLinearMap
  have hq := (contDiff_normalizedCubicBlocks.differentiable (by simp)).differentiableAt
    (x := x)
  have hL := L.hasFDerivAt.comp x hq.hasFDerivAt
  have hH := (contDiff_overlap.differentiable (by simp)).differentiableAt
    (x := rescaleBlocks (normalizedCubicBlocks x))
  have h := congrArg (fun f => f v) (hH.hasFDerivAt.comp x hL).fderiv
  have hf : fderiv ℝ extendedOverlap x v =
      fderiv ℝ overlap (rescaleBlocks (normalizedCubicBlocks x))
        (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := by
    convert h using 1 <;> rfl
  rw [normalizedCubicBlocks_eq_self hx hd, fderiv_overlap_apply] at hf
  exact hf

/-- The two local generators, composed with the projected ambient direction. -/
noncomputable def extendedLocalTerm (x : ReverseBlocks s) :
    ReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  let z := rescaleBlocks x
  let L := rescaleBlocks.comp (fderiv ℝ normalizedCubicBlocks x).toLinearMap
  let a := (mulCLM (forward z)ᴴ).toLinearMap.comp ((fderiv ℝ forward z).toLinearMap.comp L)
  let b := (mulCLM (reverse z)ᴴ).toLinearMap.comp ((fderiv ℝ reverse z).toLinearMap.comp L)
  (-((mulLeftCLM (overlap z)).toLinearMap.comp b) +
    (mulRightCLM (overlap z)).toLinearMap.comp a)

theorem extendedLocalTerm_apply (x v : ReverseBlocks s) :
    let z := rescaleBlocks x
    let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
    extendedLocalTerm x v =
      -((reverse z)ᴴ * reverseVelocity z w) * overlap z +
        overlap z * ((forward z)ᴴ * forwardVelocity z w) := by
  simp [extendedLocalTerm, fderiv_forward_apply, fderiv_reverse_apply]

theorem finrank_extendedLocalTerm_le {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    Module.finrank ℝ (LinearMap.range (extendedLocalTerm x)) ≤ 4 * d ^ 2 - 3 := by
  let : NeZero d := ⟨hd.ne'⟩
  have h := finrank_range_le_of_local_motion (overlap (rescaleBlocks x)) (extendedLocalTerm x)
    (fun v => by
      have ht := isTangent_rescaled_fderiv_normalizedCubicBlocks hx hd v
      exact ⟨_, hx.forward_generator_mem_localSkew ht, _, hx.reverse_generator_mem_localSkew ht,
        extendedLocalTerm_apply x v⟩)
  simpa only [Fintype.card_fin] using h

/-- The ambient error term is real-linear without any choice of generators. -/
noncomputable def extendedResidual (x : ReverseBlocks s) :
    ReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (fderiv ℝ extendedOverlap x).toLinearMap - extendedLocalTerm x

theorem fderiv_extendedOverlap_decomposition (x : ReverseBlocks s) :
    (fderiv ℝ extendedOverlap x).toLinearMap = extendedLocalTerm x + extendedResidual x := by
  simp [extendedResidual]

theorem extendedResidual_apply {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : ReverseBlocks s) :
    let z := rescaleBlocks x
    let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
    extendedResidual x v = crossGramResidual (forward z) (reverse z)
      (forwardVelocity z w) (reverseVelocity z w) := by
  have ht := isTangent_rescaled_fderiv_normalizedCubicBlocks hx hd v
  have hb := hx.reverse_generator_mem_localSkew ht
  have hskew := mem_skewHermitian_iff.mp (localSkew_le_skewHermitian hb)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hskew
  let z := rescaleBlocks x
  let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
  have hdec := crossGramVelocity_decomposition (forward z) (reverse z)
    (forwardVelocity z w) (reverseVelocity z w) (by
    rw [hskew, add_neg_cancel])
  dsimp only
  rw [extendedResidual, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
    fderiv_extendedOverlap_apply hx hd, extendedLocalTerm_apply]
  exact sub_eq_iff_eq_add.mpr (hdec.trans (add_comm _ _))

theorem norm_fderiv_extendedOverlap_le_budget {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) (v : ReverseBlocks s) :
    ‖fderiv ℝ extendedOverlap x v‖ ≤ (witnessCoordinateBudget d K : ℝ) * euclideanNorm v := by
  have hd0 : 0 < d := by omega
  rw [fderiv_extendedOverlap_apply hx hd0, ← fderiv_overlap_apply]
  exact (hx.norm_fderiv_overlap_rescaled_le_budget hd _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd0 v)
      (Nat.cast_nonneg _))

theorem norm_extendedResidual_le_budget {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2)
    (v : ReverseBlocks s) :
    ‖extendedResidual x v‖ ≤ (δ * witnessCoordinateBudget d K) * euclideanNorm v := by
  have hd0 : 0 < d := by omega
  rw [extendedResidual_apply hx hd0]
  exact (hx.norm_rescaled_residual_le_budget hd hδ hdef _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd0 v)
      (mul_nonneg hδ (Nat.cast_nonneg _)))

/-- TP7's ambient decomposition, before transporting the blocks into common
padded Euclidean coordinates. No rank or derivative bound is an assumption. -/
theorem exists_extendedOverlap_rank_error_decomposition {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : ReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (fderiv ℝ extendedOverlap x).toLinearMap = T + R ∧
      Module.finrank ℝ (LinearMap.range T) ≤ 4 * d ^ 2 - 3 ∧
      (∀ v, ‖fderiv ℝ extendedOverlap x v‖ ≤ (witnessCoordinateBudget d K : ℝ) * euclideanNorm v) ∧
      (∀ v, ‖R v‖ ≤ (δ * witnessCoordinateBudget d K) * euclideanNorm v) :=
  ⟨extendedLocalTerm x, extendedResidual x, fderiv_extendedOverlap_decomposition x,
    finrank_extendedLocalTerm_le hx (by omega), norm_fderiv_extendedOverlap_le_budget hx hd,
    norm_extendedResidual_le_budget hx hd hδ hdef⟩

end ReverseBlocks
end NLQCLean
