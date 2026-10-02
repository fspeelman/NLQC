import NLQCLean.Approx.PVMExtendedWitness
import NLQCLean.Rigidity.PVMReverseGenerator
import NLQCLean.Geometry.PVMMotionRank

/-!
# Ambient PVM motion and leakage decomposition

The actual full ambient derivative splits into an explicit
real-linear motion of rank at most 3d²−2 and the cross-Gram leakage residual.
No unitary condition on the overlap matrix is used.
-/

namespace NLQCLean
namespace PVMReverseBlocks
open Matrix
open scoped Matrix.Norms.Frobenius
variable {d K : ℕ} {s : PVMReverseShape d K}

/-- Local input and diagonal output generators on each projected ambient direction. -/
noncomputable def extendedLocalTerm (x : PVMReverseBlocks s) :
    PVMReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  let z := rescaleBlocks x
  let L := rescaleBlocks.comp (fderiv ℝ normalizedCubicBlocks x).toLinearMap
  let a := (mulCLM (forward z)ᴴ).toLinearMap.comp ((fderiv ℝ forward z).toLinearMap.comp L)
  let b := (mulCLM (reverse z)ᴴ).toLinearMap.comp ((fderiv ℝ reverse z).toLinearMap.comp L)
  (-((mulLeftCLM (overlap z)).toLinearMap.comp b) +
    (mulRightCLM (overlap z)).toLinearMap.comp a)

theorem extendedLocalTerm_apply (x v : PVMReverseBlocks s) :
    let z := rescaleBlocks x
    let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
    extendedLocalTerm x v =
      -((reverse z)ᴴ * reverseVelocity z w) * overlap z +
        overlap z * ((forward z)ᴴ * forwardVelocity z w) := by
  simp [extendedLocalTerm, fderiv_forward_apply, fderiv_reverse_apply]

theorem finrank_extendedLocalTerm_le {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    Module.finrank ℝ (LinearMap.range (extendedLocalTerm x)) ≤ 3 * d ^ 2 - 2 := by
  let : NeZero d := ⟨hd.ne'⟩
  have h := finrank_range_le_of_pvm_motion (overlap (rescaleBlocks x)) (extendedLocalTerm x)
    (fun v => by
      have ht := isTangent_rescaled_fderiv_normalizedCubicBlocks hx hd v
      exact ⟨_, hx.forward_generator_mem_localSkew ht, _, hx.reverse_generator_mem_diagSkew ht,
        extendedLocalTerm_apply x v⟩)
  simpa only [Fintype.card_fin] using h

/-- The ambient error term is real-linear without any choice of generators. -/
noncomputable def extendedResidual (x : PVMReverseBlocks s) :
    PVMReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (fderiv ℝ extendedOverlap x).toLinearMap - extendedLocalTerm x

theorem fderiv_extendedOverlap_decomposition (x : PVMReverseBlocks s) :
    (fderiv ℝ extendedOverlap x).toLinearMap = extendedLocalTerm x + extendedResidual x := by
  simp [extendedResidual]

theorem extendedResidual_apply {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : PVMReverseBlocks s) :
    let z := rescaleBlocks x
    let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
    extendedResidual x v = crossGramResidual (forward z) (reverse z)
      (forwardVelocity z w) (reverseVelocity z w) := by
  have ht := isTangent_rescaled_fderiv_normalizedCubicBlocks hx hd v
  have hb := hx.reverse_generator_mem_diagSkew ht
  have hskew := (mem_diagSkew_iff.mp hb).2
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

theorem norm_extendedResidual_le_budget {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2)
    (v : PVMReverseBlocks s) :
    ‖extendedResidual x v‖ ≤ (δ * P) * euclideanNorm v := by
  rw [extendedResidual_apply hx (by omega)]
  exact norm_projected_residual_le_budget hx hd hfloor hP hδ hdef v

/-- An actual ambient rank-plus-error decomposition, without assumed rank bounds. -/
theorem exists_extendedOverlap_rank_error_decomposition {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : PVMReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (fderiv ℝ extendedOverlap x).toLinearMap = T + R ∧
      Module.finrank ℝ (LinearMap.range T) ≤ 3 * d ^ 2 - 2 ∧
      (∀ v, ‖fderiv ℝ extendedOverlap x v‖ ≤ (P : ℝ) * euclideanNorm v) ∧
      (∀ v, ‖R v‖ ≤ (δ * P) * euclideanNorm v) :=
  ⟨extendedLocalTerm x, extendedResidual x, fderiv_extendedOverlap_decomposition x,
    finrank_extendedLocalTerm_le hx (by omega), norm_fderiv_extendedOverlap_le_budget hx hd hfloor hP,
    norm_extendedResidual_le_budget hx hd hfloor hP hδ hdef⟩

/-- **`prop:overlap-derivative` for measurements.** Along every tangent direction of a valid
PVM witness, the overlap velocity is `-b T + T a + Ξ` with a local input generator `a`, a
diagonal skew-Hermitian output generator `b` and the leakage term `Ξ`, whose Frobenius norm
is at most `√h (‖Ė‖_op + ‖Ḋ‖_op)`, with `h ≤ d² δ²`. -/
theorem IsValid.local_velocity_decomposition {x v : PVMReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ a b : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      a ∈ localSkew (Fin d) (Fin d) ∧ b ∈ diagSkew (Fin d × Fin d) ∧
      overlapVelocity x v = -b * overlap x + overlap x * a +
        crossGramResidual (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v) ∧
      ‖crossGramResidual (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v)‖ ≤
        ((d : ℝ) * δ) * (opNorm (forwardVelocity x v) + opNorm (reverseVelocity x v)) := by
  have ha := hx.forward_generator_mem_localSkew hv
  have hb := hx.reverse_generator_mem_diagSkew hv
  refine ⟨(forward x)ᴴ * forwardVelocity x v, (reverse x)ᴴ * reverseVelocity x v, ha, hb, ?_, ?_⟩
  · apply crossGramVelocity_decomposition
    have h := (mem_diagSkew_iff.mp hb).2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
    rw [h, add_neg_cancel]
  · apply norm_crossGramResidual_le_of_defect_sq _ _ _ _
      hx.isIsometry_forward hx.isIsometry_reverse (mul_nonneg (Nat.cast_nonneg _) hδ)
    have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
    simpa only [hD, mul_pow, overlap] using hdef

end PVMReverseBlocks
end NLQCLean
