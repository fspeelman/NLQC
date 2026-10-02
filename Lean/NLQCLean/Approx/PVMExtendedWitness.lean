import NLQCLean.Approx.PVMNormalizedCubicWitness
import NLQCLean.Approx.PVMWitnessDifferentialBounds
import NLQCLean.Approx.PVMWitnessCoordinates

/-!
# Cubic PVM witnesses in common Euclidean coordinates

The blockwise cubic fixes every valid padded point, kills
dummy directions and contracts ambient velocities. The extended overlap has
full ambient derivative norm bounded by the common coordinate budget.

-/

namespace NLQCLean
namespace PVMReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : PVMReverseShape d K}

/-- The globally defined cubic extension of the normalized overlap. -/
noncomputable def extendedOverlap (x : PVMReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  overlap (rescaleBlocks (normalizedCubicBlocks x))

theorem contDiff_extendedOverlap : ContDiff ℝ ∞ (extendedOverlap : PVMReverseBlocks s → _) := by
  let L := (rescaleBlocks (s := s)).toContinuousLinearMap
  exact contDiff_overlap.comp (L.contDiff.comp contDiff_normalizedCubicBlocks)

theorem extendedOverlap_eq_overlap {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    extendedOverlap x = overlap (rescaleBlocks x) := by
  rw [extendedOverlap, normalizedCubicBlocks_eq_self hx hd]

theorem fderiv_extendedOverlap_apply {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : PVMReverseBlocks s) :
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

/-- Every ambient direction satisfies the fixed-budget derivative bound
following the blockwise tangent projection. -/
theorem norm_fderiv_extendedOverlap_le_budget {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)
    (v : PVMReverseBlocks s) :
    ‖fderiv ℝ extendedOverlap x v‖ ≤ (P : ℝ) * euclideanNorm v := by
  rw [fderiv_extendedOverlap_apply hx (by omega), ← fderiv_overlap_apply]
  exact (hx.norm_fderiv_overlap_rescaled_le_budget hd hfloor hP _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_fderiv_normalizedCubicBlocks_le hx (by omega) v)
      (Nat.cast_nonneg _))

/-- The explicit leakage residual stays small after projection of every
ambient direction by the blockwise cubic. -/
theorem norm_projected_residual_le_budget {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2)
    (v : PVMReverseBlocks s) :
    ‖crossGramResidual (forward (rescaleBlocks x)) (reverse (rescaleBlocks x))
      (forwardVelocity (rescaleBlocks x) (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)))
      (reverseVelocity (rescaleBlocks x) (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)))‖ ≤
        (δ * P) * euclideanNorm v :=
  (hx.norm_rescaled_residual_le_budget hd hfloor hP hδ hdef _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_fderiv_normalizedCubicBlocks_le hx (by omega) v)
      (mul_nonneg hδ (Nat.cast_nonneg _)))

end PVMReverseBlocks
namespace PVMReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

/-- The six normalized cubics, with zero output in every dummy coordinate. -/
noncomputable def coordinateCubic (x : RealEuclidean P) :
    RealEuclidean P :=
  encodeCoordinates s hd hfloor hP (normalizedCubicBlocks (decodeCoordinates s hd hfloor hP x))

/-- The global cubic overlap extension in Euclidean coordinates. -/
noncomputable def coordinateOverlap (x : RealEuclidean P) :
    RealEuclidean (2 * d ^ 4) :=
  overlapOutputCoordinates d (extendedOverlap (decodeCoordinates s hd hfloor hP x))

theorem coordinateOverlap_eq_raw_comp_cubic (x : RealEuclidean P) :
    coordinateOverlap s hd hfloor hP x = coordinateRawOverlap s hd hfloor hP (coordinateCubic s hd hfloor hP x) := by
  simp only [coordinateOverlap, coordinateRawOverlap, coordinateCubic,
    decode_encodeCoordinates, extendedOverlap]

theorem coordinateCubic_zero_padding (x : RealEuclidean P)
    {j : Fin P} (hj : j ∉ Set.range (coordinateEmbedding s hd hfloor hP)) :
    coordinateCubic s hd hfloor hP x j = 0 :=
  encodeCoordinates_zero_padding s hd hfloor hP _ hj

theorem coordinateCubic_eq_self {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x)))
    (hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor hP), x j = 0) : coordinateCubic s hd hfloor hP x = x := by
  rw [coordinateCubic, normalizedCubicBlocks_eq_self hx hd]
  exact encode_decodeCoordinates_of_padding s hd hfloor hP x hpad

theorem coordinateOverlap_eq_raw {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) :
    coordinateOverlap s hd hfloor hP x = coordinateRawOverlap s hd hfloor hP x := by
  rw [coordinateOverlap, extendedOverlap_eq_overlap hx hd]
  rfl

theorem contDiff_coordinateCubic : ContDiff ℝ ∞ (coordinateCubic s hd hfloor hP) := by
  let E := (encodeCoordinates s hd hfloor hP).toContinuousLinearMap
  let D := (decodeCoordinates s hd hfloor hP).toContinuousLinearMap
  exact E.contDiff.comp (contDiff_normalizedCubicBlocks.comp D.contDiff)

theorem fderiv_coordinateCubic_apply (x v : RealEuclidean P) :
    fderiv ℝ (coordinateCubic s hd hfloor hP) x v =
      encodeCoordinates s hd hfloor hP
        (fderiv ℝ normalizedCubicBlocks (decodeCoordinates s hd hfloor hP x) (decodeCoordinates s hd hfloor hP v)) := by
  let E := (encodeCoordinates s hd hfloor hP).toContinuousLinearMap
  let D := (decodeCoordinates s hd hfloor hP).toContinuousLinearMap
  have hq := (contDiff_normalizedCubicBlocks.differentiable (by simp)).differentiableAt
    (x := decodeCoordinates s hd hfloor hP x)
  have h := congrArg (fun L => L v) (E.hasFDerivAt.comp x (hq.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

theorem norm_fderiv_coordinateCubic_le_one {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) :
    ‖fderiv ℝ (coordinateCubic s hd hfloor hP) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [fderiv_coordinateCubic_apply, norm_encodeCoordinates, one_mul]
  exact (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd _).trans
    (euclideanNorm_decodeCoordinates_le s hd hfloor hP v)

theorem contDiff_coordinateOverlap : ContDiff ℝ ∞ (coordinateOverlap s hd hfloor hP) := by
  let O := (overlapOutputCoordinates d).toLinearMap.toContinuousLinearMap
  let D := (decodeCoordinates s hd hfloor hP).toContinuousLinearMap
  exact O.contDiff.comp (contDiff_extendedOverlap.comp D.contDiff)

theorem fderiv_coordinateOverlap_apply (x v : RealEuclidean P) :
    fderiv ℝ (coordinateOverlap s hd hfloor hP) x v =
      overlapOutputCoordinates d
        (fderiv ℝ extendedOverlap (decodeCoordinates s hd hfloor hP x) (decodeCoordinates s hd hfloor hP v)) := by
  let O := (overlapOutputCoordinates d).toLinearMap.toContinuousLinearMap
  let D := (decodeCoordinates s hd hfloor hP).toContinuousLinearMap
  have hH := (contDiff_extendedOverlap.differentiable (by simp)).differentiableAt
    (x := decodeCoordinates s hd hfloor hP x)
  have h := congrArg (fun L => L v) (O.hasFDerivAt.comp x (hH.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

/-- The full ambient operator norm, in the common Euclidean source. -/
theorem norm_fderiv_coordinateOverlap_le_budget (hd2 : 2 ≤ d)
    {x : RealEuclidean P}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor hP x))) :
    ‖fderiv ℝ (coordinateOverlap s hd hfloor hP) x‖ ≤ (P : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro v
  rw [fderiv_coordinateOverlap_apply, norm_overlapOutputCoordinates]
  exact (norm_fderiv_extendedOverlap_le_budget hx hd2 hfloor hP _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd hfloor hP v) (Nat.cast_nonneg _))

end PVMReverseBlocks
end NLQCLean
