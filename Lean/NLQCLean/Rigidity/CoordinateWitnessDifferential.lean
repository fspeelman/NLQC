import NLQCLean.Approx.WitnessEuclideanCoordinates

/-!
# Ambient differential bounds in common real Euclidean coordinates

The padded cubic kills dummy coordinates. The extended overlap is a
map R^P → R^(2d^4), with actual continuous-linear derivative norm at most
P and an explicit rank-(4d²-3) term plus an error of norm at most delta*P.
-/

namespace NLQCLean
namespace ReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d)

/-- The normalized raw overlap in common Euclidean source/output coordinates. -/
noncomputable def coordinateRawOverlap (x : RealEuclidean (witnessCoordinateBudget d K)) :
    RealEuclidean (2 * d ^ 4) :=
  overlapOutputCoordinates d (overlap (rescaleBlocks (decodeCoordinates s hd x)))

/-- The six normalized cubics, with zero output in every dummy coordinate. -/
noncomputable def coordinateCubic (x : RealEuclidean (witnessCoordinateBudget d K)) :
    RealEuclidean (witnessCoordinateBudget d K) :=
  encodeCoordinates s hd (normalizedCubicBlocks (decodeCoordinates s hd x))

/-- The global cubic overlap extension in genuine Euclidean coordinates. -/
noncomputable def coordinateOverlap (x : RealEuclidean (witnessCoordinateBudget d K)) :
    RealEuclidean (2 * d ^ 4) :=
  overlapOutputCoordinates d (extendedOverlap (decodeCoordinates s hd x))

theorem coordinateOverlap_eq_raw_comp_cubic (x : RealEuclidean (witnessCoordinateBudget d K)) :
    coordinateOverlap s hd x = coordinateRawOverlap s hd (coordinateCubic s hd x) := by
  simp only [coordinateOverlap, coordinateRawOverlap, coordinateCubic,
    decode_encodeCoordinates, extendedOverlap]

theorem coordinateCubic_zero_padding (x : RealEuclidean (witnessCoordinateBudget d K))
    {j : Fin (witnessCoordinateBudget d K)} (hj : j ∉ Set.range (coordinateEmbedding s hd)) :
    coordinateCubic s hd x j = 0 :=
  encodeCoordinates_zero_padding s hd _ hj

theorem coordinateCubic_eq_self {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x)))
    (hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) : coordinateCubic s hd x = x := by
  rw [coordinateCubic, normalizedCubicBlocks_eq_self hx hd]
  exact encode_decodeCoordinates_of_padding s hd x hpad

theorem coordinateOverlap_eq_raw {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    coordinateOverlap s hd x = coordinateRawOverlap s hd x := by
  rw [coordinateOverlap, extendedOverlap_eq_overlap hx hd]
  rfl

theorem contDiff_coordinateCubic : ContDiff ℝ ∞ (coordinateCubic s hd) := by
  let E := (encodeCoordinates s hd).toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  exact E.contDiff.comp (contDiff_normalizedCubicBlocks.comp D.contDiff)

theorem fderiv_coordinateCubic_apply (x v : RealEuclidean (witnessCoordinateBudget d K)) :
    fderiv ℝ (coordinateCubic s hd) x v =
      encodeCoordinates s hd
        (fderiv ℝ normalizedCubicBlocks (decodeCoordinates s hd x) (decodeCoordinates s hd v)) := by
  let E := (encodeCoordinates s hd).toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  have hq := (contDiff_normalizedCubicBlocks.differentiable (by simp)).differentiableAt
    (x := decodeCoordinates s hd x)
  have h := congrArg (fun L => L v) (E.hasFDerivAt.comp x (hq.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

theorem norm_fderiv_coordinateCubic_le_one {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    ‖fderiv ℝ (coordinateCubic s hd) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [fderiv_coordinateCubic_apply, norm_encodeCoordinates, one_mul]
  exact (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd _).trans
    (euclideanNorm_decodeCoordinates_le s hd v)

theorem contDiff_coordinateOverlap : ContDiff ℝ ∞ (coordinateOverlap s hd) := by
  let O := (overlapOutputCoordinates d).toLinearMap.toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  exact O.contDiff.comp (contDiff_extendedOverlap.comp D.contDiff)

theorem fderiv_coordinateOverlap_apply (x v : RealEuclidean (witnessCoordinateBudget d K)) :
    fderiv ℝ (coordinateOverlap s hd) x v =
      overlapOutputCoordinates d
        (fderiv ℝ extendedOverlap (decodeCoordinates s hd x) (decodeCoordinates s hd v)) := by
  let O := (overlapOutputCoordinates d).toLinearMap.toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  have hH := (contDiff_extendedOverlap.differentiable (by simp)).differentiableAt
    (x := decodeCoordinates s hd x)
  have h := congrArg (fun L => L v) (O.hasFDerivAt.comp x (hH.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

/-- Transport the explicit local term by the fixed coordinate maps. -/
noncomputable def coordinateLocalTerm (x : RealEuclidean (witnessCoordinateBudget d K)) :
    RealEuclidean (witnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd x)).comp (decodeCoordinates s hd))).toContinuousLinearMap

/-- Transport the explicit error term by the same fixed coordinate maps. -/
noncomputable def coordinateResidual (x : RealEuclidean (witnessCoordinateBudget d K)) :
    RealEuclidean (witnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedResidual (decodeCoordinates s hd x)).comp (decodeCoordinates s hd))).toContinuousLinearMap

theorem fderiv_coordinateOverlap_decomposition (x : RealEuclidean (witnessCoordinateBudget d K)) :
    fderiv ℝ (coordinateOverlap s hd) x = coordinateLocalTerm s hd x + coordinateResidual s hd x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_coordinateOverlap_apply]
  change overlapOutputCoordinates d (fderiv ℝ extendedOverlap (decodeCoordinates s hd x)
    (decodeCoordinates s hd v)) =
      overlapOutputCoordinates d (extendedLocalTerm (decodeCoordinates s hd x) (decodeCoordinates s hd v)) +
        overlapOutputCoordinates d (extendedResidual (decodeCoordinates s hd x) (decodeCoordinates s hd v))
  rw [← map_add]
  congr 1
  exact congrArg (fun L => L (decodeCoordinates s hd v))
    (fderiv_extendedOverlap_decomposition (decodeCoordinates s hd x))

theorem finrank_coordinateLocalTerm_le {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    Module.finrank ℝ (LinearMap.range (coordinateLocalTerm s hd x).toLinearMap) ≤ 4 * d ^ 2 - 3 := by
  change Module.finrank ℝ (LinearMap.range ((overlapOutputCoordinates d).toLinearMap.comp
    ((extendedLocalTerm (decodeCoordinates s hd x)).comp (decodeCoordinates s hd)))) ≤ _
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (finrank_extendedLocalTerm_le hx hd))

/-- The full ambient operator norm on R^P → R^(2d^4), at every valid decoded witness. -/
theorem norm_fderiv_coordinateOverlap_le_budget (hd2 : 2 ≤ d)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    ‖fderiv ℝ (coordinateOverlap s hd) x‖ ≤ (witnessCoordinateBudget d K : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro v
  rw [fderiv_coordinateOverlap_apply, norm_overlapOutputCoordinates]
  exact (norm_fderiv_extendedOverlap_le_budget hx hd2 _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd v) (Nat.cast_nonneg _))

theorem norm_coordinateResidual_le_budget (hd2 : 2 ≤ d)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ‖coordinateResidual s hd x‖ ≤ δ * witnessCoordinateBudget d K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (Nat.cast_nonneg _))
  intro v
  change ‖overlapOutputCoordinates d
    (extendedResidual (decodeCoordinates s hd x) (decodeCoordinates s hd v))‖ ≤ _
  rw [norm_overlapOutputCoordinates]
  exact (norm_extendedResidual_le_budget hx hd2 hδ hdef _).trans
    (mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd v)
      (mul_nonneg hδ (Nat.cast_nonneg _)))

/-- TP7's ambient rank-plus-small-error statement on the common Euclidean spaces. -/
theorem exists_coordinateOverlap_rank_error_decomposition (hd2 : 2 ≤ d)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : RealEuclidean (witnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlap s hd) x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 4 * d ^ 2 - 3 ∧
      ‖fderiv ℝ (coordinateOverlap s hd) x‖ ≤ (witnessCoordinateBudget d K : ℝ) ∧
      ‖R‖ ≤ δ * witnessCoordinateBudget d K :=
  ⟨coordinateLocalTerm s hd x, coordinateResidual s hd x, fderiv_coordinateOverlap_decomposition s hd x,
    finrank_coordinateLocalTerm_le s hd hx, norm_fderiv_coordinateOverlap_le_budget s hd hd2 hx,
    norm_coordinateResidual_le_budget s hd hd2 hx hδ hdef⟩

end ReverseBlocks
end NLQCLean
