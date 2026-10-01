import NLQCLean.Geometry.NormDetBounds
import NLQCLean.Geometry.PolynomialImageVolumeHypothesis

/-!
# The determinant estimate for a thickened map


All products here use the real Euclidean norm.
-/

namespace NLQCLean

open Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The adjoint of `(u,v) ↦ L u + c v` on the Euclidean product. -/
noncomputable def thickenedAdjoint (L : E →L[ℝ] F) (c : ℝ) :
    F →ₗ[ℝ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp
    (L.adjoint.toLinearMap.prod (c • LinearMap.id))

theorem thickenedAdjoint_apply (L : E →L[ℝ] F) (c : ℝ) (x : F) :
    thickenedAdjoint L c x = WithLp.toLp 2 (L.adjoint x, c • x) := rfl

theorem thickenedAdjoint_adjoint_apply (L : E →L[ℝ] F) (c : ℝ)
    (z : WithLp 2 (E × F)) :
    (thickenedAdjoint L c).adjoint z = L z.fst + c • z.snd := by
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.adjoint_inner_right]
  simp only [thickenedAdjoint_apply, WithLp.prod_inner_apply,
    inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [L.adjoint_inner_left]
  rfl

theorem thickenedAdjoint_gram (L : E →L[ℝ] F) (c : ℝ) :
    (thickenedAdjoint L c).adjoint.comp (thickenedAdjoint L c) =
      (L.comp L.adjoint).toLinearMap + c ^ 2 • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simp only [thickenedAdjoint_apply, WithLp.prod_inner_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    inner_add_right, inner_smul_left, inner_smul_right]
  rw [L.adjoint_inner_left (L.adjoint x) y]
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem sqrt_det_thickenedGram (L : E →L[ℝ] F) (c : ℝ) :
    Real.sqrt (LinearMap.det ((L.comp L.adjoint).toLinearMap + c ^ 2 • LinearMap.id)) =
      (thickenedAdjoint L c).normDet := by
  have h : (thickenedAdjoint L c).normDet ^ 2 =
      LinearMap.det ((L.comp L.adjoint).toLinearMap + c ^ 2 • LinearMap.id) := by
    simpa [thickenedAdjoint_gram] using
      (thickenedAdjoint L c).normDet_sq
  rw [← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

theorem norm_thickenedAdjoint_le (L : E →L[ℝ] F) {c : ℝ} (hc : 0 ≤ c) (x : F) :
    ‖thickenedAdjoint L c x‖ ≤ ‖L.adjoint x‖ + c * ‖x‖ := by
  have hs := WithLp.prod_norm_sq_eq_of_L2 (thickenedAdjoint L c x)
  change ‖thickenedAdjoint L c x‖ ^ 2 = ‖L.adjoint x‖ ^ 2 + ‖c • x‖ ^ 2 at hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at hs
  have hn := norm_nonneg (thickenedAdjoint L c x)
  have hp := mul_nonneg hc (norm_nonneg x)
  nlinarith [norm_nonneg (L.adjoint x), mul_nonneg (norm_nonneg (L.adjoint x)) hp]

/-- Determinant comparison from a rank-plus-error decomposition. -/
theorem sqrt_det_thickenedGram_le (L T R : E →L[ℝ] F)
    (hL : L = T + R) {Λ μ c : ℝ} (hμ : 0 ≤ μ) (hμΛ : μ ≤ Λ) (hc : 0 ≤ c)
    (hΛ : ‖L‖ ≤ Λ) (hR : ‖R‖ ≤ μ) {t : ℕ}
    (hT : finrank ℝ T.range ≤ t) (ht : t ≤ finrank ℝ F) :
    Real.sqrt (LinearMap.det ((L.comp L.adjoint).toLinearMap + c ^ 2 • LinearMap.id)) ≤
      (Λ + c) ^ t * (μ + c) ^ (finrank ℝ F - t) := by
  rw [sqrt_det_thickenedGram]
  apply normDet_le_of_subspace_rank_bound (thickenedAdjoint L c) T.range
    (add_nonneg hμ hc) (by linarith) hT ht
  · intro x _
    calc
      ‖thickenedAdjoint L c x‖ ≤ ‖L.adjoint x‖ + c * ‖x‖ := norm_thickenedAdjoint_le L hc x
      _ ≤ Λ * ‖x‖ + c * ‖x‖ := by
        gcongr
        calc
          ‖L.adjoint x‖ ≤ ‖L.adjoint‖ * ‖x‖ := L.adjoint.le_opNorm x
          _ ≤ Λ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]; gcongr
      _ = (Λ + c) * ‖x‖ := (add_mul _ _ _).symm
  · intro x hx
    have hxT : T.adjoint x = 0 := by
      change x ∈ T.adjoint.ker
      rwa [← T.orthogonal_range]
    have hxL : L.adjoint x = R.adjoint x := by
      rw [hL, map_add, add_apply, hxT, zero_add]
    calc
      ‖thickenedAdjoint L c x‖ ≤ ‖L.adjoint x‖ + c * ‖x‖ := norm_thickenedAdjoint_le L hc x
      _ = ‖R.adjoint x‖ + c * ‖x‖ := by rw [hxL]
      _ ≤ μ * ‖x‖ + c * ‖x‖ := by
        gcongr
        calc
          ‖R.adjoint x‖ ≤ ‖R.adjoint‖ * ‖x‖ := R.adjoint.le_opNorm x
          _ ≤ μ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]; gcongr
      _ = (μ + c) * ‖x‖ := (add_mul _ _ _).symm

/-- Split consecutive Euclidean coordinates, preserving the l2 norm. -/
noncomputable def euclideanProductCoordinates (a m : ℕ) :
    RealEuclidean (a + m) ≃ₗᵢ[ℝ] WithLp 2 (RealEuclidean a × RealEuclidean m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))

/-- The linear thickening `(u,v) ↦ L u + c v`, on Euclidean coordinates. -/
noncomputable def thickenedLinearMap {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) (c : ℝ) :
    RealEuclidean (a + m) →L[ℝ] RealEuclidean m :=
  (thickenedAdjoint L c).toContinuousLinearMap.adjoint.comp
    (euclideanProductCoordinates a m).toContinuousLinearEquiv.toContinuousLinearMap

theorem thickenedLinearMap_apply {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) (c : ℝ) (z : RealEuclidean (a + m)) :
    thickenedLinearMap L c z = L (euclideanProductCoordinates a m z).fst +
      c • (euclideanProductCoordinates a m z).snd :=
  thickenedAdjoint_adjoint_apply L c _

theorem thickenedLinearMap_gram {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) (c : ℝ) :
    ((thickenedLinearMap L c).comp (thickenedLinearMap L c).adjoint).toLinearMap =
      (L.comp L.adjoint).toLinearMap + c ^ 2 • LinearMap.id := by
  rw [← thickenedAdjoint_gram]
  apply LinearMap.ext
  intro x
  simp only [thickenedLinearMap, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The exact top-Jacobian contract for applying the image-volume bound to a thickened map. -/
theorem topRealJacobian_thickenedLinearMap_le {a m : ℕ}
    (L T R : RealEuclidean a →L[ℝ] RealEuclidean m)
    (hL : L = T + R) {Λ μ c : ℝ} (hμ : 0 ≤ μ) (hμΛ : μ ≤ Λ) (hc : 0 ≤ c)
    (hΛ : ‖L‖ ≤ Λ) (hR : ‖R‖ ≤ μ) {t : ℕ}
    (hT : finrank ℝ T.range ≤ t) (ht : t ≤ m) :
    topRealJacobian (thickenedLinearMap L c) ≤ (Λ + c) ^ t * (μ + c) ^ (m - t) := by
  rw [topRealJacobian, thickenedLinearMap_gram]
  have hm : finrank ℝ (RealEuclidean m) = m := by simp [RealEuclidean]
  simpa only [hm] using sqrt_det_thickenedGram_le L T R hL hμ hμΛ hc hΛ hR hT
    (by simpa only [hm] using ht)

end NLQCLean
