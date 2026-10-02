import NLQCLean.Geometry.DirectVolume.Lagrange

/-!
# Direct image-volume route: regularity of the Lagrange level sets

For almost every parameter `(b, v)` the Lagrange map `H` is regular along its
level set over `(b, v)` (L7), and for almost every `(b, v)` and almost every
`z ∈ ℝ^m` the equal-dimensional map `K = (H, π_I ∘ x)` is regular along its level
set over `((b, v), z)` (L8). On the open part of the Lagrange system the
derivative of `H` is injective on vectors with no `x` component (L9).
Roadmap steps D2 and D5 (`D0-PROOF.md` §8).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function MeasureTheory
open scoped ContDiff

variable {a m L D : ℕ}

/-- `liftX` as a continuous linear map. -/
noncomputable def liftXL (a m : ℕ) : (Fin (a + m + L) → ℝ) →L[ℝ] RealEuclidean a :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).symm :
      (Fin a → ℝ) →L[ℝ] RealEuclidean a).comp
    (ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (ixL a m k))

@[simp] theorem liftXL_apply (q : Fin (a + m + L) → ℝ) : liftXL a m q = liftX q := by
  ext k; simp [liftXL, liftX]

theorem contDiff_lagrangeMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) :
    ContDiff ℝ ∞ (lagrangeMap p g J) :=
  ContDiff.prodMk (contDiff_pi.mpr fun _ => contDiff_eval_top _)
    (contDiff_pi.mpr fun _ => contDiff_eval_top _)

/-- The equal-dimensional map `K = (H, π_I ∘ x)`. -/
noncomputable def lagrangeCoordMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (I : Fin m → Fin a)
    (q : Fin (a + m + L) → ℝ) : ((Fin L → ℝ) × (Fin a → ℝ)) × RealEuclidean m :=
  (lagrangeMap p g J q, coordinateProjection I (liftX q))

theorem contDiff_lagrangeCoordMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (I : Fin m → Fin a) :
    ContDiff ℝ ∞ (lagrangeCoordMap p g J I) := by
  refine (contDiff_lagrangeMap p g J).prodMk ?_
  have : (fun q => coordinateProjection I (liftX q)) =
      ((coordinateProjectionL I).comp (liftXL a m) : (Fin (a + m + L) → ℝ) →L[ℝ] _) := by
    funext q; simp [coordinateProjectionL]
  rw [this]
  exact ContinuousLinearMap.contDiff _

instance isAddHaarMeasure_volume_params :
    (volume : Measure ((Fin L → ℝ) × (Fin a → ℝ))).IsAddHaarMeasure := by
  have := isAddHaarMeasure_volume_pi (Fin L)
  have := isAddHaarMeasure_volume_pi (Fin a)
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- **L7.** For almost every parameter, `H` is regular along its level set. -/
theorem ae_regular_lagrangeMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) :
    ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ), ∀ q, lagrangeMap p g J q = bv →
      Surjective (fderiv ℝ (lagrangeMap p g J) q) := by
  have hnull := criticalImage_volume_eq_zero (contDiff_lagrangeMap p g J)
    (s := {q | ¬ Surjective (fderiv ℝ (lagrangeMap p g J) q)}) fun q hq => hq
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with bv hbv q hq
  by_contra h
  exact hbv ⟨q, h, hq⟩

/-- **L8.** For almost every parameter and almost every slice value, `K` is
regular along its level set. -/
theorem ae_ae_regular_lagrangeCoordMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (I : Fin m → Fin a) :
    ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ), ∀ᵐ z : RealEuclidean m, ∀ q,
      lagrangeCoordMap p g J I q = (bv, z) →
        Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q) :=
  ae_ae_regular_slice (contDiff_lagrangeCoordMap p g J I)

/-- The derivative of `H` along vectors with no `x` component. -/
noncomputable def lagrangeVertical (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (x : RealEuclidean a)
    (w : Fin (a + m + L) → ℝ) : (Fin L → ℝ) × (Fin a → ℝ) :=
  (fun t => if t ∈ J then 0 else w (imL a m t),
    fun k => ∑ i, w (ilL a m i) * evalE (pderiv k (p.coordinates i)) x +
      ∑ t ∈ J, w (imL a m t) * evalE (pderiv k (g t)) x)

/-- Along a vertical line `H` is affine. -/
theorem lagrangeMap_add_smul_vertical (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (q w : Fin (a + m + L) → ℝ)
    (hw : ∀ k, w (ixL a m k) = 0) (s : ℝ) :
    lagrangeMap p g J (q + s • w) =
      lagrangeMap p g J q + s • lagrangeVertical p g J (liftX q) w := by
  have hx : ∀ P : MvPolynomial (Fin a) ℝ,
      eval (q + s • w) (rename (ixL a m) P) = eval q (rename (ixL a m) P) := by
    intro P
    simp only [eval_rename]
    rw [show (q + s • w) ∘ ixL a m = q ∘ ixL a m from funext fun k => by simp [hw k]]
  simp only [lagrangeMap, lagrangeVertical, Prod.mk_add_mk, Prod.smul_mk, Prod.mk.injEq]
  constructor
  · funext t
    by_cases ht : t ∈ J
    · simp [lagrangeValuePoly, ht, hx]
    · simp [lagrangeValuePoly, ht]
  · funext k
    simp only [lagrangeGradPoly, map_add, map_sum, map_mul, eval_X, hx, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, evalE_liftX]
    simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    ring_nf

/-- **L9 (kernel lemma).** On the open part of the Lagrange system, a vector with
no `x` component in the kernel of `DH` vanishes. -/
theorem eq_zero_of_fderiv_lagrangeMap_vertical (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) {b : Fin L → ℝ}
    {q : Fin (a + m + L) → ℝ} (hq : q ∈ lagrangeOpen p g J b) {w : Fin (a + m + L) → ℝ}
    (hw : ∀ k, w (ixL a m k) = 0) (hker : fderiv ℝ (lagrangeMap p g J) q w = 0) : w = 0 := by
  classical
  -- The derivative along `w` is the vertical part.
  have hline : HasDerivAt (fun s : ℝ => lagrangeMap p g J (q + s • w))
      (lagrangeVertical p g J (liftX q) w) 0 := by
    have : (fun s : ℝ => lagrangeMap p g J (q + s • w)) =
        fun s => lagrangeMap p g J q + s • lagrangeVertical p g J (liftX q) w := by
      funext s; exact lagrangeMap_add_smul_vertical p g J q w hw s
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (lagrangeVertical p g J (liftX q) w)).const_add (lagrangeMap p g J q)
  have hchain : HasDerivAt (fun s : ℝ => lagrangeMap p g J (q + s • w))
      (fderiv ℝ (lagrangeMap p g J) q w) 0 := by
    have hd : HasDerivAt (fun s : ℝ => q + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q
    have hf : HasFDerivAt (lagrangeMap p g J) (fderiv ℝ (lagrangeMap p g J) q) (q + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]
      exact ((contDiff_lagrangeMap p g J).differentiable (by simp)).differentiableAt.hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hd
  have hvert : lagrangeVertical p g J (liftX q) w = 0 := by
    rw [hline.unique hchain, hker]
  simp only [lagrangeVertical, Prod.mk_eq_zero] at hvert
  obtain ⟨hv1, hv2⟩ := hvert
  -- Independence of the gradients kills the multiplier components.
  set c : Fin m ⊕ J → ℝ := fun σ => match σ with
    | .inl i => w (ilL a m i)
    | .inr t => w (imL a m t) with hc
  have hrel : ∑ σ, c σ • lagrangeGradients p g J (liftX q) σ = 0 := by
    funext k
    have := congrFun hv2 k
    simp only [Pi.zero_apply] at this ⊢
    rw [Finset.sum_apply, Fintype.sum_sum_type]
    rw [← Finset.sum_coe_sort J] at this
    simpa [hc, lagrangeGradients] using this
  have hc0 := Fintype.linearIndependent_iff.mp hq.1 c hrel
  funext r
  refine Fin.addCases (fun r₁ => ?_) (fun t => ?_) r
  · refine Fin.addCases (fun k => ?_) (fun i => ?_) r₁
    · exact hw k
    · exact hc0 (.inl i)
  · by_cases ht : t ∈ J
    · exact hc0 (.inr ⟨t, ht⟩)
    · have := congrFun hv1 t
      simpa [ht, imL] using this

end NLQCLean.DirectVolume
