import NLQCLean.Geometry.DirectVolume.LevelFamily
import NLQCLean.Geometry.SardSlices

/-!
# Direct image-volume route: singular values of the strata

For a set `J` of active constraints, the masked level map
`(x, b') ↦ ((g_t(x) for t ∈ J, b'_t for t ∉ J), p(x))` has the full target
`(Fin L → ℝ) × ℝ^m`. By Sard slices, for almost every level vector `b` its
singular values over `b` form a null set of `ℝ^m` (L3). At a regular point the
gradients of `p` and of the active constraints are linearly independent (L4).
Roadmap step D2 (`D0-PROOF.md` §6).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function MeasureTheory
open scoped ContDiff

variable {a m L D : ℕ}

/-- The derivative of a bounded polynomial map. -/
noncomputable def mapDeriv (p : PolyMap a m D) (x : RealEuclidean a) :
    RealEuclidean a →L[ℝ] RealEuclidean m :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm :
      (Fin m → ℝ) →L[ℝ] RealEuclidean m).comp
    (ContinuousLinearMap.pi fun i => gradE (p.coordinates i) x)

theorem mapDeriv_apply (p : PolyMap a m D) (x v : RealEuclidean a) (i : Fin m) :
    mapDeriv p x v i = gradE (p.coordinates i) x v := by
  simp [mapDeriv]

theorem hasFDerivAt_eval (p : PolyMap a m D) (x : RealEuclidean a) :
    HasFDerivAt p.eval (mapDeriv p x) x := by
  have h : HasFDerivAt (fun y : RealEuclidean a => fun i => evalE (p.coordinates i) y)
      (ContinuousLinearMap.pi fun i => gradE (p.coordinates i) x) x :=
    hasFDerivAt_pi.mpr fun i => (hasStrictFDerivAt_evalE _ x).hasFDerivAt
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.hasFDerivAt.comp x h

/-- The masked level map of a stratum `J`. -/
noncomputable def maskedLevelMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) :
    RealEuclidean a × (Fin L → ℝ) → (Fin L → ℝ) × RealEuclidean m :=
  fun z => (fun t => if t ∈ J then evalE (g t) z.1 else z.2 t, p.eval z.1)

/-- Its derivative. -/
noncomputable def maskedLevelDeriv (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (x : RealEuclidean a) :
    RealEuclidean a × (Fin L → ℝ) →L[ℝ] (Fin L → ℝ) × RealEuclidean m :=
  (ContinuousLinearMap.pi fun t =>
      if t ∈ J then (gradE (g t) x).comp (ContinuousLinearMap.fst ℝ _ _)
      else (ContinuousLinearMap.proj t).comp (ContinuousLinearMap.snd ℝ _ _)).prod
    ((mapDeriv p x).comp (ContinuousLinearMap.fst ℝ _ _))

theorem hasFDerivAt_maskedLevelMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L))
    (z : RealEuclidean a × (Fin L → ℝ)) :
    HasFDerivAt (maskedLevelMap p g J) (maskedLevelDeriv p g J z.1) z := by
  refine HasFDerivAt.prodMk (hasFDerivAt_pi.mpr fun t => ?_) ((hasFDerivAt_eval p z.1).comp z
    hasFDerivAt_fst)
  by_cases ht : t ∈ J
  · simp only [ht, ite_true]
    exact (hasStrictFDerivAt_evalE (g t) z.1).hasFDerivAt.comp z hasFDerivAt_fst
  · simp only [ht, ite_false]
    have hsnd : HasFDerivAt (Prod.snd : RealEuclidean a × (Fin L → ℝ) → (Fin L → ℝ))
        (ContinuousLinearMap.snd ℝ _ _) z := hasFDerivAt_snd
    exact (hasFDerivAt_apply t z.2).comp z hsnd

theorem contDiff_maskedLevelMap (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) :
    ContDiff ℝ ∞ (maskedLevelMap p g J) := by
  refine ContDiff.prodMk (contDiff_pi.mpr fun t => ?_)
    ((PolyMap.contDiff_eval_top p).comp contDiff_fst)
  by_cases ht : t ∈ J
  · simp only [ht, ite_true]
    exact (contDiff_evalE (g t)).comp contDiff_fst
  · simp only [ht, ite_false]
    exact (contDiff_apply ℝ ℝ t).comp contDiff_snd

/-- Values over the level `b` with a singular preimage. -/
def singularLevelValues (p : PolyMap a m D) (g : Fin L → MvPolynomial (Fin a) ℝ)
    (J : Finset (Fin L)) (b : Fin L → ℝ) : Set (RealEuclidean m) :=
  {y | ∃ x, (∀ t ∈ J, evalE (g t) x = b t) ∧ p.eval x = y ∧
    ¬ Surjective (fderiv ℝ (maskedLevelMap p g J) (x, b))}

/-- **L3.** For almost every level vector, the singular values form a null set. -/
theorem ae_volume_singularLevelValues (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) :
    ∀ᵐ b : Fin L → ℝ, volume (singularLevelValues p g J b) = 0 := by
  filter_upwards [ae_ae_regular_slice (contDiff_maskedLevelMap p g J)] with b hb
  rw [ae_iff] at hb
  refine measure_mono_null (fun y hy => ?_) hb
  obtain ⟨x, hxJ, hxy, hsing⟩ := hy
  intro hreg
  refine hsing (hreg (x, b) ?_)
  simp only [maskedLevelMap, Prod.mk.injEq]
  refine ⟨funext fun t => ?_, hxy⟩
  by_cases ht : t ∈ J
  · simp [ht, hxJ t ht]
  · simp [ht]

/-- The gradient vectors of the components of `p` and of the active constraints. -/
noncomputable def lagrangeGradients (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) (x : RealEuclidean a) :
    Fin m ⊕ J → (Fin a → ℝ)
  | .inl i => fun k => evalE (pderiv k (p.coordinates i)) x
  | .inr t => fun k => evalE (pderiv k (g t)) x

/-- **L4.** At a regular point of the masked level map the gradients of `p` and
of the active constraints are linearly independent. -/
theorem linearIndependent_of_surjective_masked (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (J : Finset (Fin L)) {x : RealEuclidean a}
    {b' : Fin L → ℝ} (hs : Surjective (fderiv ℝ (maskedLevelMap p g J) (x, b'))) :
    LinearIndependent ℝ (lagrangeGradients p g J x) := by
  classical
  rw [(hasFDerivAt_maskedLevelMap p g J (x, b')).fderiv] at hs
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Realize the coefficients as directional derivatives.
  obtain ⟨⟨xd, bd⟩, hxd⟩ := hs (fun t => if ht : t ∈ J then c (.inr ⟨t, ht⟩) else 0,
    WithLp.toLp 2 fun i => c (.inl i))
  simp only [maskedLevelDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
    comp_apply, ContinuousLinearMap.coe_fst', Prod.mk.injEq] at hxd
  obtain ⟨h1, h2⟩ := hxd
  have hval : ∀ σ, ∑ k, lagrangeGradients p g J x σ k * xd k = c σ := by
    rintro (i | ⟨t, ht⟩)
    · have := congrArg (fun w : RealEuclidean m => w i) h2
      simp only [mapDeriv_apply, gradE_apply] at this
      simpa [lagrangeGradients] using this
    · have := congrFun h1 t
      simp only [ContinuousLinearMap.pi_apply] at this
      rw [ite_eq_left ht, dite_eq_left ht] at this
      simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_fst',
        gradE_apply] at this
      simpa [lagrangeGradients] using this
  -- Pair the relation with `xd`.
  have hsq : ∑ σ, c σ * c σ = 0 := by
    calc ∑ σ, c σ * c σ = ∑ σ, c σ * ∑ k, lagrangeGradients p g J x σ k * xd k := by
          simp only [hval]
      _ = ∑ k, (∑ σ, c σ • lagrangeGradients p g J x σ) k * xd k := by
          simp only [Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => by ring
      _ = 0 := by rw [hc]; simp
  intro σ
  have hnn : ∀ τ ∈ Finset.univ, 0 ≤ c τ * c τ := fun τ _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq σ (Finset.mem_univ σ)
  exact mul_self_eq_zero.mp this

end NLQCLean.DirectVolume
