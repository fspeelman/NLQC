import NLQCLean.Approx.SlimWitnessCalculus
import NLQCLean.Approx.NormalizedCubicWitness
import NLQCLean.Geometry.LocalMotionRank

/-!
# Normalized cubic extension of slim witnesses and its local rank

The block cubic fixes every normalized valid slim witness; its derivative
projects ambient directions to the linearized constraints after rescaling and contracts the
block Euclidean norm. The extended overlap splits into an explicit local term of real rank at
most `4d² − 3` and the explicit cross-Gram residual.
-/

namespace NLQCLean
namespace SlimReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : SlimReverseShape d K}

noncomputable def normalizedCubicBlocks (x : SlimReverseBlocks s) : SlimReverseBlocks s :=
  (cubicSphere x.1, cubicSphere x.2.1,
    rescaledCubicStiefel (d * s.1.r : ℝ) x.2.2.1,
    rescaledCubicStiefel (d * s.1.r : ℝ) x.2.2.2.1,
    rescaledCubicStiefel (d * frozenSupport d K : ℝ) x.2.2.2.2.1,
    rescaledCubicStiefel (d * frozenSupport d K : ℝ) x.2.2.2.2.2)

theorem contDiff_normalizedCubicBlocks :
    ContDiff ℝ ∞ (normalizedCubicBlocks : SlimReverseBlocks s → _) := by
  exact (contDiff_cubicSphere.comp contDiff_fst).prodMk
    ((contDiff_cubicSphere.comp (contDiff_fst.snd')).prodMk
      (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd')).prodMk
        (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd'.snd')).prodMk
          (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd'.snd'.snd')).prodMk
            ((contDiff_rescaledCubicStiefel _).comp (contDiff_snd.snd'.snd'.snd'.snd'))))))

theorem fderiv_normalizedCubicBlocks_apply (x v : SlimReverseBlocks s) :
    fderiv ℝ normalizedCubicBlocks x v =
      (fderiv ℝ cubicSphere x.1 v.1, fderiv ℝ cubicSphere x.2.1 v.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.1 v.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.2.1 v.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * frozenSupport d K : ℝ)) x.2.2.2.2.1 v.2.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * frozenSupport d K : ℝ)) x.2.2.2.2.2 v.2.2.2.2.2) := by
  have hl := hasFDerivAt_id (𝕜 := ℝ) x
  have h0 := (contDiff_cubicSphere.differentiable (by simp)).differentiableAt (x := x.1)
  have hd0 := h0.hasFDerivAt.comp x hl.fst
  have h1 := (contDiff_cubicSphere.differentiable (by simp)).differentiableAt (x := x.2.1)
  have hd1 := h1.hasFDerivAt.comp x hl.snd.fst
  have h2 := ((contDiff_rescaledCubicStiefel (d * s.1.r : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.1)
  have hd2 := h2.hasFDerivAt.comp x hl.snd.snd.fst
  have h3 := ((contDiff_rescaledCubicStiefel (d * s.1.r : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.1)
  have hd3 := h3.hasFDerivAt.comp x hl.snd.snd.snd.fst
  have h4 := ((contDiff_rescaledCubicStiefel (d * frozenSupport d K : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.2.1)
  have hd4 := h4.hasFDerivAt.comp x hl.snd.snd.snd.snd.fst
  have h5 := ((contDiff_rescaledCubicStiefel (d * frozenSupport d K : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.2.2)
  have hd5 := h5.hasFDerivAt.comp x hl.snd.snd.snd.snd.snd
  have h := hd0.prodMk (hd1.prodMk (hd2.prodMk (hd3.prodMk (hd4.prodMk hd5))))
  have he := congrArg (fun f => f v) h.fderiv
  convert he using 1 <;> rfl

theorem normalizedCubicBlocks_eq_self {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) : normalizedCubicBlocks x = x := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr := pos_d_mul_r (s := s) hd
  have hdK := pos_d_mul_support (s := s) hd
  have ha := rescaledCubicStiefel_of_gram _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.1)
  have hb := rescaledCubicStiefel_of_gram _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.2.1)
  have hta := rescaledCubicStiefel_of_gram _ hdK
    ((isIsometry_sqrt_smul_iff _ hdK.le _).mp hx.2.2.2.2.1)
  have htb := rescaledCubicStiefel_of_gram _ hdK
    ((isIsometry_sqrt_smul_iff _ hdK.le _).mp hx.2.2.2.2.2)
  simp only [normalizedCubicBlocks, cubicSphere_of_isUnitVector hη, cubicSphere_of_isUnitVector hg,
    ha, hb, hta, htb]

theorem isTangent_rescaled_fderiv_normalizedCubicBlocks {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : SlimReverseBlocks s) :
    IsTangent (rescaleBlocks x) (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr := pos_d_mul_r (s := s) hd
  have hdK := pos_d_mul_support (s := s) hd
  rw [fderiv_normalizedCubicBlocks_apply]
  refine ⟨?_, ?_, rescaledCubicStiefel_derivative_tangent hdr hx.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hdr hx.2.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hdK hx.2.2.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hdK hx.2.2.2.2.2 _⟩
  · change (vecInner x.1 (fderiv ℝ cubicSphere x.1 v.1)).re = 0
    rw [fderiv_cubicSphere_apply hη]
    exact (dCubicSphere_projection hη v.1).1
  · change (vecInner x.2.1 (fderiv ℝ cubicSphere x.2.1 v.2.1)).re = 0
    rw [fderiv_cubicSphere_apply hg]
    exact (dCubicSphere_projection hg v.2.1).1

theorem euclideanNorm_le_of_blockNorms_le {u v : SlimReverseBlocks s}
    (h : ∀ i, blockNorms u i ≤ blockNorms v i) : euclideanNorm u ≤ euclideanNorm v := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (blockNorms_nonneg u i) (h i) 2

theorem euclideanNorm_fderiv_normalizedCubicBlocks_le {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : SlimReverseBlocks s) :
    euclideanNorm (fderiv ℝ normalizedCubicBlocks x v) ≤ euclideanNorm v := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr := pos_d_mul_r (s := s) hd
  have hdK := pos_d_mul_support (s := s) hd
  have ha := (rescaledCubicStiefel_projection _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.1) v.2.2.1).2.2
  have hb := (rescaledCubicStiefel_projection _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.2.1) v.2.2.2.1).2.2
  have hta := (rescaledCubicStiefel_projection _ hdK
    ((isIsometry_sqrt_smul_iff _ hdK.le _).mp hx.2.2.2.2.1) v.2.2.2.2.1).2.2
  have htb := (rescaledCubicStiefel_projection _ hdK
    ((isIsometry_sqrt_smul_iff _ hdK.le _).mp hx.2.2.2.2.2) v.2.2.2.2.2).2.2
  apply euclideanNorm_le_of_blockNorms_le
  intro i
  rw [fderiv_normalizedCubicBlocks_apply]
  fin_cases i
  · simpa [blockNorms, fderiv_cubicSphere_apply hη] using
      (dCubicSphere_projection hη v.1).2.2
  · simpa [blockNorms, fderiv_cubicSphere_apply hg] using
      (dCubicSphere_projection hg v.2.1).2.2
  · simpa [blockNorms] using ha
  · simpa [blockNorms] using hb
  · simpa [blockNorms] using hta
  · simpa [blockNorms] using htb

/-- The globally defined cubic extension of the normalized overlap. -/
noncomputable def extendedOverlap (x : SlimReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  overlap (rescaleBlocks (normalizedCubicBlocks x))

theorem contDiff_extendedOverlap :
    ContDiff ℝ ∞ (extendedOverlap : SlimReverseBlocks s → _) := by
  let L := (rescaleBlocks (s := s)).toContinuousLinearMap
  exact contDiff_overlap.comp (L.contDiff.comp contDiff_normalizedCubicBlocks)

theorem extendedOverlap_eq_overlap {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    extendedOverlap x = overlap (rescaleBlocks x) := by
  rw [extendedOverlap, normalizedCubicBlocks_eq_self hx hd]

theorem fderiv_extendedOverlap_apply {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : SlimReverseBlocks s) :
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
noncomputable def extendedLocalTerm (x : SlimReverseBlocks s) :
    SlimReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  let z := rescaleBlocks x
  let L := rescaleBlocks.comp (fderiv ℝ normalizedCubicBlocks x).toLinearMap
  let a := (mulCLM (forward z)ᴴ).toLinearMap.comp ((fderiv ℝ forward z).toLinearMap.comp L)
  let b := (mulCLM (reverse z)ᴴ).toLinearMap.comp ((fderiv ℝ reverse z).toLinearMap.comp L)
  (-((mulLeftCLM (overlap z)).toLinearMap.comp b) +
    (mulRightCLM (overlap z)).toLinearMap.comp a)

theorem extendedLocalTerm_apply (x v : SlimReverseBlocks s) :
    let z := rescaleBlocks x
    let w := rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)
    extendedLocalTerm x v =
      -((reverse z)ᴴ * reverseVelocity z w) * overlap z +
        overlap z * ((forward z)ᴴ * forwardVelocity z w) := by
  simp [extendedLocalTerm, fderiv_forward_apply, fderiv_reverse_apply]

theorem finrank_extendedLocalTerm_le {x : SlimReverseBlocks s}
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
noncomputable def extendedResidual (x : SlimReverseBlocks s) :
    SlimReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (fderiv ℝ extendedOverlap x).toLinearMap - extendedLocalTerm x

theorem fderiv_extendedOverlap_decomposition (x : SlimReverseBlocks s) :
    (fderiv ℝ extendedOverlap x).toLinearMap = extendedLocalTerm x + extendedResidual x := by
  simp [extendedResidual]

theorem extendedResidual_apply {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : SlimReverseBlocks s) :
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

end SlimReverseBlocks
end NLQCLean
