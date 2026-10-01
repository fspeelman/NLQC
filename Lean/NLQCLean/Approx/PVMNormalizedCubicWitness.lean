import NLQCLean.Approx.NormalizedCubicWitness
import NLQCLean.Approx.PVMBlockNormalization
import NLQCLean.Approx.PVMCoordinateCount
import NLQCLean.Geometry.RescaledSphereCubic
import NLQCLean.Rigidity.PVMWitnessCalculus

/-!
# The normalized blockwise cubic extension for PVM witnesses

The dependent garbage family is projected one
unit-vector sphere at a time.  The resource and four matrix blocks use the
existing sphere and rescaled Stiefel cubics.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace PVMReverseBlocks

variable {d K : ℕ} {s : PVMReverseShape d K}

/-- Apply the rescaled sphere cubic separately to every dependent garbage
vector. -/
noncomputable def normalizedGarbageCubic
    (g : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ :=
  fun i => rescaledCubicSphere (d ^ 2 : ℝ) (g i)

theorem contDiff_normalizedGarbageCubic :
    ContDiff ℝ ∞ (normalizedGarbageCubic (d := d) (s := s)) := by
  rw [contDiff_pi]
  intro i
  have hi : ContDiff ℝ ∞
      (fun g : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ => g i) :=
    contDiff_pi.mp contDiff_id i
  exact (contDiff_rescaledCubicSphere (ε := Fin (s.2.rank i) × Fin (s.2.rank i))
    (d ^ 2 : ℝ)).comp hi

theorem fderiv_normalizedGarbageCubic_apply
    (g v : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    fderiv ℝ (normalizedGarbageCubic (d := d) (s := s)) g v =
      fun i => fderiv ℝ (rescaledCubicSphere (d ^ 2 : ℝ)) (g i) (v i) := by
  have hcomponent (i : Fin d × Fin d) :
      HasFDerivAt
        (fun g : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ =>
          rescaledCubicSphere (d ^ 2 : ℝ) (g i))
        ((fderiv ℝ (rescaledCubicSphere (d ^ 2 : ℝ)) (g i)).comp
          (ContinuousLinearMap.proj i)) g := by
    exact ((contDiff_rescaledCubicSphere (ε := Fin (s.2.rank i) × Fin (s.2.rank i))
      (d ^ 2 : ℝ)).differentiable (by simp)).differentiableAt.hasFDerivAt.comp g
        (hasFDerivAt_apply i g)
  have h : HasFDerivAt (normalizedGarbageCubic (d := d) (s := s))
      (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (rescaledCubicSphere (d ^ 2 : ℝ)) (g i)).comp
          (ContinuousLinearMap.proj i)) g := by
    rw [hasFDerivAt_pi]
    intro i
    simpa only [normalizedGarbageCubic] using hcomponent i
  have he := congrArg (fun L => L v) h.fderiv
  funext i
  have hei := congrFun he i
  simpa using hei

/-- Cubic projection in the normalized coordinates of all six independent
blocks, with one sphere cubic for each garbage vector. -/
noncomputable def normalizedCubicBlocks (x : PVMReverseBlocks s) : PVMReverseBlocks s :=
  (cubicSphere x.1,
    normalizedGarbageCubic x.2.1,
    rescaledCubicStiefel (d * s.1.r : ℝ) x.2.2.1,
    rescaledCubicStiefel (d * s.1.r : ℝ) x.2.2.2.1,
    rescaledCubicStiefel (s.supportSize : ℝ) x.2.2.2.2.1,
    rescaledCubicStiefel (s.supportSize : ℝ) x.2.2.2.2.2)

theorem contDiff_normalizedCubicBlocks :
    ContDiff ℝ ∞ (normalizedCubicBlocks : PVMReverseBlocks s → _) := by
  exact (contDiff_cubicSphere.comp contDiff_fst).prodMk
    ((contDiff_normalizedGarbageCubic.comp contDiff_fst.snd').prodMk
      (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd')).prodMk
        (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd'.snd')).prodMk
          (((contDiff_rescaledCubicStiefel _).comp
            (contDiff_fst.snd'.snd'.snd'.snd')).prodMk
            ((contDiff_rescaledCubicStiefel _).comp
              (contDiff_snd.snd'.snd'.snd'.snd'))))))

/-- The full ambient derivative acts blockwise, including pointwise on the
dependent garbage family. -/
theorem fderiv_normalizedCubicBlocks_apply (x v : PVMReverseBlocks s) :
    fderiv ℝ normalizedCubicBlocks x v =
      (fderiv ℝ cubicSphere x.1 v.1,
        (fun i => fderiv ℝ (rescaledCubicSphere (d ^ 2 : ℝ)) (x.2.1 i) (v.2.1 i)),
        fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.1 v.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.2.1 v.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (s.supportSize : ℝ)) x.2.2.2.2.1 v.2.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (s.supportSize : ℝ)) x.2.2.2.2.2 v.2.2.2.2.2) := by
  have hl := hasFDerivAt_id (𝕜 := ℝ) x
  have h0 := (contDiff_cubicSphere.differentiable (by simp)).differentiableAt
    (x := x.1)
  have hd0 := h0.hasFDerivAt.comp x hl.fst
  have h1 := (contDiff_normalizedGarbageCubic.differentiable (by simp)).differentiableAt
    (x := x.2.1)
  have hd1 := h1.hasFDerivAt.comp x hl.snd.fst
  have h2 := ((contDiff_rescaledCubicStiefel (d * s.1.r : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.1)
  have hd2 := h2.hasFDerivAt.comp x hl.snd.snd.fst
  have h3 := ((contDiff_rescaledCubicStiefel (d * s.1.r : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.1)
  have hd3 := h3.hasFDerivAt.comp x hl.snd.snd.snd.fst
  have h4 := ((contDiff_rescaledCubicStiefel (s.supportSize : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.2.1)
  have hd4 := h4.hasFDerivAt.comp x hl.snd.snd.snd.snd.fst
  have h5 := ((contDiff_rescaledCubicStiefel (s.supportSize : ℝ)).differentiable
    (by simp)).differentiableAt (x := x.2.2.2.2.2)
  have hd5 := h5.hasFDerivAt.comp x hl.snd.snd.snd.snd.snd
  have h := hd0.prodMk (hd1.prodMk (hd2.prodMk (hd3.prodMk (hd4.prodMk hd5))))
  have he := congrArg (fun f => f v) h.fderiv
  change fderiv ℝ normalizedCubicBlocks x v =
    (fderiv ℝ cubicSphere x.1 v.1,
      fderiv ℝ normalizedGarbageCubic x.2.1 v.2.1,
      fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.1 v.2.2.1,
      fderiv ℝ (rescaledCubicStiefel (d * s.1.r : ℝ)) x.2.2.2.1 v.2.2.2.1,
      fderiv ℝ (rescaledCubicStiefel (s.supportSize : ℝ)) x.2.2.2.2.1 v.2.2.2.2.1,
      fderiv ℝ (rescaledCubicStiefel (s.supportSize : ℝ)) x.2.2.2.2.2 v.2.2.2.2.2) at he
  rw [fderiv_normalizedGarbageCubic_apply] at he
  exact he

theorem normalizedCubicBlocks_eq_self {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) : normalizedCubicBlocks x = x := by
  have hη : IsUnitVector x.1 := by simpa [rescaleBlocks] using hx.1
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by exact_mod_cast s.supportSize_pos hd
  have hg : normalizedGarbageCubic x.2.1 = x.2.1 := by
    funext i
    exact rescaledCubicSphere_of_isUnitVector _ hd2 (isUnitVector_rescaled_garbage hx i)
  have ha := rescaledCubicStiefel_of_gram _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.1)
  have hb := rescaledCubicStiefel_of_gram _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.2.1)
  have hta := rescaledCubicStiefel_of_gram _ hS
    ((isIsometry_sqrt_smul_iff _ hS.le _).mp hx.2.2.2.2.1)
  have htb := rescaledCubicStiefel_of_gram _ hS
    ((isIsometry_sqrt_smul_iff _ hS.le _).mp hx.2.2.2.2.2)
  change normalizedCubicBlocks x =
    (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2)
  simp only [normalizedCubicBlocks, cubicSphere_of_isUnitVector hη, hg, ha, hb, hta, htb]

/-- At a normalized valid witness, the rescaled derivative satisfies every
resource, per-garbage-vector, and matrix tangent equation. -/
theorem isTangent_rescaled_fderiv_normalizedCubicBlocks {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : PVMReverseBlocks s) :
    IsTangent (rescaleBlocks x) (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := by
  have hη : IsUnitVector x.1 := by simpa [rescaleBlocks] using hx.1
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by exact_mod_cast s.supportSize_pos hd
  rw [fderiv_normalizedCubicBlocks_apply]
  refine ⟨?_, ?_,
    rescaledCubicStiefel_derivative_tangent hdr hx.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hdr hx.2.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hS hx.2.2.2.2.1 _,
    rescaledCubicStiefel_derivative_tangent hS hx.2.2.2.2.2 _⟩
  · change (vecInner x.1 (fderiv ℝ cubicSphere x.1 v.1)).re = 0
    rw [fderiv_cubicSphere_apply hη]
    exact (dCubicSphere_projection hη v.1).1
  · intro i
    exact rescaledCubicSphere_tangent _ hd2 (isUnitVector_rescaled_garbage hx i) (v.2.1 i)

theorem blockNorms_nonneg (v : PVMReverseBlocks s) (i : Fin 6) : 0 ≤ blockNorms v i := by
  fin_cases i <;> simp [blockNorms]

theorem euclideanNorm_le_of_blockNorms_le {u v : PVMReverseBlocks s}
    (h : ∀ i, blockNorms u i ≤ blockNorms v i) : euclideanNorm u ≤ euclideanNorm v := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (blockNorms_nonneg u i) (h i) 2

/-- The blockwise cubic derivative contracts the explicit Euclidean norm in
every ambient direction. -/
theorem euclideanNorm_fderiv_normalizedCubicBlocks_le {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : PVMReverseBlocks s) :
    euclideanNorm (fderiv ℝ normalizedCubicBlocks x v) ≤ euclideanNorm v := by
  have hη : IsUnitVector x.1 := by simpa [rescaleBlocks] using hx.1
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by exact_mod_cast s.supportSize_pos hd
  have hg :
      Real.sqrt (∑ i, ‖WithLp.toLp 2
        (fderiv ℝ (rescaledCubicSphere (d ^ 2 : ℝ)) (x.2.1 i) (v.2.1 i))‖ ^ 2) ≤
        Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_fderiv_rescaledCubicSphere_apply_le _ hd2
        (isUnitVector_rescaled_garbage hx i) (v.2.1 i)) 2
  have ha := (rescaledCubicStiefel_projection _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.1) v.2.2.1).2.2
  have hb := (rescaledCubicStiefel_projection _ hdr
    ((isIsometry_sqrt_smul_iff _ hdr.le _).mp hx.2.2.2.1) v.2.2.2.1).2.2
  have hta := (rescaledCubicStiefel_projection _ hS
    ((isIsometry_sqrt_smul_iff _ hS.le _).mp hx.2.2.2.2.1) v.2.2.2.2.1).2.2
  have htb := (rescaledCubicStiefel_projection _ hS
    ((isIsometry_sqrt_smul_iff _ hS.le _).mp hx.2.2.2.2.2) v.2.2.2.2.2).2.2
  apply euclideanNorm_le_of_blockNorms_le
  intro i
  rw [fderiv_normalizedCubicBlocks_apply]
  fin_cases i
  · simpa [blockNorms, fderiv_cubicSphere_apply hη] using
      (dCubicSphere_projection hη v.1).2.2
  · simpa [blockNorms] using hg
  · simpa [blockNorms] using ha
  · simpa [blockNorms] using hb
  · simpa [blockNorms] using hta
  · simpa [blockNorms] using htb

end PVMReverseBlocks

end NLQCLean
