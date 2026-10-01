import NLQCLean.Geometry.RescaledCubicProjection
import NLQCLean.Approx.WitnessDifferentialBounds

/-!
# The normalized six-block cubic extension

The block cubic fixes every normalized valid witness. Its derivative
projects every ambient direction to the original linearized constraints
after rescaling, and contracts the explicit Euclidean sum of block norms.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem rescaledCubicStiefel_derivative_tangent {m k : Type*}
    [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {n : ℝ} (hn : 0 < n) {W : Matrix m k ℂ}
    (hW : IsIsometry (Real.sqrt n • W)) (Z : Matrix m k ℂ) :
    let P := fderiv ℝ (rescaledCubicStiefel n) W Z
    (Real.sqrt n • W)ᴴ * (Real.sqrt n • P) +
      (Real.sqrt n • P)ᴴ * (Real.sqrt n • W) = 0 := by
  have h := (rescaledCubicStiefel_projection n hn
    ((isIsometry_sqrt_smul_iff n hn.le W).mp hW) Z).1
  dsimp only
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← smul_add, h, smul_zero]

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

/-- Cubic projection in the normalized coordinates of all six independent blocks. -/
noncomputable def normalizedCubicBlocks (x : ReverseBlocks s) : ReverseBlocks s :=
  (cubicSphere x.1, cubicSphere x.2.1,
    rescaledCubicStiefel (d * s.r : ℝ) x.2.2.1,
    rescaledCubicStiefel (d * s.r : ℝ) x.2.2.2.1,
    rescaledCubicStiefel (d * K : ℝ) x.2.2.2.2.1,
    rescaledCubicStiefel (d * K : ℝ) x.2.2.2.2.2)

theorem contDiff_normalizedCubicBlocks :
    ContDiff ℝ ∞ (normalizedCubicBlocks : ReverseBlocks s → _) := by
  exact (contDiff_cubicSphere.comp contDiff_fst).prodMk
    ((contDiff_cubicSphere.comp (contDiff_fst.snd')).prodMk
      (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd')).prodMk
        (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd'.snd')).prodMk
          (((contDiff_rescaledCubicStiefel _).comp (contDiff_fst.snd'.snd'.snd'.snd')).prodMk
            ((contDiff_rescaledCubicStiefel _).comp (contDiff_snd.snd'.snd'.snd'.snd'))))))

theorem fderiv_normalizedCubicBlocks_apply (x v : ReverseBlocks s) :
    fderiv ℝ normalizedCubicBlocks x v =
      (fderiv ℝ cubicSphere x.1 v.1, fderiv ℝ cubicSphere x.2.1 v.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * s.r : ℝ)) x.2.2.1 v.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * s.r : ℝ)) x.2.2.2.1 v.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * K : ℝ)) x.2.2.2.2.1 v.2.2.2.2.1,
        fderiv ℝ (rescaledCubicStiefel (d * K : ℝ)) x.2.2.2.2.2 v.2.2.2.2.2) := by
  have hl := hasFDerivAt_id (𝕜 := ℝ) x
  have h0 := (contDiff_cubicSphere.differentiable (by simp)).differentiableAt (x := x.1)
  have hd0 := h0.hasFDerivAt.comp x hl.fst
  have h1 := (contDiff_cubicSphere.differentiable (by simp)).differentiableAt (x := x.2.1)
  have hd1 := h1.hasFDerivAt.comp x hl.snd.fst
  have h2 := ((contDiff_rescaledCubicStiefel (d * s.r : ℝ)).differentiable (by simp)).differentiableAt (x := x.2.2.1)
  have hd2 := h2.hasFDerivAt.comp x hl.snd.snd.fst
  have h3 := ((contDiff_rescaledCubicStiefel (d * s.r : ℝ)).differentiable (by simp)).differentiableAt (x := x.2.2.2.1)
  have hd3 := h3.hasFDerivAt.comp x hl.snd.snd.snd.fst
  have h4 := ((contDiff_rescaledCubicStiefel (d * K : ℝ)).differentiable (by simp)).differentiableAt (x := x.2.2.2.2.1)
  have hd4 := h4.hasFDerivAt.comp x hl.snd.snd.snd.snd.fst
  have h5 := ((contDiff_rescaledCubicStiefel (d * K : ℝ)).differentiable (by simp)).differentiableAt (x := x.2.2.2.2.2)
  have hd5 := h5.hasFDerivAt.comp x hl.snd.snd.snd.snd.snd
  have h := hd0.prodMk (hd1.prodMk (hd2.prodMk (hd3.prodMk (hd4.prodMk hd5))))
  have he := congrArg (fun f => f v) h.fderiv
  convert he using 1 <;> rfl

theorem normalizedCubicBlocks_eq_self {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) : normalizedCubicBlocks x = x := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
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

theorem isTangent_rescaled_fderiv_normalizedCubicBlocks {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : ReverseBlocks s) :
    IsTangent (rescaleBlocks x) (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
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

theorem blockNorms_nonneg (v : ReverseBlocks s) (i : Fin 6) : 0 ≤ blockNorms v i := by
  fin_cases i <;> simp [blockNorms]

theorem euclideanNorm_le_of_blockNorms_le {u v : ReverseBlocks s}
    (h : ∀ i, blockNorms u i ≤ blockNorms v i) : euclideanNorm u ≤ euclideanNorm v := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (blockNorms_nonneg u i) (h i) 2

/-- Contraction uses l2 across the six blocks, including l2 within the two vectors. -/
theorem euclideanNorm_fderiv_normalizedCubicBlocks_le {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (v : ReverseBlocks s) :
    euclideanNorm (fderiv ℝ normalizedCubicBlocks x v) ≤ euclideanNorm v := by
  have hη : IsUnitVector x.1 := hx.1
  have hg : IsUnitVector x.2.1 := hx.2.1
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
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

end ReverseBlocks
end NLQCLean
