import NLQCLean.Geometry.CubicProjection

/-!
# Cubic projection for rescaled isometry blocks

After dividing an n-column isometry by sqrt(n), use
`q_n(W) = (3 W - n W W† W)/2`. Scalar conjugation preserves the real
orthogonal projection, including its action on every ambient direction.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

/-- The cubic in normalized matrix-block coordinates. -/
noncomputable def rescaledCubicStiefel (n : ℝ) (W : Matrix m k ℂ) : Matrix m k ℂ :=
  (3 / 2 : ℝ) • W - (n / 2) • (W * Wᴴ * W)

omit [DecidableEq m] [DecidableEq k] in
theorem cubicStiefel_eq_real (W : Matrix m k ℂ) :
    cubicStiefel W = (3 / 2 : ℝ) • W - (1 / 2 : ℝ) • (W * Wᴴ * W) := by
  simp only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_inv, one_div, cubicStiefel]

omit [DecidableEq m] [DecidableEq k] in
theorem contDiff_rescaledCubicStiefel (n : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (rescaledCubicStiefel n : Matrix m k ℂ → Matrix m k ℂ) := by
  have hid : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun W : Matrix m k ℂ => W) := contDiff_id
  exact (hid.const_smul (3 / 2 : ℝ)).sub
    ((ContDiff.matrixMul (ContDiff.matrixMul hid (ContDiff.matrixConjTranspose hid)) hid).const_smul
      (n / 2))

omit [DecidableEq m] [DecidableEq k] in
/-- Conjugation by a scalar rescaling is a polynomial identity. -/
theorem cubicStiefel_smul_eq_rescaled (c : ℝ) (W : Matrix m k ℂ) :
    cubicStiefel (c • W) = c • rescaledCubicStiefel (c ^ 2) W := by
  rw [cubicStiefel_eq_real]
  simp only [rescaledCubicStiefel, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
  congr 1 <;> congr 1 <;> ring

omit [DecidableEq m] [DecidableEq k] in
theorem rescaledCubicStiefel_eq_conjugate (n : ℝ) (hn : 0 < n) (W : Matrix m k ℂ) :
    rescaledCubicStiefel n W = (Real.sqrt n)⁻¹ • cubicStiefel (Real.sqrt n • W) := by
  rw [cubicStiefel_smul_eq_rescaled, Real.sq_sqrt hn.le, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul]

omit [Fintype k] [DecidableEq m] in
/-- The rescaled Gram equation is exactly the original isometry condition. -/
theorem isIsometry_sqrt_smul_iff (n : ℝ) (hn : 0 ≤ n) (W : Matrix m k ℂ) :
    IsIsometry (Real.sqrt n • W) ↔ n • (Wᴴ * W) = 1 := by
  simp only [IsIsometry, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hn]

omit [DecidableEq m] in
theorem rescaledCubicStiefel_of_gram (n : ℝ) (hn : 0 < n) {W : Matrix m k ℂ}
    (hW : n • (Wᴴ * W) = 1) : rescaledCubicStiefel n W = W := by
  have hV := (isIsometry_sqrt_smul_iff n hn.le W).mpr hW
  rw [rescaledCubicStiefel_eq_conjugate n hn, cubicStiefel_of_isometry hV,
    smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul]

theorem dCubicStiefel_real_smul {V : Matrix m k ℂ} (hV : IsIsometry V)
    (c : ℝ) (Z : Matrix m k ℂ) : dCubicStiefel V (c • Z) = c • dCubicStiefel V Z := by
  rw [← fderiv_cubicStiefel_apply hV, map_smul, fderiv_cubicStiefel_apply hV]

/-- The full ambient derivative is the unscaled orthogonal projection at
sqrt(n) W, acting on the original ambient velocity Z. -/
theorem fderiv_rescaledCubicStiefel_apply (n : ℝ) (hn : 0 < n) {W : Matrix m k ℂ}
    (hW : n • (Wᴴ * W) = 1) (Z : Matrix m k ℂ) :
    fderiv ℝ (rescaledCubicStiefel n) W Z = dCubicStiefel (Real.sqrt n • W) Z := by
  have hV := (isIsometry_sqrt_smul_iff n hn.le W).mpr hW
  apply fderiv_apply_eq_of_hasDerivAt_line
    ((contDiff_rescaledCubicStiefel n).differentiable (by simp)).differentiableAt
  have hd := (hasDerivAt_cubicStiefel hV (Real.sqrt n • Z)).const_smul (Real.sqrt n)⁻¹
  have heq : (fun t : ℝ => rescaledCubicStiefel n (W + t • Z)) =
      fun t : ℝ => (Real.sqrt n)⁻¹ • cubicStiefel
        (Real.sqrt n • W + t • (Real.sqrt n • Z)) := by
    funext t
    rw [rescaledCubicStiefel_eq_conjugate n hn, smul_add, smul_comm (Real.sqrt n) t]
  rw [heq]
  simpa only [Pi.smul_def, dCubicStiefel_real_smul hV, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul] using hd

/-- Rescaling preserves the tangent constraint, orthogonal complement, and
norm contraction of the ambient cubic derivative. -/
theorem rescaledCubicStiefel_projection (n : ℝ) (hn : 0 < n) {W : Matrix m k ℂ}
    (hW : n • (Wᴴ * W) = 1) (Z : Matrix m k ℂ) :
    let P := fderiv ℝ (rescaledCubicStiefel n) W Z
    Wᴴ * P + Pᴴ * W = 0 ∧
      (∀ Y, Wᴴ * Y + Yᴴ * W = 0 → (frobInner (Z - P) Y).re = 0) ∧ ‖P‖ ≤ ‖Z‖ := by
  dsimp only
  rw [fderiv_rescaledCubicStiefel_apply n hn hW]
  have hV := (isIsometry_sqrt_smul_iff n hn.le W).mpr hW
  have hp := dCubicStiefel_projection hV Z
  have hlin : ∀ Y : Matrix m k ℂ,
      (Real.sqrt n • W)ᴴ * Y + Yᴴ * (Real.sqrt n • W) =
        Real.sqrt n • (Wᴴ * Y + Yᴴ * W) := by
    intro Y
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_add]
  refine ⟨?_, ?_, hp.2.2⟩
  · rw [hlin] at hp
    exact (smul_eq_zero.mp hp.1).resolve_left (Real.sqrt_pos.mpr hn).ne'
  · intro Y hY
    apply hp.2.1 Y
    rw [hlin, hY, smul_zero]

end NLQCLean
