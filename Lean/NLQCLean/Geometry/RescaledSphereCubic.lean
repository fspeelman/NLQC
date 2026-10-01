import NLQCLean.Geometry.MatrixPolynomialDegree

/-!
# Cubic projection for rescaled sphere blocks

For a sphere block normalized at squared radius `1 / n`, this file supplies
the cubic extension

`z ↦ (3 / 2) • z - (n / 2) • (sqNorm z • z)`.

At a point for which `sqrt n • z` is a unit vector, its full ambient
derivative is the ordinary real orthogonal sphere projection.  The file also
records the coordinatewise polynomial degree bound for rescaled sphere blocks.
-/

namespace NLQCLean

variable {ε : Type*} [Fintype ε]

/-- The cubic extension for a sphere block rescaled to squared radius `1 / n`. -/
noncomputable def rescaledCubicSphere (n : ℝ) (z : ε → ℂ) : ε → ℂ :=
  (3 / 2 : ℝ) • z - (n / 2 : ℝ) • (sqNorm z • z)

theorem contDiff_rescaledCubicSphere (n : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (rescaledCubicSphere n : (ε → ℂ) → (ε → ℂ)) := by
  have hid : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ε → ℂ => z) := contDiff_id
  exact (hid.const_smul (3 / 2 : ℝ)).sub
    ((contDiff_sqNorm.smul hid).const_smul (n / 2 : ℝ))

theorem sqNorm_real_smul (c : ℝ) (z : ε → ℂ) :
    sqNorm (c • z) = c ^ 2 * sqNorm z := by
  simp only [sqNorm, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  rw [pow_two]

/-- Scalar conjugation transports the unit-sphere cubic to the rescaled cubic. -/
theorem cubicSphere_smul_eq_rescaled (c : ℝ) (z : ε → ℂ) :
    cubicSphere (c • z) = c • rescaledCubicSphere (c ^ 2) z := by
  ext e
  simp only [cubicSphere, rescaledCubicSphere, Pi.smul_apply, Pi.sub_apply,
    Complex.real_smul]
  rw [sqNorm_real_smul]
  push_cast
  ring

theorem rescaledCubicSphere_eq_conjugate (n : ℝ) (hn : 0 < n) (z : ε → ℂ) :
    rescaledCubicSphere n z =
      (Real.sqrt n)⁻¹ • cubicSphere (Real.sqrt n • z) := by
  rw [cubicSphere_smul_eq_rescaled, Real.sq_sqrt hn.le, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul]

/-- The rescaled cubic fixes every vector on its rescaled sphere. -/
theorem rescaledCubicSphere_of_isUnitVector (n : ℝ) (hn : 0 < n) {z : ε → ℂ}
    (hz : IsUnitVector (Real.sqrt n • z)) : rescaledCubicSphere n z = z := by
  rw [rescaledCubicSphere_eq_conjugate n hn, cubicSphere_of_isUnitVector hz,
    smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul]

theorem dCubicSphere_real_smul {z : ε → ℂ} (hz : IsUnitVector z)
    (c : ℝ) (w : ε → ℂ) : dCubicSphere z (c • w) = c • dCubicSphere z w := by
  rw [← fderiv_cubicSphere_apply hz, map_smul, fderiv_cubicSphere_apply hz]

/-- At a rescaled unit vector, the full ambient derivative is the ordinary
sphere projection at `sqrt n • z`, acting on the unscaled ambient velocity. -/
theorem fderiv_rescaledCubicSphere_apply (n : ℝ) (hn : 0 < n) {z : ε → ℂ}
    (hz : IsUnitVector (Real.sqrt n • z)) (w : ε → ℂ) :
    fderiv ℝ (rescaledCubicSphere n) z w =
      dCubicSphere (Real.sqrt n • z) w := by
  apply fderiv_apply_eq_of_hasDerivAt_line
    ((contDiff_rescaledCubicSphere n).differentiable (by simp)).differentiableAt
  have hd := (hasDerivAt_cubicSphere hz (Real.sqrt n • w)).const_smul
    (Real.sqrt n)⁻¹
  have heq : (fun t : ℝ => rescaledCubicSphere n (z + t • w)) =
      fun t : ℝ => (Real.sqrt n)⁻¹ • cubicSphere
        (Real.sqrt n • z + t • (Real.sqrt n • w)) := by
    funext t
    rw [rescaledCubicSphere_eq_conjugate n hn, smul_add,
      smul_comm (Real.sqrt n) t]
  rw [heq]
  have hderiv : (Real.sqrt n)⁻¹ •
      dCubicSphere (Real.sqrt n • z) (Real.sqrt n • w) =
      dCubicSphere (Real.sqrt n • z) w := by
    rw [dCubicSphere_real_smul hz, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne', one_smul]
  rw [hderiv] at hd
  simpa only [Pi.smul_def] using hd

/-- The rescaled derivative is tangent after restoring the sphere scale. -/
theorem rescaledCubicSphere_tangent (n : ℝ) (hn : 0 < n) {z : ε → ℂ}
    (hz : IsUnitVector (Real.sqrt n • z)) (w : ε → ℂ) :
    (vecInner (Real.sqrt n • z)
      (Real.sqrt n • fderiv ℝ (rescaledCubicSphere n) z w)).re = 0 := by
  rw [fderiv_rescaledCubicSphere_apply n hn hz,
    ← dCubicSphere_real_smul hz]
  exact dCubicSphere_linearized hz (Real.sqrt n • w)

/-- The full ambient derivative of the rescaled sphere cubic contracts the
Euclidean norm. -/
theorem norm_fderiv_rescaledCubicSphere_apply_le (n : ℝ) (hn : 0 < n)
    {z : ε → ℂ} (hz : IsUnitVector (Real.sqrt n • z)) (w : ε → ℂ) :
    ‖WithLp.toLp 2 (fderiv ℝ (rescaledCubicSphere n) z w)‖ ≤
      ‖WithLp.toLp 2 w‖ := by
  rw [fderiv_rescaledCubicSphere_apply n hn hz]
  exact (dCubicSphere_projection hz w).2.2

/-- Applying the rescaled sphere cubic multiplies every coordinate degree by
at most three. -/
theorem polynomialDegree_rescaledCubicSphere
    {a D : ℕ} {ι : Type*} [Fintype ι]
    {f : RealEuclidean a → ι → ℂ}
    (hf : ∀ i, ComplexPolynomialDegreeLE D (fun x => f x i)) (n : ℝ) :
    ∀ i, ComplexPolynomialDegreeLE (3 * D)
      (fun x => rescaledCubicSphere n (f x) i) := by
  intro i
  have hsq := polynomialDegree_sqNorm hf
  have hcubic := ((ComplexPolynomialDegreeLE.ofReal hsq).mul (hf i)).real_smul
    (n / 2 : ℝ)
  have h := ((hf i).real_smul (3 / 2 : ℝ)).sub hcubic
  apply (h.mono (by omega)).congr
  intro x
  simp only [rescaledCubicSphere, Pi.sub_apply, Pi.smul_apply,
    Complex.real_smul]

end NLQCLean
