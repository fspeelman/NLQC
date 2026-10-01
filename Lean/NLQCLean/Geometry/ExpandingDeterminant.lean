import NLQCLean.Geometry.NormDetBounds

/-!
# Determinant lower bound from uniform expansion

Apply the verified Hadamard bound to the inverse endomorphism.
This gives the equal-dimensional determinant estimate without an SVD API.
-/

namespace NLQCLean

open Module

/-- A real endomorphism expanding every vector by c expands volume by at least c^dim. -/
theorem pow_le_abs_det_of_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖v‖ ≤ ‖L v‖) : c ^ finrank ℝ E ≤ |L.det| := by
  have hinj : Function.Injective L := by
    intro x y hxy
    have h := hL (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (x - y)]
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective L ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  have hi (v : E) : ‖e.symm v‖ ≤ c⁻¹ * ‖v‖ := by
    have h : c * ‖e.symm v‖ ≤ ‖e (e.symm v)‖ := hL (e.symm v)
    rw [e.apply_symm_apply] at h
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).mpr (by linarith)
  let b := stdOrthonormalBasis ℝ E
  have hupper : |e.symm.toLinearMap.det| ≤ c⁻¹ ^ finrank ℝ E := by
    calc
      _ = e.symm.toLinearMap.normDet := e.symm.toLinearMap.normDet_eq_abs_det.symm
      _ ≤ ∏ i, ‖e.symm (b i)‖ := normDet_le_prod_norm _ b
      _ ≤ ∏ _ : Fin (finrank ℝ E), c⁻¹ := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i _
        simpa only [b.orthonormal.1 i, mul_one] using hi (b i)
      _ = _ := by simp
  have hdet : L.det * e.symm.toLinearMap.det = 1 := by
    rw [← LinearMap.det_comp]
    have hcomp : L.comp e.symm.toLinearMap = LinearMap.id := by
      ext v
      exact e.apply_symm_apply v
    rw [hcomp, LinearMap.det_id]
  have habs : |L.det| * |e.symm.toLinearMap.det| = 1 := by
    rw [← abs_mul, hdet, abs_one]
  have hbound : 1 ≤ |L.det| * c⁻¹ ^ finrank ℝ E := by
    rw [← habs]
    exact mul_le_mul_of_nonneg_left hupper (abs_nonneg _)
  have hpos : 0 < c ^ finrank ℝ E := pow_pos hc _
  rw [inv_pow, ← div_eq_mul_inv] at hbound
  simpa only [one_mul] using (le_div_iff₀ hpos).mp hbound

end NLQCLean
