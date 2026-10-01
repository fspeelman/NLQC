import NLQCLean.Geometry.RealFrobeniusInner
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The unitary Cayley chart

On the skew-Hermitian Frobenius unit ball,
the Cayley map is an injective unitary parametrization. We use the ambient
matrix inverse derivative and retain the Frobenius norm throughout.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Topology _root_.ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixCayley (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 + A) * (1 - A)⁻¹

theorem isUnit_one_sub_matrix_of_norm_lt_one (A : Matrix n n ℂ) (hA : ‖A‖ < 1) :
    IsUnit (1 - A) := isUnit_one_sub_of_norm_lt_one hA

theorem matrixCayley_eq_two_inv_sub_one (A : Matrix n n ℂ) (hA : IsUnit (1 - A)) :
    matrixCayley A = (2 : ℝ) • (1 - A)⁻¹ - 1 := by
  have hi : (1 - A) * (1 - A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  rw [matrixCayley, two_smul]
  calc
    _ = (1 - A)⁻¹ + (1 - A)⁻¹ - (1 - A) * (1 - A)⁻¹ := by noncomm_ring
    _ = _ := by rw [hi]

theorem isIsometry_matrixCayley (A : Matrix n n ℂ) (hA : Aᴴ = -A)
    (hi : IsUnit (1 - A)) : IsIsometry (matrixCayley A) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hi
  have he : (1 + A)ᴴ * (1 + A) = (1 - A)ᴴ * (1 - A) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hA]
    noncomm_ring
  change ((1 + A) * (1 - A)⁻¹)ᴴ * ((1 + A) * (1 - A)⁻¹) = 1
  rw [Matrix.conjTranspose_mul]
  calc
    _ = ((1 - A)⁻¹)ᴴ * ((1 + A)ᴴ * (1 + A)) * (1 - A)⁻¹ := by noncomm_ring
    _ = ((1 - A)⁻¹)ᴴ * ((1 - A)ᴴ * (1 - A)) * (1 - A)⁻¹ := by rw [he]
    _ = ((1 - A) * (1 - A)⁻¹)ᴴ * ((1 - A) * (1 - A)⁻¹) := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdet]; simp

theorem matrixCayley_injectiveOn :
    Set.InjOn (matrixCayley (n := n)) {A | IsUnit (1 - A)} := by
  intro A hA B hB he
  rw [matrixCayley_eq_two_inv_sub_one A hA, matrixCayley_eq_two_inv_sub_one B hB] at he
  have hi : (1 - A)⁻¹ = (1 - B)⁻¹ := by
    exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) (sub_left_injective he)
  have h := Matrix.inv_inj hi ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  exact sub_right_injective h

/-- The nonsingular matrix inverse has the usual real ambient derivative at units. -/
theorem hasFDerivAt_matrixInverse (A : Matrix n n ℂ) (hA : IsUnit A) :
    HasFDerivAt (fun X : Matrix n n ℂ => X⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) A⁻¹ A⁻¹) A := by
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hA.unit
  simp only [Matrix.coe_units_inv, hA.unit_spec] at h
  have he : (fun X : Matrix n n ℂ => X⁻¹) = Ring.inverse :=
    funext fun X => Matrix.nonsing_inv_eq_ringInverse X
  rw [he]
  exact h

noncomputable def matrixCayleyDerivative (A : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (2 : ℝ) • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (1 - A)⁻¹ (1 - A)⁻¹

theorem matrixCayleyDerivative_apply (A B : Matrix n n ℂ) :
    matrixCayleyDerivative A B = (2 : ℝ) • ((1 - A)⁻¹ * B * (1 - A)⁻¹) := rfl

/-- The derivative is on the full real matrix space. -/
theorem hasFDerivAt_matrixCayley (A : Matrix n n ℂ) (hA : IsUnit (1 - A)) :
    HasFDerivAt matrixCayley (matrixCayleyDerivative A) A := by
  have hi := (hasFDerivAt_matrixInverse (1 - A) hA).comp A
    ((hasFDerivAt_const (1 : Matrix n n ℂ) A).sub (hasFDerivAt_id A))
  have hc := ((hasFDerivAt_const (1 : Matrix n n ℂ) A).add (hasFDerivAt_id A)).mul' hi
  change HasFDerivAt matrixCayley _ A at hc
  apply hc.congr_fderiv
  apply ContinuousLinearMap.ext
  intro B
  change (1 + A) * (-((1 - A)⁻¹ * (0 - B) * (1 - A)⁻¹)) + (0 + B) * (1 - A)⁻¹ =
    (2 : ℝ) • ((1 - A)⁻¹ * B * (1 - A)⁻¹)
  simp only [zero_add, zero_sub, mul_neg, neg_mul, neg_neg]
  have he := matrixCayley_eq_two_inv_sub_one A hA
  change (1 + A) * (1 - A)⁻¹ = _ at he
  rw [two_smul] at he ⊢
  calc
    _ = B * (1 - A)⁻¹ + ((1 + A) * (1 - A)⁻¹) * (B * (1 - A)⁻¹) := by noncomm_ring
    _ = _ := by rw [he]; noncomm_ring

theorem matrixCayleyDerivative_cancel (A B : Matrix n n ℂ) (hA : IsUnit (1 - A)) :
    (1 - A) * matrixCayleyDerivative A B * (1 - A) = (2 : ℝ) • B := by
  rw [matrixCayleyDerivative_apply, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    _ = ((1 - A) * (1 - A)⁻¹) * B * ((1 - A)⁻¹ * (1 - A)) := by noncomm_ring
    _ = B := by
      rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)]
      simp

private theorem norm_one_sub_mul_le_two (A X : Matrix n n ℂ) (hA : ‖A‖ ≤ 1) :
    ‖(1 - A) * X‖ ≤ 2 * ‖X‖ := by
  calc
    _ = ‖X - A * X‖ := by rw [Matrix.sub_mul, Matrix.one_mul]
    _ ≤ ‖X‖ + ‖A * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ + ‖A‖ * ‖X‖ := add_le_add le_rfl (norm_mul_le A X)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hA (norm_nonneg X)]

private theorem norm_mul_one_sub_le_two (A X : Matrix n n ℂ) (hA : ‖A‖ ≤ 1) :
    ‖X * (1 - A)‖ ≤ 2 * ‖X‖ := by
  calc
    _ = ‖X - X * A‖ := by rw [Matrix.mul_sub, Matrix.mul_one]
    _ ≤ ‖X‖ + ‖X * A‖ := norm_sub_le _ _
    _ ≤ ‖X‖ + ‖X‖ * ‖A‖ := add_le_add le_rfl (norm_mul_le X A)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hA (norm_nonneg X)]

/-- G:chartjac: every ambient velocity expands by at least one half. -/
theorem half_norm_le_matrixCayleyDerivative (A B : Matrix n n ℂ) (hA : ‖A‖ < 1) :
    (1 / 2 : ℝ) * ‖B‖ ≤ ‖matrixCayleyDerivative A B‖ := by
  have hc := matrixCayleyDerivative_cancel A B (isUnit_one_sub_matrix_of_norm_lt_one A hA)
  have h₁ := norm_one_sub_mul_le_two A (matrixCayleyDerivative A B) hA.le
  have h₂ := norm_mul_one_sub_le_two A ((1 - A) * matrixCayleyDerivative A B) hA.le
  rw [hc, norm_smul] at h₂
  norm_num at h₂
  linarith

/-- Translating the derivative back by the unitary gives a skew-Hermitian matrix. -/
theorem matrixCayleyDerivative_left_skew (A B : Matrix n n ℂ)
    (hA : Aᴴ = -A) (hB : Bᴴ = -B) (hi : IsUnit (1 - A)) :
    ((matrixCayley A)ᴴ * matrixCayleyDerivative A B)ᴴ =
      -((matrixCayley A)ᴴ * matrixCayleyDerivative A B) := by
  have he : (matrixCayley A)ᴴ * (1 - A)⁻¹ = ((1 - A)⁻¹)ᴴ := by
    rw [matrixCayley, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, hA, ← sub_eq_add_neg, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hi), Matrix.mul_one]
  have hL : (matrixCayley A)ᴴ * matrixCayleyDerivative A B =
      (2 : ℝ) • (((1 - A)⁻¹)ᴴ * B * (1 - A)⁻¹) := by
    rw [matrixCayleyDerivative_apply, Matrix.mul_smul]
    congr 1
    calc
      _ = ((matrixCayley A)ᴴ * (1 - A)⁻¹) * B * (1 - A)⁻¹ := by noncomm_ring
      _ = _ := by rw [he]
  rw [hL]
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hB, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  rw [Matrix.mul_assoc]

/-- Smoothness holds on the whole open inverse domain, before restricting to skew matrices. -/
theorem contDiffAt_matrixCayley (A : Matrix n n ℂ) (hA : IsUnit (1 - A)) :
    ContDiffAt ℝ ∞ matrixCayley A := by
  have hi : ContDiffAt ℝ ∞ (fun X : Matrix n n ℂ => X⁻¹) (1 - A) := by
    have he : (fun X : Matrix n n ℂ => X⁻¹) = Ring.inverse :=
      funext fun X => Matrix.nonsing_inv_eq_ringInverse X
    rw [he]
    simpa only [hA.unit_spec] using contDiffAt_ringInverse ℝ (n := ∞) hA.unit
  exact (contDiffAt_const.add contDiffAt_id).mul
    (hi.comp A (contDiffAt_const.sub contDiffAt_id))

end NLQCLean
