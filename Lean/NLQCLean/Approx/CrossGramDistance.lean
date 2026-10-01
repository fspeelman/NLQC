import NLQCLean.Approx.SharpFreezing

/-!
# Frobenius cross-Gram distance and leakage

These exact finite matrix identities transfer the
sharp frozen-dilation estimate to a reverse witness once its overlap identity
has been proved. No operator-norm approximation assumption is used.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

private theorem norm_sq_of_isometry {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : IsIsometry A) : ‖A‖ ^ 2 = Fintype.card n := by
  classical
  rw [frobNorm_sq]
  exact hA.sum_row_norm_sq

/-- Exact squared Frobenius residual from an isometric range. -/
theorem frobNorm_projection_residual_sq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (hB : IsIsometry B) :
    ‖A - B * (Bᴴ * A)‖ ^ 2 = ‖A‖ ^ 2 - ‖Bᴴ * A‖ ^ 2 := by
  rw [frobNorm_sub_sq, hB.frobNorm_mul_eq, frobInner_mul_left,
    frobInner_self_eq_norm_sq, Complex.ofReal_re]
  ring

/-- Orthogonal Pythagoras with arbitrary target U. -/
theorem crossGram_pythagoras {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (U : Matrix p n ℂ) (hB : IsIsometry B) :
    ‖A - B * U‖ ^ 2 = ‖A - B * (Bᴴ * A)‖ ^ 2 + ‖Bᴴ * A - U‖ ^ 2 := by
  rw [frobNorm_sub_sq A (B * U), hB.frobNorm_mul_eq, frobInner_mul_left,
    frobNorm_projection_residual_sq A B hB, frobNorm_sub_sq (Bᴴ * A) U]
  ring

/-- Passing to the cross-Gram matrix does not increase the approximation error. -/
theorem norm_crossGram_sub_le {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (U : Matrix p n ℂ) (hB : IsIsometry B) :
    ‖Bᴴ * A - U‖ ≤ ‖A - B * U‖ := by
  have h := crossGram_pythagoras A B U hB
  nlinarith [sq_nonneg ‖A - B * (Bᴴ * A)‖, norm_nonneg (Bᴴ * A - U),
    norm_nonneg (A - B * U)]

/-- Both leakage residuals have the same squared Frobenius norm for
isometries with a common domain. -/
theorem crossGram_residuals_sq {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℂ) (hA : IsIsometry A) (hB : IsIsometry B) :
    ‖A - B * (Bᴴ * A)‖ ^ 2 = (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 ∧
    ‖B - A * (Bᴴ * A)ᴴ‖ ^ 2 = (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 := by
  constructor
  · rw [frobNorm_projection_residual_sq A B hB, norm_sq_of_isometry hA]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      frobNorm_projection_residual_sq B A hA, norm_sq_of_isometry hB]
    rw [← Matrix.frobenius_norm_conjTranspose (Bᴴ * A)]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- W:leak in ordinary Frobenius coordinates. Setting `eta=sqrt(D)*delta`
gives both source residual bounds with their exact dimension factor. -/
theorem crossGram_approximation {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℂ) (U : Matrix n n ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    {η : ℝ} (hη : 0 ≤ η) (hclose : ‖A - B * U‖ ≤ η) :
    ‖Bᴴ * A - U‖ ≤ η ∧
      ‖A - B * (Bᴴ * A)‖ ^ 2 = (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 ∧
      ‖B - A * (Bᴴ * A)ᴴ‖ ^ 2 = (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 ∧
      (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 ≤ η ^ 2 := by
  obtain ⟨hleft, hright⟩ := crossGram_residuals_sq A B hA hB
  refine ⟨(norm_crossGram_sub_le A B U hB).trans hclose, hleft, hright, ?_⟩
  have hp := crossGram_pythagoras A B U hB
  rw [hleft] at hp
  have hc := sq_le_sq₀ (norm_nonneg (A - B * U)) hη
  nlinarith [hc.mpr hclose, sq_nonneg ‖Bᴴ * A - U‖]

/-- W:distance. The exact cross-Gram overlap identity transfers the original
frozen-dilation distance to the witness, with no loss in constants. -/
theorem norm_sub_eq_of_crossGram_eq {m l n p : Type*}
    [Fintype m] [Fintype l] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (F : Matrix l n ℂ) (E : Matrix l p ℂ) (U : Matrix p n ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (hF : IsIsometry F) (hE : IsIsometry E)
    (hcross : Bᴴ * A = Eᴴ * F) : ‖A - B * U‖ = ‖F - E * U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobNorm_sub_sq, frobNorm_sub_sq, norm_sq_of_isometry hA, norm_sq_of_isometry hF,
    hB.frobNorm_mul_eq, hE.frobNorm_mul_eq, frobInner_mul_left, frobInner_mul_left, hcross]

end NLQCLean
