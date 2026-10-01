import NLQCLean.Approx.PVMSharpFreezing
import NLQCLean.LinearAlgebra.CrossedSinglet

/-!
# Corrected reference projections and near-Bell freezing

The reference correction contracts the normalized Choi-vector distance.
This supplies the actual reference-state comparison used to bound both
messages. Flat column spectra also permit a smaller total garbage allocation.
The source is `lem:bell-compression` in the revised robust companion.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Contract both Choi-reference indices after a correction controlled by
Bob's output label. Alice's output and both environments remain present. -/
def nearBellReferenceProjection {d : ℕ} {δ εA εB : Type*}
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    Matrix (δ × εA) (δ × εB) ℂ :=
  fun x y => ∑ a, ∑ b, C y.1 a b * F (x, y) (a, b)

theorem nearBellReferenceProjection_sub {d : ℕ} {δ εA εB : Type*}
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (F G : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    nearBellReferenceProjection C (F - G) =
      nearBellReferenceProjection C F - nearBellReferenceProjection C G := by
  ext x y
  simp only [nearBellReferenceProjection, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The unnormalized reference contraction has operator norm at most
`sqrt d`; after Choi and reference-pair normalization it is a contraction. -/
theorem nearBellReferenceProjection_norm_sq_le
    {d : ℕ} {δ εA εB : Type*} [Fintype δ] [Fintype εA] [Fintype εB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, ‖C i‖ ^ 2 ≤ (d : ℝ))
    (F : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    ‖nearBellReferenceProjection C F‖ ^ 2 ≤ (d : ℝ) * ‖F‖ ^ 2 := by
  have hrow (x : δ × εA) (y : δ × εB) :
      Complex.normSq (nearBellReferenceProjection C F x y) ≤
        (d : ℝ) * ∑ q : Fin d × Fin d, Complex.normSq (F (x, y) q) := by
    have h1 : ‖∑ q : Fin d × Fin d, C y.1 q.1 q.2 * F (x, y) q‖ ≤
        ∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ * ‖F (x, y) q‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun q : Fin d × Fin d => ‖C y.1 q.1 q.2‖)
      (fun q : Fin d × Fin d => ‖F (x, y) q‖)
    have hnorm : (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ ^ 2) = ‖C y.1‖ ^ 2 := by
      simp only [frobNorm_sq, Fintype.sum_prod_type]
    calc
      _ = ‖∑ q : Fin d × Fin d, C y.1 q.1 q.2 * F (x, y) q‖ ^ 2 := by
        simp only [nearBellReferenceProjection, Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]
      _ ≤ (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ * ‖F (x, y) q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ ^ 2) *
          ∑ q : Fin d × Fin d, ‖F (x, y) q‖ ^ 2 := h2
      _ ≤ _ := by
        rw [hnorm]
        simp only [Complex.normSq_eq_norm_sq]
        exact mul_le_mul_of_nonneg_right (hC y.1) (Finset.sum_nonneg fun q _ => sq_nonneg _)
  calc
    _ = ∑ x, ∑ y, Complex.normSq (nearBellReferenceProjection C F x y) := by
      simp only [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq, Fintype.sum_prod_type]
    _ ≤ ∑ x, ∑ y, (d : ℝ) * ∑ q : Fin d × Fin d, Complex.normSq (F (x, y) q) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hrow x y
    _ = _ := by
      simp only [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq,
        Fintype.sum_prod_type, Finset.mul_sum]

end NLQCLean
