import NLQCLean.LinearAlgebra.TraceDistance

/-!
# Finite channel amplification and an ancilla-uniform trace-norm bound

Amplification acts by the channel on the first tensor factor
and the identity on the second. Its finite coefficient expansion gives a
bound independent of the ancillary dimension, for every linear map.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker Matrix.Norms.Frobenius

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α] [DecidableEq β]

/-- The entrywise tensor amplification `Phi tensor id_alpha`. -/
noncomputable def amplify (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (α : Type*)
    [Fintype α] [DecidableEq α] :
    Matrix (ι × α) (ι × α) ℂ →ₗ[ℂ] Matrix (κ × α) (κ × α) ℂ where
  toFun X := fun p q => ∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * X (i, p.2) (j, q.2)
  map_add' X Y := by
    ext p q
    change (∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 *
      (X (i, p.2) (j, q.2) + Y (i, p.2) (j, q.2))) =
      (∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * X (i, p.2) (j, q.2)) +
      (∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * Y (i, p.2) (j, q.2))
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext p q
    change (∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * (c * X (i, p.2) (j, q.2))) =
      c * (∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * X (i, p.2) (j, q.2))
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem amplify_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) (p q : κ × α) :
    amplify Φ α X p q = ∑ i, ∑ j, Φ (Matrix.single i j 1) p.1 q.1 * X (i, p.2) (j, q.2) := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- Every linear map is given by its matrix-unit coefficients. -/
theorem linearMap_matrix_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix ι ι ℂ) (k l : κ) :
    Φ X k l = ∑ i, ∑ j, Φ (Matrix.single i j 1) k l * X i j := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    ext k l
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply]
    simp [smul_eq_mul, ite_and, mul_ite]
  conv_lhs => rw [hX, map_sum]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_comm]

omit [Fintype κ] [DecidableEq κ] in
/-- Equivalently, apply Phi to each fixed ancilla block. -/
theorem amplify_apply_block (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) (p q : κ × α) :
    amplify Φ α X p q = Φ (fun i j => X (i, p.2) (j, q.2)) p.1 q.1 := by
  exact (linearMap_matrix_apply Φ (Matrix.of fun i j => X (i, p.2) (j, q.2)) p.1 q.1).symm

omit [Fintype κ] [DecidableEq κ] in
/-- The defining tensor-product identity, for arbitrary inputs on both factors. -/
theorem amplify_kronecker (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix α α ℂ) :
    amplify Φ α (X ⊗ₖ Y) = Φ X ⊗ₖ Y := by
  ext p q
  rw [amplify_apply_block]
  have h : (fun i j => (X ⊗ₖ Y) (i, p.2) (j, q.2)) = Y p.2 q.2 • X := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_comm]
  rw [h, map_smul]
  simp [Matrix.kroneckerMap_apply, mul_comm]

omit [Fintype κ] [DecidableEq κ] in
/-- Ancilla basis relabeling commutes exactly with amplification. -/
theorem amplify_submatrix_ancilla (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (e : β ≃ α) (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify Φ β (X.submatrix ((Equiv.refl ι).prodCongr e) ((Equiv.refl ι).prodCongr e)) =
      (amplify Φ α X).submatrix ((Equiv.refl κ).prodCongr e) ((Equiv.refl κ).prodCongr e) := by
  ext p q
  rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem amplify_add (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (Φ + Ψ) α X = amplify Φ α X + amplify Ψ α X := by
  ext p q
  simp only [amplify_apply, LinearMap.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem amplify_smul (c : ℂ) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (c • Φ) α X = c • amplify Φ α X := by
  ext p q
  simp [amplify_apply, Finset.mul_sum, mul_assoc]

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem amplify_zero (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) α X = 0 := by
  ext p q
  simp [amplify_apply]

/-- A matrix unit on the main register, amplified by an identity. -/
def amplificationLeg (k : κ) (i : ι) (α : Type*) [DecidableEq α] :
    Matrix (κ × α) (ι × α) ℂ := Matrix.single k i 1 ⊗ₖ (1 : Matrix α α ℂ)

theorem opNorm_amplificationLeg_le (k : κ) (i : ι) :
    opNorm (amplificationLeg k i α) ≤ 1 :=
  (opNorm_kronecker_one_le _).trans (opNorm_single_one_le k i)

omit [Fintype κ] in
theorem amplificationLeg_sandwich_apply (k l : κ) (i j : ι)
    (X : Matrix (ι × α) (ι × α) ℂ) (p q : κ × α) :
    (amplificationLeg k i α * X * (amplificationLeg l j α)ᴴ) p q =
      if k = p.1 ∧ l = q.1 then X (i, p.2) (j, q.2) else 0 := by
  by_cases hk : k = p.1 <;> by_cases hl : l = q.1 <;>
    simp [amplificationLeg, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, apply_ite, ite_mul, hk, hl]

/-- A finite sum of elementary sandwiches, with no ancillary dimension in the coefficients. -/
theorem amplify_eq_sum_sandwich (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify Φ α X = ∑ k, ∑ l, ∑ i, ∑ j, Φ (Matrix.single i j 1) k l •
      (amplificationLeg k i α * X * (amplificationLeg l j α)ᴴ) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, amplificationLeg_sandwich_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, ite_and]
  simp

/-- A finite coefficient bound depending only on the original linear map. -/
noncomputable def channelCoefficientBound (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : ℝ :=
  ∑ k, ∑ l, ∑ i, ∑ j, ‖Φ (Matrix.single i j 1) k l‖

omit [DecidableEq κ] in
theorem channelCoefficientBound_nonneg (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    0 ≤ channelCoefficientBound Φ := by
  unfold channelCoefficientBound
  positivity

/-- Amplification is bounded uniformly in every finite ancillary dimension. -/
theorem traceNorm_amplify_le (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    traceNorm (amplify Φ α X) ≤ channelCoefficientBound Φ * traceNorm X := by
  rw [amplify_eq_sum_sandwich]
  unfold channelCoefficientBound
  simp only [Finset.sum_mul]
  apply (traceNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (traceNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  apply (traceNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (traceNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [traceNorm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have h := traceNorm_mul_mul_le (amplificationLeg k i α) X (amplificationLeg l j α)ᴴ
  rw [opNorm_conjTranspose] at h
  apply h.trans
  calc
    _ ≤ 1 * traceNorm X * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (opNorm_amplificationLeg_le k i) (traceNorm_nonneg X))
        (opNorm_amplificationLeg_le l j) (opNorm_nonneg _)
        (by simpa using traceNorm_nonneg X)
    _ = _ := by ring

end NLQCLean
