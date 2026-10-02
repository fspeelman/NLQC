import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Determinant bounds in an adapted orthonormal basis

This module supplies the unconditional Jacobian linear algebra. Gram--Schmidt gives
the product-of-column-norms bound without a singular-value perturbation API.
-/

namespace NLQCLean

open Module InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Hadamard's bound for the volume factor of an arbitrary rectangular map. -/
theorem normDet_le_prod_norm_fin {n : ℕ}
    (L : E →ₗ[ℝ] F) (b : OrthonormalBasis (Fin n) ℝ E) :
    L.normDet ≤ ∏ i, ‖L (b i)‖ := by
  by_cases h : L.normDet = 0
  · rw [h]
    exact Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hr : finrank ℝ L.range = Fintype.card (Fin n) :=
    (not_not.mp (L.normDet_eq_zero_iff_rank_range_ne.not.mp h)).trans
      (finrank_eq_card_basis b.toBasis)
  let v : Fin n → L.range := fun i => L.rangeRestrict (b i)
  let c := gramSchmidtOrthonormalBasis hr v
  rw [L.normDet_eq_norm_det_toMatrix_rangeRestrict b c]
  have hm : L.rangeRestrict.toMatrix b.toBasis c.toBasis = c.toBasis.toMatrix v := by
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, v]
  rw [hm]
  rw [← Basis.det_apply, gramSchmidtOrthonormalBasis_det, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  calc
    ‖inner ℝ (c i) (v i)‖ ≤ ‖c i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖L (b i)‖ := by rw [c.orthonormal.1 i, one_mul]; rfl

/-- The basis index need not carry an order. -/
theorem normDet_le_prod_norm {ι : Type*} [Fintype ι]
    (L : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    L.normDet ≤ ∏ i, ‖L (b i)‖ := by
  classical
  let e := Fintype.equivFin ι
  calc
    L.normDet ≤ ∏ i : Fin (Fintype.card ι), ‖L (b (e.symm i))‖ := by
      simpa only [OrthonormalBasis.coe_reindex, Function.comp_apply] using
        normDet_le_prod_norm_fin L (b.reindex e)
    _ = ∏ i, ‖L (b i)‖ := e.symm.prod_comp (fun i => ‖L (b i)‖)

/-- Split the determinant factors between a subspace and its orthogonal complement. -/
theorem normDet_le_of_subspace_bounds (L : E →ₗ[ℝ] F) (V : Submodule ℝ E)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hVA : ∀ x ∈ V, ‖L x‖ ≤ A * ‖x‖)
    (hVB : ∀ x ∈ Vᗮ, ‖L x‖ ≤ B * ‖x‖) :
    L.normDet ≤ A ^ finrank ℝ V * B ^ (finrank ℝ E - finrank ℝ V) := by
  classical
  let b₀ := stdOrthonormalBasis ℝ V
  let b₁ := stdOrthonormalBasis ℝ Vᗮ
  let b := (b₀.prod b₁).map V.orthogonalDecomposition.symm
  have hb₀ (i : Fin (finrank ℝ V)) : b (Sum.inl i) = (b₀ i : E) := by
    simp [b, OrthonormalBasis.prod_apply, Submodule.orthogonalDecomposition_symm_apply]
  have hb₁ (i : Fin (finrank ℝ Vᗮ)) : b (Sum.inr i) = (b₁ i : E) := by
    simp [b, OrthonormalBasis.prod_apply, Submodule.orthogonalDecomposition_symm_apply]
  calc
    L.normDet ≤ ∏ i, ‖L (b i)‖ := normDet_le_prod_norm L b
    _ = (∏ i, ‖L (b₀ i : E)‖) * ∏ i, ‖L (b₁ i : E)‖ := by
      rw [Fintype.prod_sum_type]; simp only [hb₀, hb₁]
    _ ≤ (∏ _ : Fin (finrank ℝ V), A) * ∏ _ : Fin (finrank ℝ Vᗮ), B := by
      apply mul_le_mul
      · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        simpa only [Submodule.norm_coe, b₀.orthonormal.1 i, mul_one] using
          hVA (b₀ i) (b₀ i).property
      · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        simpa only [Submodule.norm_coe, b₁.orthonormal.1 i, mul_one] using
          hVB (b₁ i) (b₁ i).property
      · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
      · exact Finset.prod_nonneg fun _ _ => hA
    _ = A ^ finrank ℝ V * B ^ (finrank ℝ E - finrank ℝ V) := by
      have hd := V.finrank_add_finrank_orthogonal
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      omega

/-- Increasing the number of factors charged at the larger bound preserves an upper bound. -/
theorem rank_power_bound_mono {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A)
    {k t m : ℕ} (hkt : k ≤ t) (htm : t ≤ m) :
    A ^ k * B ^ (m - k) ≤ A ^ t * B ^ (m - t) := by
  have hA := hB.trans hBA
  have h₁ : m - k = (t - k) + (m - t) := by omega
  calc
    A ^ k * B ^ (m - k) = (A ^ k * B ^ (t - k)) * B ^ (m - t) := by
      rw [h₁, pow_add, mul_assoc]
    _ ≤ (A ^ k * A ^ (t - k)) * B ^ (m - t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBA _) (pow_nonneg hA _))
        (pow_nonneg hB _)
    _ = A ^ t * B ^ (m - t) := by rw [← pow_add, Nat.add_sub_of_le hkt]

/-- The adapted determinant bound with an upper bound on the exceptional dimension. -/
theorem normDet_le_of_subspace_rank_bound (L : E →ₗ[ℝ] F) (V : Submodule ℝ E)
    {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) {t : ℕ}
    (hVt : finrank ℝ V ≤ t) (ht : t ≤ finrank ℝ E)
    (hVA : ∀ x ∈ V, ‖L x‖ ≤ A * ‖x‖)
    (hVB : ∀ x ∈ Vᗮ, ‖L x‖ ≤ B * ‖x‖) :
    L.normDet ≤ A ^ t * B ^ (finrank ℝ E - t) :=
  (normDet_le_of_subspace_bounds L V (hB.trans hBA) hB hVA hVB).trans
    (rank_power_bound_mono hB hBA hVt ht)

end NLQCLean
