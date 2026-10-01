import NLQCLean.Models.ClassicalCommunication.FiniteInstruments

/-!
# Tensor products of finite channel operations

The tensor operation is defined on every joint input matrix by its actual
matrix-unit expansion. It is complex-linear in that matrix and bilinear in
the two channel operations. Kraus tensor products agree with tensor products
of their operators, independently of normalization or a target score.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

variable {ι κ τ υ : Type*} [Fintype ι] [Fintype τ]
variable [DecidableEq ι] [DecidableEq τ]

/-- The bilinear tensor product, with input and output factor order fixed. -/
def tensorChannels
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    Matrix (ι × τ) (ι × τ) ℂ →ₗ[ℂ] Matrix (κ × υ) (κ × υ) ℂ where
  toFun Z := ∑ i, ∑ j, ∑ p, ∑ q,
    Z (i, p) (j, q) • (Φ (Matrix.single i j 1) ⊗ₖ Ψ (Matrix.single p q 1))
  map_add' Z W := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
      RingHom.id_apply]

@[simp] theorem tensorChannels_apply
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ)
    (Z : Matrix (ι × τ) (ι × τ) ℂ) :
    tensorChannels Φ Ψ Z = ∑ i, ∑ j, ∑ p, ∑ q,
      Z (i, p) (j, q) • (Φ (Matrix.single i j 1) ⊗ₖ Ψ (Matrix.single p q 1)) := rfl

theorem tensorChannels_add_left
    (Φ Φ' : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels (Φ + Φ') Ψ = tensorChannels Φ Ψ + tensorChannels Φ' Ψ := by
  apply LinearMap.ext
  intro Z
  simp only [tensorChannels_apply, LinearMap.add_apply, Matrix.add_kronecker,
    smul_add, Finset.sum_add_distrib]

theorem tensorChannels_add_right
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ Ψ' : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels Φ (Ψ + Ψ') = tensorChannels Φ Ψ + tensorChannels Φ Ψ' := by
  apply LinearMap.ext
  intro Z
  simp only [tensorChannels_apply, LinearMap.add_apply, Matrix.kronecker_add,
    smul_add, Finset.sum_add_distrib]

theorem tensorChannels_smul_left (c : ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels (c • Φ) Ψ = c • tensorChannels Φ Ψ := by
  apply LinearMap.ext
  intro Z
  simp only [tensorChannels_apply, LinearMap.smul_apply, Matrix.smul_kronecker,
    Finset.smul_sum, smul_smul, mul_comm]

theorem tensorChannels_smul_right (c : ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels Φ (c • Ψ) = c • tensorChannels Φ Ψ := by
  apply LinearMap.ext
  intro Z
  simp only [tensorChannels_apply, LinearMap.smul_apply, Matrix.kronecker_smul,
    Finset.smul_sum, smul_smul, mul_comm]

/-- Complex linearity in the first channel slot with the second slot fixed. -/
def tensorChannelsLeftLinear (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℂ]
      (Matrix (ι × τ) (ι × τ) ℂ →ₗ[ℂ] Matrix (κ × υ) (κ × υ) ℂ) where
  toFun Φ := tensorChannels Φ Ψ
  map_add' Φ Φ' := tensorChannels_add_left Φ Φ' Ψ
  map_smul' c Φ := tensorChannels_smul_left c Φ Ψ

/-- Complex linearity in the second channel slot with the first slot fixed. -/
def tensorChannelsRightLinear (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    (Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) →ₗ[ℂ]
      (Matrix (ι × τ) (ι × τ) ℂ →ₗ[ℂ] Matrix (κ × υ) (κ × υ) ℂ) where
  toFun Ψ := tensorChannels Φ Ψ
  map_add' Ψ Ψ' := tensorChannels_add_right Φ Ψ Ψ'
  map_smul' c Ψ := tensorChannels_smul_right c Φ Ψ

@[simp] theorem tensorChannelsLeftLinear_apply
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    tensorChannelsLeftLinear Ψ Φ = tensorChannels Φ Ψ := rfl

@[simp] theorem tensorChannelsRightLinear_apply
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannelsRightLinear Φ Ψ = tensorChannels Φ Ψ := rfl

/-- The same first-slot operation as a real-linear map on complex channels. -/
noncomputable def tensorChannelsLeftRealLinear (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ]
      (Matrix (ι × τ) (ι × τ) ℂ →ₗ[ℂ] Matrix (κ × υ) (κ × υ) ℂ) :=
  (tensorChannelsLeftLinear Ψ).restrictScalars ℝ

/-- The same second-slot operation as a real-linear map on complex channels. -/
noncomputable def tensorChannelsRightRealLinear (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    (Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) →ₗ[ℝ]
      (Matrix (ι × τ) (ι × τ) ℂ →ₗ[ℂ] Matrix (κ × υ) (κ × υ) ℂ) :=
  (tensorChannelsRightLinear Φ).restrictScalars ℝ

@[simp] theorem tensorChannelsLeftRealLinear_apply
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    tensorChannelsLeftRealLinear Ψ Φ = tensorChannels Φ Ψ := rfl

@[simp] theorem tensorChannelsRightRealLinear_apply
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannelsRightRealLinear Φ Ψ = tensorChannels Φ Ψ := rfl

theorem tensorChannels_sum_left {β : Type*} (t : Finset β)
    (Φ : β → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels (∑ b ∈ t, Φ b) Ψ = ∑ b ∈ t, tensorChannels (Φ b) Ψ :=
  map_sum (tensorChannelsLeftLinear Ψ) Φ t

theorem tensorChannels_sum_right {β : Type*} (t : Finset β)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : β → Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) :
    tensorChannels Φ (∑ b ∈ t, Ψ b) = ∑ b ∈ t, tensorChannels Φ (Ψ b) :=
  map_sum (tensorChannelsRightLinear Φ) Ψ t

/-- The tensor operation evaluates matrix units without ancillary normalization. -/
theorem tensorChannels_single
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ) (i j : ι) (p q : τ) :
    tensorChannels Φ Ψ (Matrix.single (i, p) (j, q) 1) =
      Φ (Matrix.single i j 1) ⊗ₖ Ψ (Matrix.single p q 1) := by
  simp [tensorChannels_apply, Matrix.single_apply, Prod.mk.injEq, ite_and, ite_smul]

/-- Product inputs are mapped to the product of the two actual outputs. -/
theorem tensorChannels_kronecker
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix τ τ ℂ →ₗ[ℂ] Matrix υ υ ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix τ τ ℂ) :
    tensorChannels Φ Ψ (X ⊗ₖ Y) = Φ X ⊗ₖ Ψ Y := by
  ext k l
  simp only [tensorChannels_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply]
  rw [linearMap_matrix_apply Φ X k.1 l.1, linearMap_matrix_apply Ψ Y k.2 l.2]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Tensor products of conjugation operations are the actual joint conjugation. -/
theorem tensorChannels_adConj (A : Matrix κ ι ℂ) (B : Matrix υ τ ℂ) :
    tensorChannels (adConj A) (adConj B) = adConj (A ⊗ₖ B) := by
  have hs (u v : ι × τ) :
      tensorChannels (adConj A) (adConj B) (Matrix.single u v 1) =
        adConj (A ⊗ₖ B) (Matrix.single u v 1) := by
    rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    rw [tensorChannels_single]
    have he : Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single p q (1 : ℂ) =
        Matrix.single (i, p) (j, q) 1 := by
      rw [Matrix.single_kronecker_single, one_mul]
    rw [← he]
    simp only [adConj_apply, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  apply LinearMap.ext
  intro Z
  ext k l
  rw [linearMap_matrix_apply (tensorChannels (adConj A) (adConj B)) Z k l,
    linearMap_matrix_apply (adConj (A ⊗ₖ B)) Z k l]
  simp only [hs]

/-- Two finite Kraus families tensor to their actual product-index Kraus family. -/
theorem tensorChannels_krausMap {ε η : Type*} [Fintype ε] [Fintype η]
    (A : ε → Matrix κ ι ℂ) (B : η → Matrix υ τ ℂ) :
    tensorChannels (krausMap A) (krausMap B) =
      krausMap (fun e : ε × η => A e.1 ⊗ₖ B e.2) := by
  simp only [krausMap, tensorChannels_sum_left, tensorChannels_sum_right,
    tensorChannels_adConj, Fintype.sum_prod_type]
  exact Finset.sum_comm

end NLQCLean.ClassicalCommunication
