import NLQCLean.LinearAlgebra.RealCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Explicit real Euclidean entry coordinates

Split each complex entry into its real and imaginary coordinates.
The Euclidean norms agree exactly. Restricting along a coordinate embedding
contracts the l2 norm; zero extension will give the common padded space.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Entrywise real and imaginary parts, as a real-linear equivalence. -/
def complexRealCoordEquiv (ι : Type*) : (ι → ℂ) ≃ₗ[ℝ] ((ι × Fin 2) → ℝ) where
  toFun z p := ![(z p.1).re, (z p.1).im] p.2
  invFun z i := ⟨z (i, 0), z (i, 1)⟩
  left_inv z := by funext i; rfl
  right_inv z := by funext ⟨i, j⟩; fin_cases j <;> rfl
  map_add' z w := by funext ⟨i, j⟩; fin_cases j <;> rfl
  map_smul' c z := by funext ⟨i, j⟩; fin_cases j <;> simp

theorem norm_complexRealCoordEquiv {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖WithLp.toLp 2 (complexRealCoordEquiv ι z)‖ = ‖WithLp.toLp 2 z‖ := by
  have hs : ‖WithLp.toLp 2 (complexRealCoordEquiv ι z)‖ ^ 2 = ‖WithLp.toLp 2 z‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      complexRealCoordEquiv, Complex.sq_norm, Complex.normSq_apply, ← pow_two]
  nlinarith [norm_nonneg (WithLp.toLp 2 (complexRealCoordEquiv ι z)), norm_nonneg (WithLp.toLp 2 z)]

/-- Flatten matrix entries; no norm on a Pi type is substituted for Frobenius. -/
def matrixEntryEquiv (m n : Type*) : Matrix m n ℂ ≃ₗ[ℝ] ((m × n) → ℂ) where
  toFun M p := M p.1 p.2
  invFun z := Matrix.of fun i j => z (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_matrixEntryEquiv {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ‖WithLp.toLp 2 (matrixEntryEquiv m n M)‖ = ‖M‖ := by
  classical
  have hs : ‖WithLp.toLp 2 (matrixEntryEquiv m n M)‖ ^ 2 = ‖M‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, frobNorm_sq, Fintype.sum_prod_type]
    rfl
  nlinarith [norm_nonneg (WithLp.toLp 2 (matrixEntryEquiv m n M)), norm_nonneg M]

/-- A matrix in real Euclidean coordinates. -/
noncomputable def matrixEuclideanCoordEquiv (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ ≃ₗ[ℝ] EuclideanSpace ℝ ((m × n) × Fin 2) :=
  (matrixEntryEquiv m n).trans ((complexRealCoordEquiv (m × n)).trans
    (WithLp.linearEquiv 2 ℝ (((m × n) × Fin 2) → ℝ)).symm)

theorem norm_matrixEuclideanCoordEquiv {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ‖matrixEuclideanCoordEquiv m n M‖ = ‖M‖ := by
  exact (norm_complexRealCoordEquiv (matrixEntryEquiv m n M)).trans (norm_matrixEntryEquiv M)

/-- A coordinate restriction is real-linear on Euclidean spaces. -/
noncomputable def euclideanRestrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) : EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => x (e i))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem norm_euclideanRestrict_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ κ) : ‖euclideanRestrict e x‖ ≤ ‖x‖ := by
  classical
  have hs : ‖euclideanRestrict e x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change ∑ i : ι, ‖x (e i)‖ ^ 2 ≤ ∑ j : κ, ‖x j‖ ^ 2
    calc
      _ = ∑ j ∈ Finset.univ.map e, ‖x j‖ ^ 2 := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (euclideanRestrict e x), norm_nonneg x]

/-- Zero extension along a fixed coordinate embedding. -/
noncomputable def euclideanExtend {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 (Function.extend e (WithLp.ofLp x) (fun _ => 0))
  map_add' x y := by
    classical
    ext j
    change Function.extend e (fun i => x i + y i) (fun _ => 0) j =
      Function.extend e (WithLp.ofLp x) (fun _ => 0) j +
        Function.extend e (WithLp.ofLp y) (fun _ => 0) j
    simp only [Function.extend_def]
    split <;> simp
  map_smul' c x := by
    classical
    ext j
    change Function.extend e (fun i => c * x i) (fun _ => 0) j =
      c * Function.extend e (WithLp.ofLp x) (fun _ => 0) j
    simp only [Function.extend_def]
    split <;> simp

theorem euclideanExtend_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) (i : ι) : (euclideanExtend e x) (e i) = x i :=
  e.injective.extend_apply (WithLp.ofLp x) (fun _ => 0) i

theorem euclideanExtend_apply_of_not_mem {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) {j : κ} (hj : j ∉ Set.range e) :
    (euclideanExtend e x) j = 0 :=
  Function.extend_apply' (WithLp.ofLp x) (fun _ => 0) j hj

theorem euclideanRestrict_extend {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) : euclideanRestrict e (euclideanExtend e x) = x := by
  ext i
  exact euclideanExtend_apply e x i

theorem norm_euclideanExtend {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) : ‖euclideanExtend e x‖ = ‖x‖ := by
  classical
  have hs : ‖euclideanExtend e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ j ∈ Finset.univ.map e, ‖(euclideanExtend e x) j‖ ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hnot : j ∉ Set.range e := by
          rintro ⟨i, hi⟩
          exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)
        rw [euclideanExtend_apply_of_not_mem e x hnot, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ = _ := by simp only [Finset.sum_map, euclideanExtend_apply]
  nlinarith [norm_nonneg (euclideanExtend e x), norm_nonneg x]

end NLQCLean
