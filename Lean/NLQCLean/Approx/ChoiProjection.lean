import NLQCLean.Approx.ChoiRank
import NLQCLean.LinearAlgebra.SchmidtOverlap
import NLQCLean.Models.UnitaryScore

/-!
# Normalized Choi projection and sharp freezing

The Choi coefficients below keep
each reference in its original laboratory, then group that laboratory's
logical output and reference before its discarded environment. This makes
the frozen Choi vector literally a Kronecker product.
-/

namespace NLQCLean

open Matrix WithLp
open scoped Matrix.Norms.Frobenius Kronecker

/-- Independent bijections of the row and column labels preserve the
Frobenius inner product. -/
theorem frobInner_submatrix_equiv {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (A B : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) :
    frobInner (A.submatrix e f) (B.submatrix e f) = frobInner A B := by
  simp only [frobInner, Matrix.submatrix_apply]
  calc
    _ = ∑ k, ∑ l, star (A (e k) l) * B (e k) l :=
      Finset.sum_congr rfl (fun k _ => f.sum_comp (fun l => star (A (e k) l) * B (e k) l))
    _ = _ := e.sum_comp (fun k => ∑ l, star (A k l) * B k l)

theorem norm_submatrix_equiv {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (A : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) : ‖A.submatrix e f‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← frobNormSq_eq_norm_sq, ← frobNormSq_eq_norm_sq]
  simp only [frobNormSq, frobInner_submatrix_equiv]

/-- Regrouping the input references preserves the full Frobenius inner product. -/
theorem frobInner_labChoiMatrix {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (F G : Matrix (a × b) (i × j) ℂ) :
    frobInner (labChoiMatrix F) (labChoiMatrix G) = frobInner F G := by
  simp only [frobInner, labChoiMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

theorem norm_normalizedLabChoiMatrix {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (F : Matrix (a × b) (i × j) ℂ) :
    ‖normalizedLabChoiMatrix F‖ = ‖F‖ / Real.sqrt (Fintype.card (i × j) : ℝ) := by
  rw [normalizedLabChoiMatrix, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_labChoiMatrix]
  ring

/-- An isometry's normalized Choi coefficients have norm one. -/
theorem norm_normalizedLabChoiMatrix_of_isometry {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Nonempty i] [Nonempty j]
    [DecidableEq i] [DecidableEq j]
    {F : Matrix (a × b) (i × j) ℂ} (hF : IsIsometry F) :
    ‖normalizedLabChoiMatrix F‖ = 1 := by
  classical
  have hs : 0 < Real.sqrt (Fintype.card (i × j) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hnorm : ‖F‖ = Real.sqrt (Fintype.card (i × j) : ℝ) := by
    rw [← hF.sum_row_norm_sq, ← frobNorm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_normalizedLabChoiMatrix, hnorm, div_self hs.ne']

/-- Move only the local reference and environment ordering, never the
laboratory cut: `((output,reference),environment)` to `((output,environment),reference)`. -/
def choiLocalRegroup (a i e : Type*) : (a × i) × e ≃ (a × e) × i where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The normalized purified Choi matrix in the tensor-product-compatible
local ordering. All reference/environment relabelings are local bijections. -/
noncomputable def tensorChoiMatrix {a b i j e f : Type*} [Fintype i] [Fintype j]
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    Matrix ((a × i) × e) ((b × j) × f) ℂ :=
  (normalizedLabChoiMatrix F).submatrix (choiLocalRegroup a i e) (choiLocalRegroup b j f)

theorem norm_tensorChoiMatrix {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    ‖tensorChoiMatrix F‖ = ‖F‖ / Real.sqrt (Fintype.card (i × j) : ℝ) := by
  rw [tensorChoiMatrix, norm_submatrix_equiv, norm_normalizedLabChoiMatrix]

theorem norm_tensorChoiMatrix_of_isometry {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    [Nonempty i] [Nonempty j]
    [DecidableEq i] [DecidableEq j]
    {F : Matrix ((a × e) × (b × f)) (i × j) ℂ} (hF : IsIsometry F) :
    ‖tensorChoiMatrix F‖ = 1 := by
  rw [tensorChoiMatrix, norm_submatrix_equiv]
  exact norm_normalizedLabChoiMatrix_of_isometry hF

theorem rank_tensorChoiMatrix {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    (tensorChoiMatrix F).rank = (normalizedLabChoiMatrix F).rank :=
  Matrix.rank_submatrix _ _ _

theorem tensorChoiMatrix_sub {a b i j e f : Type*} [Fintype i] [Fintype j]
    (F G : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    tensorChoiMatrix (F - G) = tensorChoiMatrix F - tensorChoiMatrix G := by
  ext x y
  simp [tensorChoiMatrix, normalizedLabChoiMatrix, labChoiMatrix, mul_sub]

theorem norm_sq_resourceMatrix {e f : Type*} [Fintype e] [Fintype f] (g : e × f → ℂ) :
    ‖resourceMatrix g‖ ^ 2 = ∑ x, Complex.normSq (g x) := by
  classical
  simp [frobNorm_sq, resourceMatrix, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

theorem isUnitVector_iff_norm_resourceMatrix {e f : Type*} [Fintype e] [Fintype f]
    (g : e × f → ℂ) : IsUnitVector g ↔ ‖resourceMatrix g‖ = 1 := by
  rw [IsUnitVector, ← norm_sq_resourceMatrix]
  simpa only [one_pow] using sq_eq_sq₀ (norm_nonneg (resourceMatrix g)) zero_le_one

/-- A frozen normalized Choi vector is the tensor product of its normalized
logical Choi coefficients and its environment coefficients. -/
theorem tensorChoiMatrix_frozen {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq a] [DecidableEq b]
    (U : Matrix (a × b) (i × j) ℂ) (g : e × f → ℂ) :
    tensorChoiMatrix (insertResource a b g * U) =
      normalizedLabChoiMatrix U ⊗ₖ resourceMatrix g := by
  ext x y
  simp [tensorChoiMatrix, normalizedLabChoiMatrix, labChoiMatrix, choiLocalRegroup,
    Matrix.mul_apply, insertResource_apply, Fintype.sum_prod_type, resourceMatrix,
    mul_assoc, mul_comm, mul_left_comm]

/-- Normalization divides a Choi inner product by the input dimension. -/
theorem frobInner_tensorChoiMatrix {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    (F G : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    frobInner (tensorChoiMatrix F) (tensorChoiMatrix G) =
      (Fintype.card (i × j) : ℂ)⁻¹ * frobInner F G := by
  rw [tensorChoiMatrix, tensorChoiMatrix, frobInner_submatrix_equiv,
    normalizedLabChoiMatrix, normalizedLabChoiMatrix,
    frobInner_smul_left, frobInner_smul_right, frobInner_labChoiMatrix]
  have hs : (Real.sqrt (Fintype.card (i × j) : ℝ) : ℂ) ^ 2 =
      (Fintype.card (i × j) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (i × j)))
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← mul_inv, ← sq, hs]

/-- The coefficient matrix of the score projection onto the target Choi
vector. The two environment registers remain separate. -/
noncomputable def choiEnvironment {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (U : Matrix (a × b) (i × j) ℂ)
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) : Matrix e f ℂ :=
  resourceMatrix (scoreVector U (F.submatrix (outputRegroup a b e f) id))

theorem norm_sq_choiEnvironment {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq i] [DecidableEq j]
    [DecidableEq e] [DecidableEq f]
    (U : Matrix (a × b) (i × j) ℂ)
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) :
    ‖choiEnvironment U F‖ ^ 2 =
      scoreU U (channelOf (F.submatrix (outputRegroup a b e f) id)) := by
  rw [choiEnvironment, norm_sq_resourceMatrix, scoreU_eq_sum_normSq_scoreVector]

/-- The projection identity, including its complex phase. -/
theorem frobInner_tensorChoiMatrix_frozen {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b]
    (U : Matrix (a × b) (i × j) ℂ)
    (F : Matrix ((a × e) × (b × f)) (i × j) ℂ) (g : e × f → ℂ) :
    frobInner (tensorChoiMatrix (insertResource a b g * U)) (tensorChoiMatrix F) =
      frobInner (resourceMatrix g) (choiEnvironment U F) := by
  classical
  rw [frobInner_tensorChoiMatrix]
  have hreg : (insertResource a b g * U).submatrix (outputRegroup a b e f) id =
      insertVector (a × b) g * U := by
    rw [insertVector_eq_insertResource_submatrix,
      Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_id_id]
  have hinner := frobInner_submatrix_equiv (insertResource a b g * U) F
    (outputRegroup a b e f) (Equiv.refl (i × j))
  change frobInner ((insertResource a b g * U).submatrix (outputRegroup a b e f) id)
      (F.submatrix (outputRegroup a b e f) id) = _ at hinner
  rw [← hinner, hreg, ← sum_frobInner_sliceAt]
  have hslice : ∀ x, sliceAt (insertVector (a × b) g * U) x = g x • U := by
    intro x
    ext k l
    exact insertVector_mul_apply g U (k, x) l
  simp_rw [hslice, frobInner_smul_left]
  change _ = ∑ x, ∑ y, star (g (x, y)) *
    ((Fintype.card (i × j) : ℂ)⁻¹ *
      frobInner U (sliceAt (F.submatrix (outputRegroup a b e f) id) (x, y)))
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end NLQCLean
