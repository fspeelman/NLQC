import NLQCLean.Approx.ChoiProjection
import Mathlib.Data.Matrix.Block

/-!
# Schmidt spectrum of flagged block matrices

The two laboratory outcome flags turn the projected Choi coefficient
matrix into a block diagonal matrix.  This file computes its top-`K` Schmidt
mass from arbitrary diagonal Gram coordinates on the individual blocks, and
then specializes the result to families of Kronecker-product blocks.

No ordering of the weights is chosen here.  The existing variational
characterization of `schmidtMass` therefore covers repeated and zero weights.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- Independent row and column relabelings preserve the top-`K` Schmidt
mass.  This complements `frobInner_submatrix_equiv`, `norm_submatrix_equiv`,
and `Matrix.rank_submatrix` with the variational Schmidt-mass consequence. -/
theorem schmidtMass_submatrix_equiv_le {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m]
    [DecidableEq m'] (A : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) (K : ℕ) :
    schmidtMass K (A.submatrix e f) ≤ schmidtMass K A := by
  by_cases hpos : 0 < schmidtMass K (A.submatrix e f)
  · obtain ⟨W, hW, hrank, hinner⟩ :=
      exists_schmidt_truncation (A.submatrix e f) K hpos
    let W₀ : Matrix m n ℂ := W.submatrix e.symm f.symm
    have hW₀ : ‖W₀‖ = 1 := (norm_submatrix_equiv W e.symm f.symm).trans hW
    have hrank₀ : W₀.rank ≤ K := by
      change (W.submatrix e.symm f.symm).rank ≤ K
      rw [Matrix.rank_submatrix]
      exact hrank
    have hinner₀ : frobInner W₀ A =
        (Real.sqrt (schmidtMass K (A.submatrix e f)) : ℂ) := by
      have h := frobInner_submatrix_equiv W₀ A e f
      calc
        frobInner W₀ A = frobInner (W₀.submatrix e f) (A.submatrix e f) := h.symm
        _ = frobInner W (A.submatrix e f) := by simp [W₀]
        _ = _ := hinner
    have hbound := norm_frobInner_sq_le_schmidtMass A W₀ hW₀ hrank₀
    rwa [hinner₀, norm_complex_sqrt_sq hpos.le] at hbound
  · exact (le_of_not_gt hpos).trans (schmidtMass_nonneg K A)

/-- Independent row and column bijections preserve `schmidtMass` exactly. -/
theorem schmidtMass_submatrix_equiv {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m]
    [DecidableEq m'] (A : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) (K : ℕ) :
    schmidtMass K (A.submatrix e f) = schmidtMass K A := by
  apply le_antisymm (schmidtMass_submatrix_equiv_le A e f K)
  have h := schmidtMass_submatrix_equiv_le (A.submatrix e f) e.symm f.symm K
  simpa using h

/-- A block diagonal family of isometries is an isometry.  Mathlib's
`blockDiagonal` puts the block label in the second coordinate: its row type is
`m × δ` and its column type is `n × δ`. -/
theorem isIsometry_blockDiagonal {δ m n : Type*}
    [Fintype δ] [Fintype m] [Fintype n] [DecidableEq δ] [DecidableEq n]
    (V : δ → Matrix m n ℂ) (hV : ∀ i, IsIsometry (V i)) :
    IsIsometry (Matrix.blockDiagonal V) := by
  rw [IsIsometry, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hblocks : (fun i ↦ (V i)ᴴ * V i) = (1 : δ → Matrix n n ℂ) := by
    funext i
    exact hV i
  rw [hblocks, Matrix.blockDiagonal_one]

/-- Diagonal Gram coordinates on each block combine into diagonal Gram
coordinates on the full flagged block matrix. -/
theorem blockDiagonal_diagonal_gram {δ m n : Type*}
    [Fintype δ] [Fintype m] [Fintype n] [DecidableEq δ] [DecidableEq m]
    (M : δ → Matrix m n ℂ) (V : δ → Matrix m m ℂ) (w : δ → m → ℝ)
    (hgram : ∀ i, ((V i)ᴴ * M i) * ((V i)ᴴ * M i)ᴴ =
      Matrix.diagonal (fun a ↦ (w i a : ℂ))) :
    ((Matrix.blockDiagonal V)ᴴ * Matrix.blockDiagonal M) *
        ((Matrix.blockDiagonal V)ᴴ * Matrix.blockDiagonal M)ᴴ =
      Matrix.diagonal (fun ai : m × δ ↦ (w ai.2 ai.1 : ℂ)) := by
  have hcoordinate :
      (Matrix.blockDiagonal V)ᴴ * Matrix.blockDiagonal M =
        Matrix.blockDiagonal (fun i ↦ (V i)ᴴ * M i) := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  rw [hcoordinate, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  simp only [hgram, Matrix.blockDiagonal_diagonal]

/-- The top-`K` Schmidt mass of a block diagonal matrix is the top-`K` mass
of the union of any nonnegative diagonal Gram coordinates of its blocks.
This statement is insensitive to ties and includes zero blocks and `K = 0`. -/
theorem schmidtMass_blockDiagonal_eq_topWeightMass_of_coordinates
    {δ m n : Type*} [Fintype δ] [Fintype m] [Fintype n]
    [DecidableEq δ] [DecidableEq m]
    (M : δ → Matrix m n ℂ) (V : δ → Matrix m m ℂ) (w : δ → m → ℝ)
    (hV : ∀ i, IsIsometry (V i)) (hV' : ∀ i, IsIsometry (V i)ᴴ)
    (hw : ∀ i a, 0 ≤ w i a)
    (hgram : ∀ i, ((V i)ᴴ * M i) * ((V i)ᴴ * M i)ᴴ =
      Matrix.diagonal (fun a ↦ (w i a : ℂ))) (K : ℕ) :
    schmidtMass K (Matrix.blockDiagonal M) =
      topWeightMass K (fun ai : m × δ ↦ w ai.2 ai.1) := by
  apply schmidtMass_eq_topWeightMass_of_coordinates
    (Matrix.blockDiagonal M) (Matrix.blockDiagonal V)
      (fun ai : m × δ ↦ w ai.2 ai.1)
  · exact isIsometry_blockDiagonal V hV
  · rw [Matrix.blockDiagonal_conjTranspose]
    exact isIsometry_blockDiagonal (fun i ↦ (V i)ᴴ) hV'
  · exact fun ai ↦ hw ai.2 ai.1
  · exact blockDiagonal_diagonal_gram M V w hgram

/-- Scaling a matrix by an arbitrary complex number multiplies every squared
Gram weight by the squared norm of that number. -/
theorem diagonal_gram_smul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (w : m → ℝ) (z : ℂ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun a ↦ (w a : ℂ))) :
    (z • M) * (z • M)ᴴ =
      Matrix.diagonal (fun a ↦ ((‖z‖ ^ 2 * w a : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgram]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, if_pos, Complex.star_def,
      Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow, smul_eq_mul]
  · simp [hab]

/-- Supplied Schmidt coordinates for two arbitrary rectangular factors give
product coordinates for a scaled Kronecker block. -/
theorem scaledKronecker_diagonal_gram
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ)
    (V : Matrix m m ℂ) (U : Matrix p p ℂ)
    (wA : m → ℝ) (wB : p → ℝ) (z : ℂ)
    (hgramA : (Vᴴ * A) * (Vᴴ * A)ᴴ =
      Matrix.diagonal (fun a ↦ (wA a : ℂ)))
    (hgramB : (Uᴴ * B) * (Uᴴ * B)ᴴ =
      Matrix.diagonal (fun c ↦ (wB c : ℂ))) :
    (((V ⊗ₖ U)ᴴ * (z • (A ⊗ₖ B))) *
        ((V ⊗ₖ U)ᴴ * (z • (A ⊗ₖ B)))ᴴ) =
      Matrix.diagonal (fun ac : m × p ↦
        ((‖z‖ ^ 2 * (wA ac.1 * wB ac.2) : ℝ) : ℂ)) := by
  have hbase : ((V ⊗ₖ U)ᴴ * (A ⊗ₖ B)) * ((V ⊗ₖ U)ᴴ * (A ⊗ₖ B))ᴴ =
      Matrix.diagonal (fun ac : m × p ↦ ((wA ac.1 * wB ac.2 : ℝ) : ℂ)) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hgramA, hgramB, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]
  simpa only [Matrix.mul_smul] using
    (diagonal_gram_smul ((V ⊗ₖ U)ᴴ * (A ⊗ₖ B))
      (fun ac : m × p ↦ wA ac.1 * wB ac.2) z hbase)

/-- The exact flagged spectrum for an arbitrary finite family of scaled
Kronecker products.  The row coordinate `((a,c),i)` has weight
`‖z i‖² * schmidtWeights (A i) a * schmidtWeights (B i) c`.

For normalized flagged Choi blocks, take `z i = D⁻¹ᐟ²`; for outcome-dependent
normalizations or amplitudes, `z` may vary freely with the label. -/
theorem schmidtMass_blockDiagonal_scaledKronecker_eq
    {δ m n p q : Type*} [Fintype δ] [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq δ] [DecidableEq m] [DecidableEq p]
    (A : δ → Matrix m n ℂ) (B : δ → Matrix p q ℂ) (z : δ → ℂ) (K : ℕ) :
    schmidtMass K
        (Matrix.blockDiagonal (fun i ↦ z i • (A i ⊗ₖ B i))) =
      topWeightMass K (fun aci : (m × p) × δ ↦
        ‖z aci.2‖ ^ 2 *
          (schmidtWeights (A aci.2) aci.1.1 *
            schmidtWeights (B aci.2) aci.1.2)) := by
  classical
  choose V hV hV' hgramA using fun i ↦ exists_schmidt_coordinates (A i)
  choose U hU hU' hgramB using fun i ↦ exists_schmidt_coordinates (B i)
  apply schmidtMass_blockDiagonal_eq_topWeightMass_of_coordinates
    (fun i ↦ z i • (A i ⊗ₖ B i)) (fun i ↦ V i ⊗ₖ U i)
    (fun i ac ↦ ‖z i‖ ^ 2 *
      (schmidtWeights (A i) ac.1 * schmidtWeights (B i) ac.2))
  · exact fun i ↦ (hV i).kronecker (hU i)
  · intro i
    rw [Matrix.conjTranspose_kronecker]
    exact (hV' i).kronecker (hU' i)
  · exact fun i ac ↦ mul_nonneg (sq_nonneg _)
      (mul_nonneg (schmidtWeights_nonneg (A i) ac.1)
        (schmidtWeights_nonneg (B i) ac.2))
  · exact fun i ↦ scaledKronecker_diagonal_gram
      (A i) (B i) (V i) (U i)
      (schmidtWeights (A i)) (schmidtWeights (B i)) (z i)
      (hgramA i) (hgramB i)

/-- Unscaled convenience form of
`schmidtMass_blockDiagonal_scaledKronecker_eq`. -/
theorem schmidtMass_blockDiagonal_kronecker_eq
    {δ m n p q : Type*} [Fintype δ] [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq δ] [DecidableEq m] [DecidableEq p]
    (A : δ → Matrix m n ℂ) (B : δ → Matrix p q ℂ) (K : ℕ) :
    schmidtMass K (Matrix.blockDiagonal (fun i ↦ A i ⊗ₖ B i)) =
      topWeightMass K (fun aci : (m × p) × δ ↦
        schmidtWeights (A aci.2) aci.1.1 *
          schmidtWeights (B aci.2) aci.1.2) := by
  simpa using schmidtMass_blockDiagonal_scaledKronecker_eq A B (fun _ ↦ (1 : ℂ)) K

end NLQCLean
