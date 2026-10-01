import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Frobenius inner products for finite complex matrices

The explicit Hilbert--Schmidt inner product, its relation to the matrix
Frobenius norm and the general isometry facts used by spectral arguments.
-/

namespace NLQCLean

open Matrix WithLp
open scoped Matrix.Norms.Frobenius ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

/-- The Frobenius (Hilbert–Schmidt) inner product `⟨A,B⟩ = Tr(A†B)`,
conjugate-linear in the first argument. -/
def frobInner (A B : Matrix κ ι ℂ) : ℂ := ∑ k, ∑ i, star (A k i) * B k i

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_eq_trace (A B : Matrix κ ι ℂ) :
    frobInner A B = (Aᴴ * B).trace := by
  simp [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_comm (γ := ι)]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The Frobenius inner product as a single sum over the product index. -/
theorem frobInner_eq_sum_prod (A B : Matrix κ ι ℂ) :
    frobInner A B = ∑ p : κ × ι, star (A p.1 p.2) * B p.1 p.2 :=
  (Fintype.sum_prod_type (f := fun p : κ × ι => star (A p.1 p.2) * B p.1 p.2)).symm

omit [DecidableEq κ] in
/-- For an isometry, `⟨F,F⟩ = D`, the domain dimension: the normalization
`‖U‖_F² = D` used silently throughout §5 of the paper. -/
theorem frobInner_self_of_isometry {F : Matrix κ ι ℂ} (h : IsIsometry F) :
    frobInner F F = (Fintype.card ι : ℂ) := by
  rw [frobInner_eq_trace, h.conjTranspose_mul_self, Matrix.trace_one]

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_conj (A B : Matrix κ ι ℂ) : star (frobInner A B) = frobInner B A := by
  simp only [frobInner, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_smul_right (c : ℂ) (A B : Matrix κ ι ℂ) :
    frobInner A (c • B) = c * frobInner A B := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_smul_left (c : ℂ) (A B : Matrix κ ι ℂ) :
    frobInner (c • A) B = star c * frobInner A B := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_sub_right (A B C : Matrix κ ι ℂ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp only [frobInner, Matrix.sub_apply, mul_sub, ← Finset.sum_sub_distrib]

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_sub_left (A B C : Matrix κ ι ℂ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp only [frobInner, Matrix.sub_apply, star_sub, sub_mul, ← Finset.sum_sub_distrib]

/-- The squared Frobenius norm, as the real part of the self inner product.
Working with `frobInner` throughout avoids any interaction with the scoped
Frobenius norm instance. -/
def frobNormSq (A : Matrix κ ι ℂ) : ℝ := (frobInner A A).re

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobInner_self_eq_sum_normSq (A : Matrix κ ι ℂ) :
    frobInner A A = ((∑ p : κ × ι, Complex.normSq (A p.1 p.2) : ℝ) : ℂ) := by
  rw [frobInner_eq_sum_prod]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by
    rw [Complex.normSq_eq_conj_mul_self]
    rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobNormSq_eq_sum_normSq (A : Matrix κ ι ℂ) :
    frobNormSq A = ∑ p : κ × ι, Complex.normSq (A p.1 p.2) := by
  rw [frobNormSq, frobInner_self_eq_sum_normSq, Complex.ofReal_re]

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobNormSq_nonneg (A : Matrix κ ι ℂ) : 0 ≤ frobNormSq A := by
  rw [frobNormSq_eq_sum_normSq]
  exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _

omit [DecidableEq ι] [DecidableEq κ] in
theorem frobNormSq_eq_zero_iff (A : Matrix κ ι ℂ) : frobNormSq A = 0 ↔ A = 0 := by
  rw [frobNormSq_eq_sum_normSq]
  constructor
  · intro h
    have hz : ∀ p : κ × ι, Complex.normSq (A p.1 p.2) = 0 := by
      intro p
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => Complex.normSq_nonneg _)).mp h p (Finset.mem_univ p)
    ext k i
    exact Complex.normSq_eq_zero.mp (hz (k, i))
  · rintro rfl
    simp

theorem frobNormSq_eq_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : frobNormSq M = ‖M‖ ^ 2 := by
  classical
  simp only [frobNormSq_eq_sum_normSq, Complex.normSq_eq_norm_sq,
    Fintype.sum_prod_type, frobNorm_sq]

/-- A matrix's Frobenius self-inner-product is its squared Frobenius norm. -/
theorem frobInner_self_eq_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : frobInner M M = (‖M‖ ^ 2 : ℝ) := by
  rw [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq, frobInner_self_eq_sum_normSq]

/-- The squared Frobenius distance, expanded through the Frobenius inner product. -/
theorem frobNorm_sub_sq {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℂ) :
    ‖M - N‖ ^ 2 = ‖M‖ ^ 2 + ‖N‖ ^ 2 - 2 * (frobInner N M).re := by
  have hconj := congrArg Complex.re (frobInner_conj N M)
  simp only [Complex.star_def, Complex.conj_re] at hconj
  rw [← frobNormSq_eq_norm_sq, frobNormSq, frobInner_sub_left,
    frobInner_sub_right, frobInner_sub_right, Complex.sub_re, Complex.sub_re,
    Complex.sub_re, frobInner_self_eq_norm_sq, frobInner_self_eq_norm_sq]
  simp only [Complex.ofReal_re]
  linarith

/-- Frobenius Cauchy--Schwarz in the project's explicit inner product. -/
theorem norm_frobInner_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : ‖frobInner A B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  have hnorm (M : Matrix m n ℂ) :
      ‖toLp 2 (fun p : m × n ↦ M p.1 p.2)‖ = ‖M‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, frobNorm_sq, Fintype.sum_prod_type]
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (toLp 2 (fun p : m × n ↦ A p.1 p.2))
    (toLp 2 (fun p : m × n ↦ B p.1 p.2))
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    ofLp_toLp, frobInner_eq_sum_prod, mul_comm, hnorm] using h

/-- Move left multiplication across the Frobenius inner product. -/
theorem frobInner_mul_left {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    (J : Matrix m r ℂ) (B : Matrix r n ℂ) (M : Matrix m n ℂ) :
    frobInner (J * B) M = frobInner B (Jᴴ * M) := by
  simp only [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- An isometric inclusion preserves the full Frobenius norm. -/
theorem IsIsometry.frobNorm_mul_eq {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq r] {J : Matrix m r ℂ} (hJ : IsIsometry J) (B : Matrix r n ℂ) :
    ‖J * B‖ = ‖B‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← frobNormSq_eq_norm_sq, ← frobNormSq_eq_norm_sq]
  simp only [frobNormSq, frobInner_mul_left, ← Matrix.mul_assoc Jᴴ J,
    hJ.conjTranspose_mul_self, Matrix.one_mul]

/-- Columns of an isometry form an orthonormal family in coefficient space. -/
theorem IsIsometry.orthonormal_columns {m r : Type*} [Fintype m] [Fintype r]
    [DecidableEq r] {J : Matrix m r ℂ} (hJ : IsIsometry J) :
    Orthonormal ℂ (fun k ↦ toLp 2 (fun i ↦ J i k)) := by
  classical
  rw [orthonormal_iff_ite]
  intro k l
  have h := congrArg (fun M : Matrix r r ℂ ↦ M k l) hJ.conjTranspose_mul_self
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm] using h

/-- Every row of an isometry has squared coefficient mass at most one,
by Bessel's inequality. This is the fractional-selection upper bound. -/
theorem IsIsometry.row_norm_sq_le_one {m r : Type*} [Fintype m] [Fintype r]
    [DecidableEq r] {J : Matrix m r ℂ} (hJ : IsIsometry J) (i : m) :
    ∑ k, ‖J i k‖ ^ 2 ≤ 1 := by
  classical
  have h := hJ.orthonormal_columns.sum_inner_products_le
    (s := Finset.univ) (toLp 2 (Pi.single i (1 : ℂ)))
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    EuclideanSpace.norm_sq_eq, Pi.single_apply] using h

/-- The sum of all row masses of an isometry is its column dimension. -/
theorem IsIsometry.sum_row_norm_sq {m r : Type*} [Fintype m] [Fintype r]
    [DecidableEq r] {J : Matrix m r ℂ} (hJ : IsIsometry J) :
    ∑ i, ∑ k, ‖J i k‖ ^ 2 = (Fintype.card r : ℝ) := by
  classical
  have h := congrArg Complex.re (frobInner_self_of_isometry hJ)
  simpa only [← frobNorm_sq, ← frobNormSq_eq_norm_sq, frobNormSq, Complex.natCast_re]
    using h

/-- The Frobenius norm squared is the real trace of the left Gram matrix. -/
theorem norm_sq_eq_re_trace_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ‖M‖ ^ 2 = (M * Mᴴ).trace.re := by
  rw [← frobNormSq_eq_norm_sq, frobNormSq, frobInner_eq_trace, Matrix.trace_mul_comm]

theorem IsIsometry.frobInner_mul_mul {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    {J : Matrix m r ℂ} (hJ : IsIsometry J) (A B : Matrix r n ℂ) :
    frobInner (J * A) (J * B) = frobInner A B := by
  classical
  rw [frobInner_mul_left, ← Matrix.mul_assoc Jᴴ J, hJ.conjTranspose_mul_self, Matrix.one_mul]

end NLQCLean
