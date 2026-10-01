import NLQCLean.LinearAlgebra.Isometry
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact coefficient-support factorization

The compression uses orthonormal bases of coefficient spans, with their ranks.
The factorization here neither pads an isometry nor truncates a state.
-/

namespace NLQCLean

open Matrix WithLp
open scoped ComplexConjugate InnerProductSpace Kronecker

/-- Every complex matrix factors through an isometric inclusion with exactly
its rank many columns. -/
theorem exists_isometry_rank_factorization {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    ∃ J : Matrix m (Fin A.rank) ℂ, ∃ B : Matrix (Fin A.rank) n ℂ,
      IsIsometry J ∧ A = J * B := by
  let S := LinearMap.range A.toEuclideanLin
  have hdim : Module.finrank ℂ S = A.rank :=
    (A.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℂ m) (PiLp.basisFun 2 ℂ n)).symm
  let b : OrthonormalBasis (Fin A.rank) ℂ S :=
    (stdOrthonormalBasis ℂ S).reindex (finCongr hdim)
  have hcol (j : n) : toLp 2 (fun i => A i j) ∈ S := by
    refine ⟨toLp 2 (Pi.single j 1), ?_⟩
    ext i
    simp [Matrix.toLpLin_apply]
  let J : Matrix m (Fin A.rank) ℂ := fun i k => (b k : EuclideanSpace ℂ m) i
  let B : Matrix (Fin A.rank) n ℂ := fun k j => b.repr ⟨toLp 2 (fun i => A i j), hcol j⟩ k
  refine ⟨J, B, ?_, ?_⟩
  · unfold IsIsometry
    ext i j
    change (∑ k, star (J k i) * J k j) = if i = j then 1 else 0
    have h := b.inner_eq_ite i j
    simpa only [J, Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Pi.star_apply, mul_comm] using h
  · ext i j
    change A i j = ∑ k, J i k * B k j
    have h := congrArg (fun v : S => (v : EuclideanSpace ℂ m) i)
      (b.sum_repr ⟨toLp 2 (fun i => A i j), hcol j⟩)
    have hsum : ∑ k, B k j * J i k = A i j := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, ofLp_sum,
        Finset.sum_apply, ofLp_smul, Pi.smul_apply, smul_eq_mul, ofLp_toLp] using h
    exact hsum.symm.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)

/-- Two-sided coefficient-support factorization at the matrix rank.
The right inclusion is transposed, not conjugate transposed: its columns
are Bob's coefficient vectors, obtained from the columns of `Aᵀ`. -/
theorem exists_isometry_two_sided_factorization {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    ∃ JA : Matrix m (Fin A.rank) ℂ, ∃ JB : Matrix n (Fin A.rank) ℂ,
      ∃ B : Matrix (Fin A.rank) (Fin A.rank) ℂ,
        IsIsometry JA ∧ IsIsometry JB ∧ A = JA * B * JBᵀ := by
  obtain ⟨JA, C, hJA, hA⟩ := exists_isometry_rank_factorization A
  obtain ⟨JB, E, hJB, hAT⟩ :
      ∃ JB : Matrix n (Fin A.rank) ℂ, ∃ E : Matrix (Fin A.rank) m ℂ,
        IsIsometry JB ∧ Aᵀ = JB * E := by
    exact (Matrix.rank_transpose A) ▸ exists_isometry_rank_factorization Aᵀ
  have hright : A = Eᵀ * JBᵀ := by
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using congrArg Matrix.transpose hAT
  refine ⟨JA, JB, JAᴴ * Eᵀ, hJA, hJB, ?_⟩
  have hproj : JA * (JAᴴ * A) = A := by
    calc
      JA * (JAᴴ * A) = JA * (JAᴴ * (JA * C)) :=
        congrArg (fun M : Matrix m n ℂ => JA * (JAᴴ * M)) hA
      _ = JA * C := by
        rw [← Matrix.mul_assoc JAᴴ, hJA.conjTranspose_mul_self, Matrix.one_mul]
      _ = A := hA.symm
  exact hproj.symm.trans ((congrArg (fun M : Matrix m n ℂ => JA * (JAᴴ * M))
    hright).trans (by simp only [Matrix.mul_assoc]))

/-- Isometries preserve the coefficient Hermitian form, with no nonempty
assumption on either finite index type. -/
theorem IsIsometry.star_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {J : Matrix m n ℂ} (hJ : IsIsometry J) (v : n → ℂ) :
    star (J *ᵥ v) ⬝ᵥ (J *ᵥ v) = star v ⬝ᵥ v := by
  classical
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hJ.conjTranspose_mul_self, Matrix.one_mulVec]

/-- A unit vector remains unit under an isometric inclusion, and conversely. -/
theorem IsIsometry.isUnitVector_mulVec_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {J : Matrix m n ℂ} (hJ : IsIsometry J) (v : n → ℂ) :
    IsUnitVector (J *ᵥ v) ↔ IsUnitVector v := by
  rw [isUnitVector_iff_sum, isUnitVector_iff_sum]
  have h := hJ.star_dotProduct_mulVec v
  simpa only [dotProduct, Pi.star_apply, mul_comm] using (congrArg (fun z : ℂ => z = 1) h).to_iff

/-- Vectorizing a two-sided coefficient matrix gives the tensor action of
the two local inclusions. The transpose on the right is essential. -/
theorem kronecker_mulVec_coefficients {m n r s : Type*}
    [Fintype r] [Fintype s] (JA : Matrix m r ℂ) (JB : Matrix n s ℂ)
    (B : Matrix r s ℂ) :
    (JA ⊗ₖ JB) *ᵥ (fun p : r × s => B p.1 p.2) =
      fun p : m × n => (JA * B * JBᵀ) p.1 p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Removing an isometric inclusion preserves the isometry constraint. -/
theorem IsIsometry.mul_iff {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {J : Matrix m n ℂ} (hJ : IsIsometry J) (B : Matrix n k ℂ) :
    IsIsometry (J * B) ↔ IsIsometry B := by
  unfold IsIsometry
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ,
    hJ.conjTranspose_mul_self, Matrix.one_mul]

/-- Retained encoder support: the first output factor is spanned by
at most `input dimension × second output dimension` coefficient vectors. -/
theorem exists_left_coefficient_factorization {κ μ ι : Type*}
    [Fintype κ] [Fintype μ] [Fintype ι]
    [DecidableEq κ] [DecidableEq μ] [DecidableEq ι]
    (V : Matrix (κ × μ) ι ℂ) :
    ∃ r : ℕ, r ≤ Fintype.card ι * Fintype.card μ ∧
      ∃ J : Matrix κ (Fin r) ℂ, ∃ B : Matrix (Fin r × μ) ι ℂ,
        IsIsometry J ∧ V = (J ⊗ₖ (1 : Matrix μ μ ℂ)) * B := by
  let C : Matrix κ (μ × ι) ℂ := fun k p => V (k, p.1) p.2
  obtain ⟨J, E, hJ, hC⟩ := exists_isometry_rank_factorization C
  let B : Matrix (Fin C.rank × μ) ι ℂ := fun p j => E p.1 (p.2, j)
  refine ⟨C.rank, ?_, J, B, hJ, ?_⟩
  · simpa only [Fintype.card_prod, Nat.mul_comm] using C.rank_le_card_width
  · ext p j
    change V p j = ∑ q, (J ⊗ₖ (1 : Matrix μ μ ℂ)) p q * B q j
    have h := congrArg (fun M : Matrix κ (μ × ι) ℂ => M p.1 (p.2, j)) hC
    simpa [C, B, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply] using h

/-- Decoder environment support: the second output factor is spanned
by at most `first output dimension × input dimension` coefficient vectors. -/
theorem exists_right_coefficient_factorization {ι ε κ : Type*}
    [Fintype ι] [Fintype ε] [Fintype κ]
    [DecidableEq ι] [DecidableEq ε] [DecidableEq κ]
    (D : Matrix (ι × ε) κ ℂ) :
    ∃ r : ℕ, r ≤ Fintype.card ι * Fintype.card κ ∧
      ∃ J : Matrix ε (Fin r) ℂ, ∃ B : Matrix (ι × Fin r) κ ℂ,
        IsIsometry J ∧ D = ((1 : Matrix ι ι ℂ) ⊗ₖ J) * B := by
  let C : Matrix ε (ι × κ) ℂ := fun e p => D (p.1, e) p.2
  obtain ⟨J, E, hJ, hC⟩ := exists_isometry_rank_factorization C
  let B : Matrix (ι × Fin C.rank) κ ℂ := fun p j => E p.2 (p.1, j)
  refine ⟨C.rank, ?_, J, B, hJ, ?_⟩
  · simpa only [Fintype.card_prod] using C.rank_le_card_width
  · ext p j
    change D p j = ∑ q, ((1 : Matrix ι ι ℂ) ⊗ₖ J) p q * B q j
    have h := congrArg (fun M : Matrix ε (ι × κ) ℂ => M p.2 (p.1, j)) hC
    simpa [C, B, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply] using h

/-- A unit coefficient vector has a nonempty finite index set. -/
theorem IsUnitVector.card_pos {ε : Type*} [Fintype ε] {v : ε → ℂ}
    (hv : IsUnitVector v) : 0 < Fintype.card ε := by
  classical
  by_contra h
  have hzero : Fintype.card ε = 0 := by omega
  let : IsEmpty ε := Fintype.card_eq_zero_iff.mp hzero
  simp [IsUnitVector] at hv

/-- The number of columns of a rectangular isometry cannot exceed its rows. -/
theorem IsIsometry.card_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {J : Matrix m n ℂ} (hJ : IsIsometry J) :
    Fintype.card n ≤ Fintype.card m := by
  calc
    Fintype.card n = (Jᴴ * J).rank := by rw [hJ.conjTranspose_mul_self, Matrix.rank_one]
    _ ≤ J.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card m := Matrix.rank_le_card_height _

end NLQCLean
