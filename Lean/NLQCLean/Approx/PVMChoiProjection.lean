import NLQCLean.Approx.PVMBlockSpectrum
import NLQCLean.Models.ProjectiveExactness

/-!
# good-flag Choi projection

The retained environment vectors are the correct
outcome blocks on the target basis inputs. They need not have norm one.
The normalized projected Choi vector has squared norm and overlap equal to
the physical PVM score, so its top-K Schmidt mass is at least the score squared.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

section Projection
variable {δ εA εB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- The unnormalized correct-outcome environment on each target column. -/
noncomputable def pvmEnvironment
    (M : Matrix δ δ ℂ) (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ)
    (i : δ) : εA × εB → ℂ :=
  outcomeBlock F i i *ᵥ pvmColumn M i

/-- The good-flag projection in dilation coordinates. -/
noncomputable def pvmProjectedDilation
    (M : Matrix δ δ ℂ) (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    Matrix ((δ × εA) × (δ × εB)) δ ℂ :=
  flagIsometry (pvmEnvironment M F) * Mᴴ

omit [DecidableEq εA] [DecidableEq εB] in
theorem sum_normSq_pvmEnvironment_le_one
    {M : Matrix δ δ ℂ} {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) (i : δ) :
    ∑ e, Complex.normSq (pvmEnvironment M F i e) ≤ 1 :=
  sum_normSq_outcomeBlock_le_one hF (isUnitVector_pvmColumn hM i) i i

/-- Move an adjoint on the right across the Frobenius inner product. -/
theorem frobInner_mul_adjoint_right {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r]
    (A : Matrix m r ℂ) (M : Matrix n r ℂ) (F : Matrix m n ℂ) :
    frobInner (A * Mᴴ) F = frobInner A (F * M) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    Matrix.trace_mul_comm M (Aᴴ * F), Matrix.mul_assoc]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Both local flags force the same label in the inner-product sum. -/
theorem frobInner_flagIsometry
    (ω : δ → εA × εB → ℂ) (B : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    frobInner (flagIsometry ω) B =
      ∑ i, ∑ e, star (ω i e) * B ((i,e.1),(i,e.2)) i := by
  rw [frobInner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fintype.sum_prod_type, flagIsometry_apply, apply_ite (starRingEnd ℂ), ite_mul, mul_ite]

omit [DecidableEq εA] [DecidableEq εB] in
theorem frobInner_flag_mul_adjoint
    (ω : δ → εA × εB → ℂ) (M : Matrix δ δ ℂ)
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    frobInner (flagIsometry ω * Mᴴ) F =
      ∑ i, ∑ e, star (ω i e) * pvmEnvironment M F i e := by
  rw [frobInner_mul_adjoint_right, frobInner_flagIsometry]
  rfl

omit [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
theorem pvmEnvironment_projected
    {M : Matrix δ δ ℂ} (hM : IsIsometry M)
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    pvmEnvironment M (pvmProjectedDilation M F) = pvmEnvironment M F := by
  funext i e
  change ((pvmProjectedDilation M F) * M) ((i,e.1),(i,e.2)) i = _
  rw [pvmProjectedDilation, Matrix.mul_assoc, hM, Matrix.mul_one]
  simp [flagIsometry_apply]

omit [DecidableEq εA] [DecidableEq εB] in
theorem frobInner_pvmProjectedDilation
    (M : Matrix δ δ ℂ) (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    frobInner (pvmProjectedDilation M F) F =
      ((∑ i, ∑ e, Complex.normSq (pvmEnvironment M F i e) : ℝ) : ℂ) := by
  rw [pvmProjectedDilation, frobInner_flag_mul_adjoint]
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

omit [DecidableEq εA] [DecidableEq εB] in
theorem frobInner_pvmProjectedDilation_self
    {M : Matrix δ δ ℂ} (hM : IsIsometry M)
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) :
    frobInner (pvmProjectedDilation M F) (pvmProjectedDilation M F) =
      frobInner (pvmProjectedDilation M F) F := by
  change frobInner (flagIsometry (pvmEnvironment M F) * Mᴴ)
    (pvmProjectedDilation M F) = _
  rw [frobInner_flag_mul_adjoint, pvmEnvironment_projected hM,
    frobInner_pvmProjectedDilation]
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

omit [DecidableEq εA] [DecidableEq εB] in
theorem norm_resourceMatrix_pvmEnvironment_le_one
    {M : Matrix δ δ ℂ} {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) (i : δ) :
    ‖resourceMatrix (pvmEnvironment M F i)‖ ≤ 1 := by
  have h := sum_normSq_pvmEnvironment_le_one hF hM i
  rw [← norm_sq_resourceMatrix] at h
  nlinarith [norm_nonneg (resourceMatrix (pvmEnvironment M F i))]

end Projection

section Choi
variable {ιA ιB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- The projected and original normalized Choi vectors overlap by q itself,
not by its square root. No exactness or normalization of the flags is assumed. -/
theorem frobInner_tensorChoiMatrix_pvmProjected
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (F : Matrix (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (ιA × ιB) ℂ) :
    frobInner (tensorChoiMatrix (pvmProjectedDilation M F)) (tensorChoiMatrix F) =
      (scorePVM M (channelOf
        (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id)) : ℂ) := by
  rw [frobInner_tensorChoiMatrix, frobInner_pvmProjectedDilation,
    scorePVM_channelOf_regrouped]
  simp only [pvmEnvironment, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

omit [DecidableEq εA] [DecidableEq εB] in
/-- The good-flag projection has squared norm q. It is unnormalized. -/
theorem norm_sq_tensorChoiMatrix_pvmProjected
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M)
    (F : Matrix (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (ιA × ιB) ℂ) :
    ‖tensorChoiMatrix (pvmProjectedDilation M F)‖ ^ 2 =
      scorePVM M (channelOf
        (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id)) := by
  rw [← frobNormSq_eq_norm_sq, frobNormSq, frobInner_tensorChoiMatrix,
    frobInner_pvmProjectedDilation_self hM, ← frobInner_tensorChoiMatrix,
    frobInner_tensorChoiMatrix_pvmProjected, Complex.ofReal_re]

omit [DecidableEq εB] in
/-- The rank-K Choi vector forces at least q² of Schmidt mass in
its unnormalized good-flag projection. -/
theorem scorePVM_sq_le_schmidtMass_pvmProjected
    [Nonempty ιA] [Nonempty ιB]
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    {F : Matrix (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (ιA × ιB) ℂ}
    (hF : IsIsometry F) {K : ℕ} (hK : (tensorChoiMatrix F).rank ≤ K) :
    (scorePVM M (channelOf
      (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id))) ^ 2 ≤
      schmidtMass K (tensorChoiMatrix (pvmProjectedDilation M F)) := by
  have h := norm_frobInner_sq_le_schmidtMass
    (tensorChoiMatrix (pvmProjectedDilation M F)) (tensorChoiMatrix F)
    (norm_tensorChoiMatrix_of_isometry hF) hK
  rw [← frobInner_conj, frobInner_tensorChoiMatrix_pvmProjected] at h
  simpa only [Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

/-- Regroup only within one laboratory to put the classical flag last. -/
def pvmChoiLocalRegroup (δ n e : Type*) : (e × n) × δ ≃ (δ × n) × e where
  toFun x := ((x.2,x.1.2),x.1.1)
  invFun x := ((x.2,x.1.2),x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Kronecker in
omit [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- In local coordinates, a flagged frozen Choi matrix is literally a block
sum of environment matrices tensored with conjugate target columns. -/
theorem tensorChoiMatrix_flag_mul_adjoint_blockDiagonal
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (ω : (ιA × ιB) → εA × εB → ℂ) :
    (tensorChoiMatrix (flagIsometry ω * Mᴴ)).submatrix
      (pvmChoiLocalRegroup (ιA × ιB) ιA εA)
      (pvmChoiLocalRegroup (ιA × ιB) ιB εB) =
    Matrix.blockDiagonal (fun i =>
      ((Real.sqrt (Fintype.card (ιA × ιB) : ℝ))⁻¹ : ℂ) •
        (resourceMatrix (ω i) ⊗ₖ (fun a b => star (M (a,b) i)))) := by
  ext x y
  rw [Matrix.blockDiagonal_apply]
  change ((Real.sqrt (Fintype.card (ιA × ιB) : ℝ))⁻¹ : ℂ) *
    outcomeBlock (flagIsometry ω * Mᴴ) x.2 y.2 (x.1.1,y.1.1) (x.1.2,y.1.2) = _
  rw [outcomeBlock_flag_mul_adjoint_apply]
  by_cases h : x.2 = y.2
  · rw [if_pos h, if_pos h]
    rfl
  · simp only [if_neg h, mul_zero]

/-- The conjugated target-column coefficient matrix across the laboratory cut. -/
def pvmConjugateColumnMatrix
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) : Matrix ιA ιB ℂ :=
  Matrix.of fun a b => star (M (a,b) i)

/-- The conjugate coefficient matrix of a target column has unit Frobenius
norm. Conjugation therefore does not change its probability normalization. -/
theorem norm_conjugate_pvmColumnMatrix
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) (i : ιA × ιB) :
    ‖pvmConjugateColumnMatrix M i‖ = 1 := by
  have h := isUnitVector_pvmColumn hM i
  have hs : ‖pvmConjugateColumnMatrix M i‖ ^ 2 = 1 := by
    rw [frobNorm_sq]
    simpa [IsUnitVector, pvmColumn, pvmConjugateColumnMatrix, Fintype.sum_prod_type,
      Complex.normSq_eq_norm_sq] using h
  nlinarith [norm_nonneg (pvmConjugateColumnMatrix M i)]

omit [DecidableEq εB] in
/-- The two outcome flags expose precisely the normalized product Schmidt
weights, in an enumeration that permits ties and zero coefficients. -/
theorem schmidtMass_tensorChoiMatrix_flag_mul_adjoint
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (ω : (ιA × ιB) → εA × εB → ℂ) (K : ℕ) :
    schmidtMass K (tensorChoiMatrix (flagIsometry ω * Mᴴ)) =
      topWeightMass K (fun p : (εA × ιA) × (ιA × ιB) =>
        (Fintype.card (ιA × ιB) : ℝ)⁻¹ *
          (schmidtWeights (resourceMatrix (ω p.2)) p.1.1 *
            schmidtWeights (fun a b => star (M (a,b) p.2)) p.1.2)) := by
  rw [← schmidtMass_submatrix_equiv _
    (pvmChoiLocalRegroup (ιA × ιB) ιA εA)
    (pvmChoiLocalRegroup (ιA × ιB) ιB εB) K,
    tensorChoiMatrix_flag_mul_adjoint_blockDiagonal]
  rw [schmidtMass_blockDiagonal_scaledKronecker_eq
    (fun i => resourceMatrix (ω i))
    (fun i => (fun a b => star (M (a,b) i) : Matrix ιA ιB ℂ))
    (fun _ => ((Real.sqrt (Fintype.card (ιA × ιB) : ℝ))⁻¹ : ℂ)) K]
  congr 1
  funext p
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

end Choi

section Protocol
variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- The overlap bound for the original pure protocol and charged footprint. -/
theorem PureProtocol.scorePVM_sq_le_schmidtMass_pvmProjected
    [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    (scorePVM M P.operationalChannel) ^ 2 ≤
      schmidtMass K (tensorChoiMatrix (pvmProjectedDilation M P.globalIsometry)) := by
  apply NLQCLean.scorePVM_sq_le_schmidtMass_pvmProjected M P.isIsometry_globalIsometry
  rw [rank_tensorChoiMatrix]
  exact P.rank_normalizedLabChoiMatrix_le_of_hasFootprint hK

end Protocol
end NLQCLean
