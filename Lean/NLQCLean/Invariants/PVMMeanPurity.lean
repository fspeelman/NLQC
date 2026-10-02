import NLQCLean.Invariants.OperatorSchmidtPurity
import NLQCLean.LinearAlgebra.Bipartite

/-!
# Mean reduced purity of a basis matrix

For a basis matrix M on ι×ι, reshape each column into an ι×ι
matrix R_i and average tr((R_i R_i†)²). This real degree-four polynomial is
invariant to first order under a common local skew-Hermitian motion on the
left and an independent diagonal skew-Hermitian (column-phase) motion on the
right, for every M, not only unitary M.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section MeanPurity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Column `i` of a basis matrix, reshaped across the ι×ι cut. -/
def pvmColumnMatrix (M : Matrix (ι × ι) (ι × ι) ℂ) (i : ι × ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => M (a, b) i

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pvmColumnMatrix_apply (M : Matrix (ι × ι) (ι × ι) ℂ) (i : ι × ι) (a b : ι) :
    pvmColumnMatrix M i a b = M (a, b) i := rfl

/-- Column reshaping as a `ℂ`-linear map. -/
def pvmColumnLM (i : ι × ι) : Matrix (ι × ι) (ι × ι) ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun M := pvmColumnMatrix M i
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

omit [Fintype ι] [DecidableEq ι] in
theorem pvmColumnMatrix_add_smul (M V : Matrix (ι × ι) (ι × ι) ℂ) (t : ℝ) (i : ι × ι) :
    pvmColumnMatrix (M + t • V) i = pvmColumnMatrix M i + t • pvmColumnMatrix V i := by
  ext; simp

/-- The purity of one reshaped column. -/
noncomputable def gramPurity (R : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace ((R * Rᴴ) * (R * Rᴴ))).re

/-- Mean reduced purity, with explicit normalization `c` (later `c = D⁻¹`). -/
noncomputable def pvmMeanPurity (c : ℝ) (M : Matrix (ι × ι) (ι × ι) ℂ) : ℝ :=
  c * ∑ i, gramPurity (pvmColumnMatrix M i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem ContDiff.pvmMeanPurity (c : ℝ) {N : WithTop ℕ∞} {f : E → Matrix (ι × ι) (ι × ι) ℂ}
    (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.pvmMeanPurity c (f x)) := by
  have hcol (i : ι × ι) : ContDiff ℝ N (fun x => gramPurity (pvmColumnMatrix (f x) i)) := by
    have hR : ContDiff ℝ N (fun x => pvmColumnMatrix (f x) i) :=
      ContDiff.linearMapFD ((pvmColumnLM i).restrictScalars ℝ) hf
    have hRR : ContDiff ℝ N (fun x => pvmColumnMatrix (f x) i * (pvmColumnMatrix (f x) i)ᴴ) :=
      ContDiff.matrixMul hR (ContDiff.matrixConjTranspose hR)
    exact ContDiff.complexRe (ContDiff.matrixTrace (ContDiff.matrixMul hRR hRR))
  exact (ContDiff.sum (fun i _ => hcol i)).const_smul c

/-- With `L, N` skew-Hermitian, the velocity of `S = R R†` is a commutator. -/
theorem gram_velocity_eq_commutator {R L N : Matrix ι ι ℂ}
    (hL : Lᴴ = -L) (hN : Nᴴ = -N) :
    R * (L * R + R * N)ᴴ + (L * R + R * N) * Rᴴ = L * (R * Rᴴ) - (R * Rᴴ) * L := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hL, hN]
  noncomm_ring

theorem trace_sq_commutator_velocity (S L : Matrix ι ι ℂ) :
    Matrix.trace (S * (L * S - S * L) + (L * S - S * L) * S) = 0 := by
  have hrw : S * (L * S - S * L) + (L * S - S * L) * S = L * (S * S) - (S * S) * L := by
    noncomm_ring
  rw [hrw, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- One column's purity has zero derivative along `L R + R N` with skew legs. -/
theorem hasDerivAt_gramPurity_motion {R L N : Matrix ι ι ℂ} (hL : Lᴴ = -L) (hN : Nᴴ = -N) :
    HasDerivAt (fun t : ℝ => gramPurity (R + t • (L * R + R * N))) 0 0 := by
  set K := L * R + R * N with hK
  have hline : HasDerivAt (fun t : ℝ => R + t • K) K 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add R
    simp only [one_smul, id_eq] at h
    exact h
  have h0 : (fun t : ℝ => R + t • K) 0 = R := by simp
  have hRH : HasDerivAt (fun t : ℝ => (R + t • K)ᴴ) Kᴴ 0 := HasDerivAt.matrixConjTranspose hline
  have hS : HasDerivAt (fun t : ℝ => (R + t • K) * (R + t • K)ᴴ) (R * Kᴴ + K * Rᴴ) 0 := by
    have h := HasDerivAt.matrixMul hline hRH
    simpa [h0] using h
  set S := R * Rᴴ with hSdef
  have hSvel : R * Kᴴ + K * Rᴴ = L * S - S * L := by
    rw [hK, hSdef]; exact gram_velocity_eq_commutator hL hN
  rw [hSvel] at hS
  have hSS : HasDerivAt (fun t : ℝ => ((R + t • K) * (R + t • K)ᴴ) * ((R + t • K) * (R + t • K)ᴴ))
      (S * (L * S - S * L) + (L * S - S * L) * S) 0 := by
    have h := HasDerivAt.matrixMul hS hS
    simpa [h0, hSdef] using h
  have htr : HasDerivAt
      (fun t : ℝ => Matrix.trace (((R + t • K) * (R + t • K)ᴴ) * ((R + t • K) * (R + t • K)ᴴ)))
      (Matrix.trace (S * (L * S - S * L) + (L * S - S * L) * S)) 0 :=
    HasDerivAt.ofLinearMap ((Matrix.traceLinearMap ι ℂ ℂ).restrictScalars ℝ) hSS
  rw [trace_sq_commutator_velocity] at htr
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 htr
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.zero_re] at hre
  exact hre

/-- Column `i` of a local-left, diagonal-right motion. -/
theorem pvmColumnMatrix_motion (M : Matrix (ι × ι) (ι × ι) ℂ) (aA aB : Matrix ι ι ℂ)
    {b : Matrix (ι × ι) (ι × ι) ℂ} (hb : ∀ i j, i ≠ j → b i j = 0) (i : ι × ι) :
    pvmColumnMatrix ((aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB) * M + M * b) i =
      (aA + b i i • (1 : Matrix ι ι ℂ)) * pvmColumnMatrix M i + pvmColumnMatrix M i * aBᵀ := by
  ext x y
  have hMb : (M * b) (x, y) i = M (x, y) i * b i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [hb j i hj, mul_zero])
      (by simp)]
  rw [pvmColumnMatrix_apply, Matrix.add_apply, hMb, Matrix.add_mul]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, pvmColumnMatrix_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, add_mul]
  have h2 : ∑ x₁, ∑ x₂, (if x = x₁ then aB y x₂ * M (x₁, x₂) i else 0) =
      ∑ x₂, aB y x₂ * M (x, x₂) i := by
    rw [Finset.sum_eq_single x (fun x₁ _ hx₁ => by simp [Ne.symm hx₁]) (by simp)]
    simp
  rw [h2]
  simp only [mul_comm (M _ i)]
  ring

omit [Fintype ι] in
theorem diag_entry_skew {b : Matrix (ι × ι) (ι × ι) ℂ} (hb : bᴴ = -b) (i : ι × ι) :
    (b i i • (1 : Matrix ι ι ℂ))ᴴ = -(b i i • (1 : Matrix ι ι ℂ)) := by
  have h := congrArg (fun X : Matrix (ι × ι) (ι × ι) ℂ => X i i) hb
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, h, neg_smul]

/-- For every basis matrix `M`, the mean reduced purity has zero
derivative along a common local skew-Hermitian motion on the left plus a diagonal
skew-Hermitian motion on the right. -/
theorem hasDerivAt_pvmMeanPurity_motion (c : ℝ) (M : Matrix (ι × ι) (ι × ι) ℂ)
    {aA aB : Matrix ι ι ℂ} (haA : aAᴴ = -aA) (haB : aBᴴ = -aB)
    {b : Matrix (ι × ι) (ι × ι) ℂ} (hb : b ∈ diagSkew (ι × ι)) :
    HasDerivAt (fun t : ℝ => pvmMeanPurity c (M + t •
      ((aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB) * M + M * b))) 0 0 := by
  obtain ⟨hdiag, hskew⟩ := mem_diagSkew_iff.mp hb
  have hcol (i : ι × ι) : HasDerivAt (fun t : ℝ => gramPurity (pvmColumnMatrix (M + t •
      ((aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB) * M + M * b)) i)) 0 0 := by
    have hL : (aA + b i i • (1 : Matrix ι ι ℂ))ᴴ = -(aA + b i i • (1 : Matrix ι ι ℂ)) := by
      rw [Matrix.conjTranspose_add, haA, diag_entry_skew hskew i, neg_add]
    have hN : (aBᵀ)ᴴ = -(aBᵀ) := conjTranspose_transpose_of_skew haB
    have h := hasDerivAt_gramPurity_motion (R := pvmColumnMatrix M i) hL hN
    simpa only [pvmColumnMatrix_add_smul, pvmColumnMatrix_motion M aA aB hdiag i] using h
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcol i)
  simp only [Finset.sum_const_zero] at hsum
  have hfin := hsum.const_mul c
  simp only [mul_zero] at hfin
  exact hfin

end MeanPurity

end NLQCLean
