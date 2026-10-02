import NLQCLean.LinearAlgebra.FrobeniusInner
import NLQCLean.LinearAlgebra.SchmidtTruncation
import NLQCLean.LinearAlgebra.SchmidtRank
import Mathlib.Analysis.Matrix.PosDef

/-!
# Best finite-rank Frobenius overlap

Gram diagonalization supplies the squared Schmidt weights;
the finite weight optimization controls projections onto a test matrix's
coefficient support. All norms here are ordinary Frobenius norms.
-/

namespace NLQCLean

open Matrix WithLp
open scoped Matrix.Norms.Frobenius ComplexConjugate

/-- In coordinates with diagonal left Gram matrix, projecting onto an
isometry's columns weights the squared row masses by the Gram eigenvalues. -/
theorem norm_sq_adjoint_mul_of_diagonal_gram {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r] [DecidableEq m]
    (M : Matrix m n ℂ) (J : Matrix m r ℂ) (w : m → ℝ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) :
    ‖Jᴴ * M‖ ^ 2 = ∑ i, w i * ∑ k, ‖J i k‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_trace_mul_conjTranspose]
  have hmul : (Jᴴ * M) * (Jᴴ * M)ᴴ = Jᴴ * (M * Mᴴ) * J := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hmul, hgram]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hz : star (J i k) * (w i : ℂ) * J i k =
      (w i : ℂ) * (Complex.normSq (J i k) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (J i k) * (w i : ℂ) * J i k = (w i : ℂ) * (star (J i k) * J i k)
    ring
  rw [hz, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The best-rank upper bound when the Gram matrix is diagonal. No nonzero
or full-rank premise is required for the target matrix. -/
theorem norm_frobInner_sq_le_topWeightMass_of_diagonal_gram {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (M W : Matrix m n ℂ) (w : m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ)))
    {K : ℕ} (hW : ‖W‖ = 1) (hrank : W.rank ≤ K) :
    ‖frobInner W M‖ ^ 2 ≤ topWeightMass K w := by
  classical
  obtain ⟨J, B, hJ, hfac⟩ := exists_isometry_rank_factorization W
  have hB : ‖B‖ = 1 := (hJ.frobNorm_mul_eq B).symm.trans (congrArg norm hfac.symm |>.trans hW)
  have hinner : ‖frobInner W M‖ ≤ ‖Jᴴ * M‖ := by
    have he := congrArg (fun X : Matrix m n ℂ ↦ frobInner X M) hfac
    rw [frobInner_mul_left] at he
    rw [he]
    simpa [hB] using norm_frobInner_le B (Jᴴ * M)
  calc
    ‖frobInner W M‖ ^ 2 ≤ ‖Jᴴ * M‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hinner
    _ = ∑ i, w i * ∑ k, ‖J i k‖ ^ 2 := norm_sq_adjoint_mul_of_diagonal_gram M J w hgram
    _ ≤ topWeightMass K w := sum_mul_le_topWeightMass K w _ hw
      (fun i ↦ Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)) hJ.row_norm_sq_le_one
      (by rw [hJ.sum_row_norm_sq, Fintype.card_fin]; exact_mod_cast hrank)

/-- Retain precisely the rows in a finite support. -/
def truncateRows {m n : Type*} [DecidableEq m] (s : Finset m) (M : Matrix m n ℂ) :
    Matrix m n ℂ := fun i j ↦ if i ∈ s then M i j else 0

theorem rank_truncateRows_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (s : Finset m) (M : Matrix m n ℂ) : (truncateRows s M).rank ≤ s.card := by
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro i hi
  change i ∉ s at hi
  funext j
  simp [Matrix.row, truncateRows, hi]

/-- Each diagonal Gram entry is the squared row norm. -/
theorem row_inner_of_diagonal_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (w : m → ℝ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) (i : m) :
    ∑ j, star (M i j) * M i j = (w i : ℂ) := by
  have h := congrArg (fun N : Matrix m m ℂ ↦ N i i) hgram
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h

theorem frobInner_truncateRows_of_diagonal_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (s : Finset m) (M : Matrix m n ℂ) (w : m → ℝ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) :
    frobInner (truncateRows s M) M = (∑ i ∈ s, w i : ℝ) := by
  have hrow (i : m) : (∑ j, star (truncateRows s M i j) * M i j) =
      if i ∈ s then (w i : ℂ) else 0 := by
    by_cases hi : i ∈ s
    · simpa only [truncateRows, ite_eq_left hi] using row_inner_of_diagonal_gram M w hgram i
    · simp [truncateRows, hi]
  simp only [frobInner, hrow]
  simp

theorem norm_sq_truncateRows_of_diagonal_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (s : Finset m) (M : Matrix m n ℂ) (w : m → ℝ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) :
    ‖truncateRows s M‖ ^ 2 = ∑ i ∈ s, w i := by
  have hself : frobInner (truncateRows s M) (truncateRows s M) =
      frobInner (truncateRows s M) M := by
    simp only [frobInner]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [truncateRows, hi]
  rw [← frobNormSq_eq_norm_sq, frobNormSq, hself,
    frobInner_truncateRows_of_diagonal_gram s M w hgram, Complex.ofReal_re]

/-- A positive top-K mass has an attaining normalized row truncation, with
its phase fixed so that the Frobenius overlap is the positive square root. -/
theorem exists_truncation_of_diagonal_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (w : m → ℝ)
    (hgram : M * Mᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) (K : ℕ)
    (hu : 0 < topWeightMass K w) :
    ∃ W : Matrix m n ℂ, ‖W‖ = 1 ∧ W.rank ≤ K ∧
      frobInner W M = (Real.sqrt (topWeightMass K w) : ℂ) := by
  classical
  obtain ⟨s, hs, hsum⟩ := exists_topWeightMass_support K w
  let u := topWeightMass K w
  let T := truncateRows s M
  have hT_sq : ‖T‖ ^ 2 = u :=
    (norm_sq_truncateRows_of_diagonal_gram s M w hgram).trans hsum.symm
  have hT : ‖T‖ = Real.sqrt u := by rw [← hT_sq, Real.sqrt_sq (norm_nonneg _)]
  have hinner : frobInner T M = (u : ℂ) := by
    rw [frobInner_truncateRows_of_diagonal_gram s M w hgram, ← hsum]
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  let W : Matrix m n ℂ := ((Real.sqrt u)⁻¹ : ℂ) • T
  refine ⟨W, ?_, (rank_smul_le _ T).trans ((rank_truncateRows_le s M).trans hs), ?_⟩
  · change ‖((Real.sqrt u)⁻¹ : ℂ) • T‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsqrt.le, hT, inv_mul_cancel₀ hsqrt.ne']
  · change frobInner (((Real.sqrt u)⁻¹ : ℂ) • T) M = _
    rw [frobInner_smul_left, hinner]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have hu_sq : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by
      exact_mod_cast Real.sq_sqrt hu.le
    rw [← hu_sq, pow_two, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hsqrt.ne'), one_mul]

/-- Squared Schmidt weights, defined as the eigenvalues of the left Gram matrix.
The enumeration may be arbitrary; `topWeightMass` is invariant under reindexing. -/
noncomputable def schmidtWeights {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) : m → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues

/-- The sum of the K largest squared Schmidt coefficients, padded by zeros. -/
noncomputable def schmidtMass {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (K : ℕ) (M : Matrix m n ℂ) : ℝ :=
  topWeightMass K (schmidtWeights M)

theorem schmidtWeights_nonneg {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (i : m) : 0 ≤ schmidtWeights M i :=
  Matrix.eigenvalues_self_mul_conjTranspose_nonneg M i

theorem sum_schmidtWeights {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) : ∑ i, schmidtWeights M i = ‖M‖ ^ 2 := by
  rw [norm_sq_eq_re_trace_mul_conjTranspose]
  have h := congrArg Complex.re (Matrix.isHermitian_mul_conjTranspose_self M).trace_eq_sum_eigenvalues
  simpa [schmidtWeights, Complex.re_sum] using h.symm

/-- The spectral theorem supplies unitary row coordinates with diagonal Gram. -/
theorem exists_schmidt_coordinates {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) :
    ∃ V : Matrix m m ℂ, IsIsometry V ∧ IsIsometry Vᴴ ∧
      (Vᴴ * M) * (Vᴴ * M)ᴴ = Matrix.diagonal (fun i ↦ (schmidtWeights M i : ℂ)) := by
  let hG := Matrix.isHermitian_mul_conjTranspose_self M
  let U := hG.eigenvectorUnitary
  refine ⟨U, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self U
  · simpa only [IsIsometry, Matrix.conjTranspose_conjTranspose, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  · have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    change (U : Matrix m m ℂ)ᴴ * (M * Mᴴ) * (U : Matrix m m ℂ) =
      Matrix.diagonal (fun i ↦ (hG.eigenvalues i : ℂ)) at h
    change ((U : Matrix m m ℂ)ᴴ * M) * ((U : Matrix m m ℂ)ᴴ * M)ᴴ =
      Matrix.diagonal (fun i ↦ (hG.eigenvalues i : ℂ))
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using h

/-- Best-rank overlap upper bound for arbitrary rectangular coefficient matrices. -/
theorem norm_frobInner_sq_le_schmidtMass {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] (M W : Matrix m n ℂ)
    {K : ℕ} (hW : ‖W‖ = 1) (hrank : W.rank ≤ K) :
    ‖frobInner W M‖ ^ 2 ≤ schmidtMass K M := by
  obtain ⟨V, _, hV', hgram⟩ := exists_schmidt_coordinates M
  rw [← hV'.frobInner_mul_mul W M]
  exact norm_frobInner_sq_le_topWeightMass_of_diagonal_gram (Vᴴ * M) (Vᴴ * W)
    (schmidtWeights M) (schmidtWeights_nonneg M) hgram
    ((hV'.frobNorm_mul_eq W).trans hW) ((Matrix.rank_mul_le_right _ _).trans hrank)

/-- An attaining normalized Schmidt truncation, with positive real overlap. -/
theorem exists_schmidt_truncation {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] (M : Matrix m n ℂ) (K : ℕ)
    (hpos : 0 < schmidtMass K M) :
    ∃ W : Matrix m n ℂ, ‖W‖ = 1 ∧ W.rank ≤ K ∧
      frobInner W M = (Real.sqrt (schmidtMass K M) : ℂ) := by
  obtain ⟨V, hV, _, hgram⟩ := exists_schmidt_coordinates M
  obtain ⟨T, hT, hTrank, hinner⟩ :=
    exists_truncation_of_diagonal_gram (Vᴴ * M) (schmidtWeights M) hgram K hpos
  refine ⟨V * T, (hV.frobNorm_mul_eq T).trans hT,
    (Matrix.rank_mul_le_right V T).trans hTrank, ?_⟩
  rw [frobInner_mul_left]
  exact hinner

theorem schmidtMass_pos {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℂ) {K : ℕ} (hK : 1 ≤ K) (hM : ‖M‖ = 1) :
    0 < schmidtMass K M := by
  by_contra h
  have hle : schmidtMass K M ≤ 0 := le_of_not_gt h
  have hw (i : m) : schmidtWeights M i = 0 := by
    have hi := sum_le_topWeightMass (schmidtWeights M) (s := {i}) (by simpa using hK)
    exact le_antisymm ((by simpa [schmidtMass] using hi : schmidtWeights M i ≤ schmidtMass K M).trans hle)
      (schmidtWeights_nonneg M i)
  have hs := sum_schmidtWeights M
  simp [hw, hM] at hs

theorem schmidtMass_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (K : ℕ) (M : Matrix m n ℂ) : 0 ≤ schmidtMass K M :=
  topWeightMass_nonneg _ _

/-- Every unit bipartite vector has an attaining normalized top-K Schmidt
truncation for K >= 1, without an additional positivity premise. -/
theorem exists_schmidt_truncation_of_norm_eq_one {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] (M : Matrix m n ℂ) (K : ℕ)
    (hK : 1 ≤ K) (hM : ‖M‖ = 1) :
    ∃ W : Matrix m n ℂ, ‖W‖ = 1 ∧ W.rank ≤ K ∧
      frobInner W M = (Real.sqrt (schmidtMass K M) : ℂ) :=
  exists_schmidt_truncation M K (schmidtMass_pos M hK hM)

theorem norm_complex_sqrt_sq {u : ℝ} (hu : 0 ≤ u) : ‖(Real.sqrt u : ℂ)‖ ^ 2 = u := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hu]

/-- Any unitary Gram diagonalization computes the same top-K mass. This
follows from the proved variational upper bound and attaining truncation,
so it does not require comparing arbitrary orderings of repeated eigenvalues. -/
theorem schmidtMass_eq_topWeightMass_of_coordinates {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℂ) (V : Matrix m m ℂ) (w : m → ℝ)
    (hV : IsIsometry V) (hV' : IsIsometry Vᴴ) (hw : ∀ i, 0 ≤ w i)
    (hgram : (Vᴴ * M) * (Vᴴ * M)ᴴ = Matrix.diagonal (fun i ↦ (w i : ℂ))) (K : ℕ) :
    schmidtMass K M = topWeightMass K w := by
  apply le_antisymm
  · by_cases hpos : 0 < schmidtMass K M
    · obtain ⟨W, hW, hrank, hinner⟩ := exists_schmidt_truncation M K hpos
      have h := norm_frobInner_sq_le_topWeightMass_of_diagonal_gram
        (Vᴴ * M) (Vᴴ * W) w hw hgram ((hV'.frobNorm_mul_eq W).trans hW)
        ((Matrix.rank_mul_le_right _ _).trans hrank)
      rwa [hV'.frobInner_mul_mul, hinner, norm_complex_sqrt_sq hpos.le] at h
    · exact (le_of_not_gt hpos).trans (topWeightMass_nonneg K w)
  · by_cases hpos : 0 < topWeightMass K w
    · obtain ⟨T, hT, hrank, hinner⟩ := exists_truncation_of_diagonal_gram (Vᴴ * M) w hgram K hpos
      have h := norm_frobInner_sq_le_schmidtMass M (V * T)
        ((hV.frobNorm_mul_eq T).trans hT) ((Matrix.rank_mul_le_right _ _).trans hrank)
      rwa [frobInner_mul_left, hinner, norm_complex_sqrt_sq hpos.le] at h
    · exact (le_of_not_gt hpos).trans (schmidtMass_nonneg K M)

open scoped Kronecker in
/-- The top-K Schmidt mass of a
tensor product of unit vectors is at most the mass of either factor. -/
theorem schmidtMass_kronecker_le_min {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p]
    (K : ℕ) (M : Matrix m n ℂ) (N : Matrix p q ℂ) (hM : ‖M‖ = 1) (hN : ‖N‖ = 1) :
    schmidtMass K (M ⊗ₖ N) ≤ min (schmidtMass K M) (schmidtMass K N) := by
  obtain ⟨V, hV, hV', hgramM⟩ := exists_schmidt_coordinates M
  obtain ⟨U, hU, hU', hgramN⟩ := exists_schmidt_coordinates N
  have hVU' : IsIsometry (V ⊗ₖ U)ᴴ := by
    rw [Matrix.conjTranspose_kronecker]
    exact hV'.kronecker hU'
  have hgram : ((V ⊗ₖ U)ᴴ * (M ⊗ₖ N)) * ((V ⊗ₖ U)ᴴ * (M ⊗ₖ N))ᴴ =
      Matrix.diagonal (fun i : m × p ↦ ((schmidtWeights M i.1 * schmidtWeights N i.2 : ℝ) : ℂ)) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hgramM, hgramN, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]
  rw [schmidtMass_eq_topWeightMass_of_coordinates (M ⊗ₖ N) (V ⊗ₖ U)
    (fun i : m × p ↦ schmidtWeights M i.1 * schmidtWeights N i.2)
    (hV.kronecker hU) hVU' (fun i ↦ mul_nonneg (schmidtWeights_nonneg M _)
      (schmidtWeights_nonneg N _)) hgram]
  exact topWeightMass_product_le_min K _ _ (schmidtWeights_nonneg M) (schmidtWeights_nonneg N)
    (by rw [sum_schmidtWeights, hM, one_pow]) (by rw [sum_schmidtWeights, hN, one_pow])

end NLQCLean
