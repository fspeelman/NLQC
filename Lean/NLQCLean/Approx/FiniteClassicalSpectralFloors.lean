import NLQCLean.Models.ClassicalCommunication.FiniteBranchSchmidtRank
import NLQCLean.Models.ClassicalCommunication.FiniteMixed
import NLQCLean.Models.ClassicalCommunication.TargetScores
import NLQCLean.Models.ClassicalCommunication.FiniteReachability
import NLQCLean.Approx.PVMSpectralFootprintFloors
import NLQCLean.Approx.GenericSpectralThresholds
import NLQCLean.Models.ProjectiveTV

/-!
# Spectral floors with finite free classical communication

For `lem:free-classical-floors`, fixed classical outcomes carry no Schmidt
rank across the laboratory cut. The actual unnormalized branch vectors have
quantum-only rank caps and total trace one. Duplicated PVM output labels are
projected locally; the sum of their traces can be smaller than one.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- Best-rank overlap for an unnormalized vector. Its squared norm remains
the trace weight of its rank-one state, including a zero branch. -/
theorem norm_frobInner_sq_le_norm_sq_mul_schmidtMass
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M W : Matrix m n ℂ) {K : ℕ} (hrank : W.rank ≤ K) :
    ‖frobInner M W‖ ^ 2 ≤ ‖W‖ ^ 2 * schmidtMass K M := by
  by_cases hW : 0 < ‖W‖
  · obtain ⟨N, hN, hWN, _⟩ := exists_normalized_matrix W hW
    have hrankN : N.rank ≤ K := by
      rw [hWN, Matrix.rank_smul_of_mem_nonZeroDivisors N
        (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hW.ne'))] at hrank
      exact hrank
    have h := norm_frobInner_sq_le_schmidtMass M N hN hrankN
    have h' : ‖frobInner M N‖ ^ 2 ≤ schmidtMass K M := by
      rw [← frobInner_conj M N, norm_star] at h
      exact h
    have hscale : ‖frobInner M W‖ ^ 2 = ‖W‖ ^ 2 * ‖frobInner M N‖ ^ 2 := by
      conv_lhs => rw [hWN, frobInner_smul_right]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg W), mul_pow]
    rw [hscale]
    exact mul_le_mul_of_nonneg_left h' (sq_nonneg _)
  · have hz : W = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hW) (norm_nonneg W))
    simp [hz, frobInner]

/-- The logical Choi inner product keeps the inverse input dimension. -/
theorem frobInner_normalizedLabChoiMatrix
    {a b i j : Type*} [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    (F G : Matrix (a × b) (i × j) ℂ) :
    frobInner (normalizedLabChoiMatrix F) (normalizedLabChoiMatrix G) =
      (Fintype.card (i × j) : ℂ)⁻¹ * frobInner F G := by
  rw [normalizedLabChoiMatrix, normalizedLabChoiMatrix,
    frobInner_smul_left, frobInner_smul_right, frobInner_labChoiMatrix]
  have hs : (Real.sqrt (Fintype.card (i × j) : ℝ) : ℂ) ^ 2 =
      (Fintype.card (i × j) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (i × j)))
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← mul_inv, ← sq, hs]

/-- A single physical Kraus branch contributes its squared Choi overlap. -/
theorem scoreU_adConj_eq_norm_sq_normalizedLabChoiOverlap
    {a b i j : Type*} [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq i] [DecidableEq j]
    (U F : Matrix (a × b) (i × j) ℂ) :
    scoreU U (adConj F) =
      ‖frobInner (normalizedLabChoiMatrix U) (normalizedLabChoiMatrix F)‖ ^ 2 := by
  classical
  let G : Matrix ((a × b) × Unit) (i × j) ℂ := fun p q => F p.1 q
  have hG : channelOf G = adConj F := by
    rw [ClassicalCommunication.channelOf_eq_sum_adConj]
    simp only [Fintype.sum_unique]
    rfl
  rw [← hG, scoreU_channelOf, Fintype.sum_unique,
    frobInner_normalizedLabChoiMatrix, ← Complex.normSq_eq_norm_sq]
  rfl

/-- Project the two local copies of outcome i from an unnormalized Choi
branch. The remaining coefficient matrix is on the two input references. -/
noncomputable def pvmBranchReferenceMatrix
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (F : Matrix ((ιA × ιB) × (ιA × ιB)) (ιA × ιB) ℂ)
    (i : ιA × ιB) : Matrix ιA ιB ℂ :=
  (normalizedLabChoiMatrix F).submatrix (fun a => (i, a)) (fun b => (i, b))

/-- Projection on a product of duplicated labels cannot increase rank. -/
theorem rank_pvmBranchReferenceMatrix_le
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (F : Matrix ((ιA × ιB) × (ιA × ιB)) (ιA × ιB) ℂ)
    (i : ιA × ιB) :
    (pvmBranchReferenceMatrix F i).rank ≤ (normalizedLabChoiMatrix F).rank :=
  Matrix.rank_submatrix_le _ _ _

/-- The diagonal duplicated-label sectors are disjoint. Their total trace
is at most the full unnormalized Choi branch trace. -/
theorem sum_norm_sq_diagonal_localProjection_le
    {δ a b : Type*} [Fintype δ] [Fintype a] [Fintype b]
    (C : Matrix (δ × a) (δ × b) ℂ) :
    ∑ i, ‖C.submatrix (fun x => (i, x)) (fun y => (i, y))‖ ^ 2 ≤ ‖C‖ ^ 2 := by
  classical
  simp only [frobNorm_sq, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.single_le_sum
    (f := fun j : δ => ∑ k : a, ∑ l : b, ‖C (i, k) (j, l)‖ ^ 2)
    (fun j _ => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => sq_nonneg (‖C (i, k) (j, l)‖))))
    (Finset.mem_univ i)

/-- The same trace estimate in the actual PVM Choi-reference coordinates. -/
theorem sum_norm_sq_pvmBranchReferenceMatrix_le
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (F : Matrix ((ιA × ιB) × (ιA × ιB)) (ιA × ιB) ℂ) :
    ∑ i, ‖pvmBranchReferenceMatrix F i‖ ^ 2 ≤ ‖normalizedLabChoiMatrix F‖ ^ 2 :=
  sum_norm_sq_diagonal_localProjection_le _

/-- On one Kraus branch the correct-label PVM score is the sum of overlaps
with the conjugate target columns on the two input references. -/
theorem scorePVM_adConj_eq_sum_norm_sq_referenceOverlap
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    [DecidableEq ιA] [DecidableEq ιB]
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (F : Matrix ((ιA × ιB) × (ιA × ιB)) (ιA × ιB) ℂ) :
    scorePVM M (adConj F) =
      ∑ i, ‖frobInner (pvmConjugateColumnMatrix M i)
        (pvmBranchReferenceMatrix F i)‖ ^ 2 := by
  classical
  let D : Matrix (((ιA × ιB) × Unit) × ((ιA × ιB) × Unit)) (ιA × ιB) ℂ :=
    fun p q => F (p.1.1, p.2.1) q
  have hD : channelOf (D.submatrix (outputRegroup _ _ Unit Unit) id) = adConj F := by
    rw [ClassicalCommunication.channelOf_eq_sum_adConj]
    simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    rfl
  rw [← hD, scorePVM_channelOf_regrouped, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let z : ℂ := ∑ a, F (i, i) a * M a i
  have hi : frobInner (pvmConjugateColumnMatrix M i)
      (pvmBranchReferenceMatrix F i) =
      ((Real.sqrt (Fintype.card (ιA × ιB) : ℝ))⁻¹ : ℂ) * z := by
    simp [frobInner, pvmConjugateColumnMatrix, pvmBranchReferenceMatrix,
      normalizedLabChoiMatrix, labChoiMatrix, z, Fintype.sum_prod_type,
      Finset.mul_sum, mul_comm, mul_assoc]
  rw [hi, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, outcomeBlock,
    Matrix.mulVec, dotProduct, pvmColumn, Matrix.of_apply, D,
    ← Complex.normSq_eq_norm_sq]
  simp only [z, Fintype.sum_prod_type]

/-- The largest target-column top-K mass; ties and zero weights are allowed. -/
noncomputable def pvmMaxColumnSchmidtMass
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    [DecidableEq ιA] [Nonempty ιA] [Nonempty ιB]
    (K : ℕ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  (Finset.univ : Finset (ιA × ιB)).sup' Finset.univ_nonempty
    (fun i => schmidtMass K (pvmConjugateColumnMatrix M i))

theorem column_schmidtMass_le_pvmMaxColumnSchmidtMass
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    [DecidableEq ιA] [Nonempty ιA] [Nonempty ιB]
    (K : ℕ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) :
    schmidtMass K (pvmConjugateColumnMatrix M i) ≤ pvmMaxColumnSchmidtMass K M :=
  by
    unfold pvmMaxColumnSchmidtMass
    exact Finset.le_sup'
      (fun j : ιA × ιB => schmidtMass K (pvmConjugateColumnMatrix M j))
      (Finset.mem_univ i)

theorem pvmMaxColumnSchmidtMass_nonneg
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    [DecidableEq ιA] [Nonempty ιA] [Nonempty ιB]
    (K : ℕ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    0 ≤ pvmMaxColumnSchmidtMass K M :=
  (schmidtMass_nonneg K (pvmConjugateColumnMatrix M (Classical.ofNonempty))).trans
    (column_schmidtMass_le_pvmMaxColumnSchmidtMass K M _)

namespace ClassicalCommunication.FiniteClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

/-- After all finite branch labels and both correct output labels are fixed,
the sum of projected Choi traces is at most one. -/
theorem sum_norm_sq_pvm_branch_references_le_one
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB) :
    ∑ b, ∑ i, ‖pvmBranchReferenceMatrix (P.branchKraus b) i‖ ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ b, ‖normalizedLabChoiMatrix (P.branchKraus b)‖ ^ 2 :=
      Finset.sum_le_sum fun b _ => sum_norm_sq_pvmBranchReferenceMatrix_le _
    _ = 1 := P.sum_norm_sq_normalizedLabChoiMatrix_branchKraus

/-- The unitary top-K bound with finite classical alphabets uncharged. -/
theorem scoreU_le_schmidtMass
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hK : P.HasQuantumFootprint K) :
    scoreU U P.operationalChannel ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  have hs : scoreU U P.operationalChannel = ∑ t,
      ‖frobInner (normalizedLabChoiMatrix U)
        (normalizedLabChoiMatrix (P.branchKraus t))‖ ^ 2 := by
    change unitaryScoreRealLinear U P.operationalChannel = _
    rw [P.operationalChannel_eq_sum_branchKraus, map_sum]
    simp only [unitaryScoreRealLinear_apply,
      scoreU_adConj_eq_norm_sq_normalizedLabChoiOverlap]
  rw [hs]
  calc
    _ ≤ ∑ t, ‖normalizedLabChoiMatrix (P.branchKraus t)‖ ^ 2 *
        schmidtMass K (normalizedLabChoiMatrix U) :=
      Finset.sum_le_sum fun t _ => norm_frobInner_sq_le_norm_sq_mul_schmidtMass _ _
        (P.rank_normalizedLabChoiMatrix_branchKraus_le t hK)
    _ = schmidtMass K (normalizedLabChoiMatrix U) := by
      rw [← Finset.sum_mul, P.sum_norm_sq_normalizedLabChoiMatrix_branchKraus, one_mul]

/-- A uniform upper bound on target-column top-K masses bounds the actual
two-sided PVM score. Duplicated output labels retain their total trace at most one. -/
theorem scorePVM_le_of_column_schmidtMass_le
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {t : ℝ}
    (hK : P.HasQuantumFootprint K) (ht : 0 ≤ t)
    (hmass : ∀ i, schmidtMass K (pvmConjugateColumnMatrix M i) ≤ t) :
    scorePVM M P.operationalChannel ≤ t := by
  have hs : scorePVM M P.operationalChannel = ∑ b, ∑ i,
      ‖frobInner (pvmConjugateColumnMatrix M i)
        (pvmBranchReferenceMatrix (P.branchKraus b) i)‖ ^ 2 := by
    change pvmScoreRealLinear M P.operationalChannel = _
    rw [P.operationalChannel_eq_sum_branchKraus, map_sum]
    simp only [pvmScoreRealLinear_apply,
      scorePVM_adConj_eq_sum_norm_sq_referenceOverlap]
  rw [hs]
  calc
    _ ≤ ∑ b, ∑ i, ‖pvmBranchReferenceMatrix (P.branchKraus b) i‖ ^ 2 * t := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro i _
      exact (norm_frobInner_sq_le_norm_sq_mul_schmidtMass _ _
        ((rank_pvmBranchReferenceMatrix_le _ i).trans
          (P.rank_normalizedLabChoiMatrix_branchKraus_le b hK))).trans
        (mul_le_mul_of_nonneg_left (hmass i) (sq_nonneg _))
    _ ≤ ∑ b, ‖normalizedLabChoiMatrix (P.branchKraus b)‖ ^ 2 * t := by
      apply Finset.sum_le_sum
      intro b _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_norm_sq_pvmBranchReferenceMatrix_le _) ht
    _ = t := by
      rw [← Finset.sum_mul, P.sum_norm_sq_normalizedLabChoiMatrix_branchKraus, one_mul]

/-- The literal maximum-column floor, with classical alphabet dimensions absent. -/
theorem scorePVM_le_max_column_schmidtMass
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ}
    (hK : P.HasQuantumFootprint K) :
    scorePVM M P.operationalChannel ≤ pvmMaxColumnSchmidtMass K M :=
  P.scorePVM_le_of_column_schmidtMass_le M hK
    (pvmMaxColumnSchmidtMass_nonneg K M)
    (column_schmidtMass_le_pvmMaxColumnSchmidtMass K M)

/-- Score accuracy forces the unitary target's top-K quantum mass. -/
theorem unitary_spectral_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (P.scoreU_le_schmidtMass U hK)

/-- Exact finite free-classical unitary implementation covers target Choi rank. -/
theorem unitary_exact_schmidt_rank_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K)
    (hscore : 1 ≤ scoreU U P.operationalChannel) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (P.scoreU_le_schmidtMass U hK))

/-- A target-only smallest-weight threshold forces full unitary Choi size. -/
theorem unitary_full_spectral_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    ht hε (P.unitary_spectral_floor U hK hscore)

/-- The flat SWAP Choi spectrum forces d²(1-epsilon) in quantum footprint. -/
theorem swap_quantumFootprint_floor
    (P : FiniteClassicalProtocol ιA ιA ρA ρB κA κB μA μB
      σA σB ηA ηB ιA ιA εA εB) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) P.operationalChannel) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K := by
  have h := P.unitary_spectral_floor (swapUnitary ιA) hK hscore
  rw [schmidtMass_swapUnitary_eq_min] at h
  have hd : 0 < (Fintype.card (ιA × ιA) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmul := (le_div_iff₀ hd).mp (h.trans (min_le_left _ _))
  simpa only [Fintype.card_prod, Nat.cast_mul, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hmul

/-- Maximally entangled PVM columns force d(1-epsilon), without charging labels. -/
theorem maximallyEntangledPVM_quantumFootprint_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA => ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (Fintype.card ιA : ℝ) * (1 - ε) ≤ K := by
  have hs := P.scorePVM_le_of_column_schmidtMass_le M hK
    (div_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg _))
    (fun i => schmidtMass_le_div_card_of_flat_gram _ (hflat i) K)
  have hd : 0 < (Fintype.card ιA : ℝ) := by exact_mod_cast Fintype.card_pos
  simpa only [mul_comm] using (le_div_iff₀ hd).mp (hscore.trans hs)

/-- Every column loses a smallest weight if K is below its full Schmidt size. -/
theorem pvm_full_spectral_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    Fintype.card ιA ≤ K := by
  classical
  by_contra hfull
  have hmass (i : ιA × ιB) : schmidtMass K (pvmConjugateColumnMatrix M i) ≤ 1 - t := by
    have h := topWeightMass_le_sum_sub_of_lt_card
      (schmidtWeights (pvmConjugateColumnMatrix M i)) (schmidtWeights_nonneg _)
      (ht i) (Nat.lt_of_not_ge hfull)
    simpa only [schmidtMass, sum_schmidtWeights, norm_conjugate_pvmColumnMatrix hM,
      one_pow] using h
  have hnonneg : 0 ≤ 1 - t :=
    (schmidtMass_nonneg K (pvmConjugateColumnMatrix M (Classical.ofNonempty))).trans
      (hmass _)
  have hs := P.scorePVM_le_of_column_schmidtMass_le M hK hnonneg hmass
  linarith

/-- Common-map finite mixing is selected by the actual affine unitary score. -/
theorem mixed_scoreU_le_schmidtMass
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hK : P.HasMixedQuantumFootprint m K) :
    scoreU U (P.mixedOperationalChannel m) ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (unitaryScoreRealLinear U) m hK
  exact hs.trans ((P.componentProtocol m k).scoreU_le_schmidtMass U hfoot)

/-- Common-map finite mixing retains the quantum-only maximum-column bound. -/
theorem mixed_scorePVM_le_max_column_schmidtMass
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ}
    (hK : P.HasMixedQuantumFootprint m K) :
    scorePVM M (P.mixedOperationalChannel m) ≤ pvmMaxColumnSchmidtMass K M := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact hs.trans ((P.componentProtocol m k).scorePVM_le_max_column_schmidtMass M hfoot)

/-- The same target-only unitary threshold applies to every component-capped mixture. -/
theorem mixed_unitary_full_spectral_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (hscore : 1 - ε ≤ scoreU U (P.mixedOperationalChannel m)) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    ht hε (hscore.trans (P.mixed_scoreU_le_schmidtMass m U hK))

/-- The finite-mixed PVM threshold preserves common instruments and both decoders. -/
theorem mixed_pvm_full_spectral_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M (P.mixedOperationalChannel m)) :
    Fintype.card ιA ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact (P.componentProtocol m k).pvm_full_spectral_floor M hM hfoot ht hε
    (hscore.trans hs)

/-- The SWAP floor retains the mixture's Schmidt-number cap and common maps. -/
theorem mixed_swap_quantumFootprint_floor
    (P : FiniteClassicalProtocol ιA ιA ρA ρB κA κB μA μB
      σA σB ηA ηB ιA ιA εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) (P.mixedOperationalChannel m)) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (unitaryScoreRealLinear (swapUnitary ιA)) m hK
  exact (P.componentProtocol m k).swap_quantumFootprint_floor hfoot (hscore.trans hs)

/-- Finite common-map mixtures retain the linear flat-column quantum floor. -/
theorem mixed_maximallyEntangledPVM_quantumFootprint_floor
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA => ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K : ℕ} {ε : ℝ} (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scorePVM M (P.mixedOperationalChannel m)) :
    (Fintype.card ιA : ℝ) * (1 - ε) ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact (P.componentProtocol m k).maximallyEntangledPVM_quantumFootprint_floor
    M hflat hfoot (hscore.trans hs)

/-- The original finite operational channel's diamond accuracy gives its
normalized unitary score before any component selection. -/
theorem scoreU_ge_of_diamondError_le
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {ε : ℝ}
    (hU : IsIsometry U)
    (herror : diamondError P.operationalChannel (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U P.operationalChannel := by
  have hs := P.coherentProtocol.scoreU_ge_of_diamondError_le (e := ε) hU
    (by simpa only [P.coherentProtocol_operationalChannel] using herror)
  simpa only [P.coherentProtocol_operationalChannel] using hs

/-- Joint total variation tests both duplicated correct labels and supplies
the actual PVM score with the source's linear error normalization. -/
theorem scorePVM_ge_of_pvmTVError_le
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {ε : ℝ}
    (hM : IsIsometry M) (herror : pvmTVError M P.operationalChannel ≤ ε) :
    1 - ε ≤ scorePVM M P.operationalChannel := by
  have hs := P.coherentProtocol.one_sub_scorePVM_le_pvmTVError hM
  rw [P.coherentProtocol_operationalChannel] at hs
  linarith

/-- Diamond accuracy of the honest common-map mixture gives its original score. -/
theorem mixed_scoreU_ge_of_diamondError_le
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {ε : ℝ}
    (hU : IsIsometry U)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U (P.mixedOperationalChannel m) := by
  have hs := m.scoreU_ge_of_diamondError_le
    P.coherentProtocol.encA_isometry P.coherentProtocol.encB_isometry
    P.coherentProtocol.decA_isometry P.coherentProtocol.decB_isometry
    (e := ε) hU
    (by simpa only [P.mixedOperationalChannel_eq_coherentMixedChannel] using herror)
  simpa only [← P.mixedOperationalChannel_eq_coherentMixedChannel] using hs

/-- The original mixed joint-TV error is converted to score before selecting
a resource component; the selected component's TV error is never inferred. -/
theorem mixed_scorePVM_ge_of_pvmTVError_le
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {ε : ℝ}
    (hM : IsIsometry M)
    (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) :
    1 - ε ≤ scorePVM M (P.mixedOperationalChannel m) := by
  have hs := m.one_sub_scorePVM_le_pvmTVError
    P.coherentProtocol.encA_isometry P.coherentProtocol.encB_isometry
    P.coherentProtocol.decA_isometry P.coherentProtocol.decB_isometry hM
  rw [← P.mixedOperationalChannel_eq_coherentMixedChannel] at hs
  linarith

/-- The unitary spectral floor accepts the actual original diamond error. -/
theorem unitary_spectral_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K)
    (herror : diamondError P.operationalChannel (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  P.unitary_spectral_floor U hK (P.scoreU_ge_of_diamondError_le U hU herror)

/-- The PVM maximum-column floor accepts joint-TV accuracy of the original channel. -/
theorem pvm_spectral_floor_of_pvmTVError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hM : IsIsometry M) (hK : P.HasQuantumFootprint K)
    (herror : pvmTVError M P.operationalChannel ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  (P.scorePVM_ge_of_pvmTVError_le M hM herror).trans
    (P.scorePVM_le_max_column_schmidtMass M hK)

/-- The mixed unitary floor retains the mixture's quantum-only footprint. -/
theorem mixed_unitary_spectral_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hU : IsIsometry U) (hK : P.HasMixedQuantumFootprint m K)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  (P.mixed_scoreU_ge_of_diamondError_le m U hU herror).trans
    (P.mixed_scoreU_le_schmidtMass m U hK)

/-- The mixed PVM floor uses the original common-map channel's joint-TV error. -/
theorem mixed_pvm_spectral_floor_of_pvmTVError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hM : IsIsometry M) (hK : P.HasMixedQuantumFootprint m K)
    (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  (P.mixed_scorePVM_ge_of_pvmTVError_le m M hM herror).trans
    (P.mixed_scorePVM_le_max_column_schmidtMass m M hK)

/-- SWAP diamond accuracy requires the linear d² quantum footprint floor. -/
theorem swap_quantumFootprint_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιA ρA ρB κA κB μA μB
      σA σB ηA ηB ιA ιA εA εB) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K)
    (herror : diamondError P.operationalChannel (adConj (swapUnitary ιA)) ≤ ε) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K :=
  P.swap_quantumFootprint_floor hK
    (P.scoreU_ge_of_diamondError_le _ (isIsometry_swapUnitary ιA) herror)

/-- The SWAP diamond floor for the original honest common-map finite mixture. -/
theorem mixed_swap_quantumFootprint_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιA ρA ρB κA κB μA μB
      σA σB ηA ηB ιA ιA εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj (swapUnitary ιA)) ≤ ε) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K :=
  P.mixed_swap_quantumFootprint_floor m hK
    (P.mixed_scoreU_ge_of_diamondError_le m _ (isIsometry_swapUnitary ιA) herror)

/-- A positive target-only Schmidt-weight threshold applies to original
diamond accuracy for arbitrary original finite registers. -/
theorem unitary_full_spectral_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (herror : diamondError P.operationalChannel (adConj U) ≤ ε) :
    Fintype.card (ιA' × ιA) ≤ K :=
  P.unitary_full_spectral_floor U hU hK ht hε (P.scoreU_ge_of_diamondError_le U hU herror)

/-- The full-column quantum floor uses the original PVM joint-TV hypothesis. -/
theorem pvm_full_spectral_floor_of_pvmTVError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (herror : pvmTVError M P.operationalChannel ≤ ε) :
    Fintype.card ιA ≤ K :=
  P.pvm_full_spectral_floor M hM hK ht hε (P.scorePVM_ge_of_pvmTVError_le M hM herror)

/-- Mixed full-rank unitary thresholds retain the decomposition's quantum cap. -/
theorem mixed_unitary_full_spectral_floor_of_diamondError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) :
    Fintype.card (ιA' × ιA) ≤ K :=
  P.mixed_unitary_full_spectral_floor m U hU hK ht hε
    (P.mixed_scoreU_ge_of_diamondError_le m U hU herror)

/-- Mixed full-column PVM thresholds apply to the original common-map joint-TV error. -/
theorem mixed_pvm_full_spectral_floor_of_pvmTVError
    (P : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB (ιA × ιB) (ιA × ιB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) :
    Fintype.card ιA ≤ K :=
  P.mixed_pvm_full_spectral_floor m M hM hK ht hε
    (P.mixed_scorePVM_ge_of_pvmTVError_le m M hM herror)

variable {d : ℕ} [NeZero d]

/-- The actual complete generalized Bell basis gives d(1-epsilon) in every
positive dimension, without a separate flat-spectrum hypothesis. -/
theorem generalizedBellPVM_quantumFootprint_floor
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) P.operationalChannel) :
    (d : ℝ) * (1 - ε) ≤ K := by
  simpa only [Fintype.card_fin] using P.maximallyEntangledPVM_quantumFootprint_floor
    (generalizedBellFinMatrix d) (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d)
    hK hscore

/-- Common-map finite-mixed implementation of the concrete Bell basis has
the same linear quantum floor. -/
theorem mixed_generalizedBellPVM_quantumFootprint_floor
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (P.mixedOperationalChannel m)) :
    (d : ℝ) * (1 - ε) ≤ K := by
  simpa only [Fintype.card_fin] using P.mixed_maximallyEntangledPVM_quantumFootprint_floor
    m (generalizedBellFinMatrix d) (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d)
    hK hscore

/-- The concrete Bell quantum floor from the actual original joint-TV error. -/
theorem generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K)
    (herror : pvmTVError (generalizedBellFinMatrix d) P.operationalChannel ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  P.generalizedBellPVM_quantumFootprint_floor hK
    (P.scorePVM_ge_of_pvmTVError_le _ (isIsometry_generalizedBellFinMatrix d) herror)

/-- The concrete Bell joint-TV floor under a common-map Schmidt-number cap. -/
theorem mixed_generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K)
    (herror : pvmTVError (generalizedBellFinMatrix d) (P.mixedOperationalChannel m) ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  P.mixed_generalizedBellPVM_quantumFootprint_floor m hK
    (P.mixed_scorePVM_ge_of_pvmTVError_le m _ (isIsometry_generalizedBellFinMatrix d) herror)

end ClassicalCommunication.FiniteClassicalProtocol

open MeasureTheory ClassicalCommunication

/-- Almost every fixed target has a positive spectral threshold before the
quantum budget and error are quantified, for all four finite score classes. -/
theorem ae_finite_classical_full_spectral_threshold (d : ℕ) [NeZero d] :
    ∀ᵐ (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (K : ℕ) (ε : ℝ), ε < η →
        (T ∈ finitePureScoreReachable d K ε → d ^ 2 ≤ K) ∧
        (T ∈ finiteMixedScoreReachable d K ε → d ^ 2 ≤ K) ∧
        (T ∈ finitePurePVMScoreReachable d K ε → d ≤ K) ∧
        (T ∈ finiteMixedPVMScoreReachable d K ε → d ≤ K) := by
  filter_upwards [ae_unitary_pos_schmidtWeight_lower_bound d,
    ae_pvm_pos_uniform_schmidtWeight_lower_bound d] with T hU hM
  obtain ⟨tU, htU, hwU⟩ := hU
  obtain ⟨tM, htM, hwM⟩ := hM
  let η := min 1 (min tU tM)
  refine ⟨η, lt_min (by norm_num) (lt_min htU htM), min_le_left _ _, ?_⟩
  intro K ε hε
  have hεU : ε < tU := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε < tM := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hT : IsIsometry (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp T.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨s, P, hK, hs⟩
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      P.unitary_full_spectral_floor (ιA := Fin d) (ιB := Fin d)
        (ιA' := Fin d) (ιB' := Fin d)
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
  · rintro ⟨s, n, m, P, hK, hs⟩
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      P.mixed_unitary_full_spectral_floor (ιA := Fin d) (ιB := Fin d)
        (ιA' := Fin d) (ιB' := Fin d) m
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
  · rintro ⟨s, P, hK, hs⟩
    simpa only [Fintype.card_fin] using
      P.pvm_full_spectral_floor (ιA := Fin d) (ιB := Fin d)
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs
  · rintro ⟨s, n, m, P, hK, hs⟩
    simpa only [Fintype.card_fin] using
      P.mixed_pvm_full_spectral_floor (ιA := Fin d) (ιB := Fin d) m
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs

end NLQCLean
