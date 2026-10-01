import NLQCLean.Approx.PVMChoiProjection
import NLQCLean.Approx.PVMBlockTruncation
import NLQCLean.Approx.SharpFreezing
import NLQCLean.LinearAlgebra.FlaggedSchmidtWeights

/-!
# Flagged freezing with one total Schmidt-rank budget

Finite product-weight selection is followed by independent
normalization of its environment blocks. At most one extra rank per label is
charged for zero retained blocks. The final application uses the actual
projected Choi spectrum and the charged protocol footprint.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

/-- Grouping a single top-K product spectrum and normalizing each selected
block yields unit matrices with one total rank bound K+card(labels). -/
theorem exists_unit_blocks_of_grouped_spectrum
    {δ m n a b : Type*} [Fintype δ] [Fintype m] [Fintype n]
    [Fintype a] [Fintype b] [DecidableEq m] [DecidableEq a]
    [Nonempty m] [Nonempty n]
    (A : δ → Matrix m n ℂ) (B : δ → Matrix a b ℂ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ∀ i, ‖B i‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    ∃ U : δ → Matrix m n ℂ, (∀ i, ‖U i‖ = 1) ∧
      (∑ i, (U i).rank) ≤ K + Fintype.card δ ∧
      topWeightMass K (fun p : δ × (m × a) =>
        t * (schmidtWeights (A p.1) p.2.1 * schmidtWeights (B p.1) p.2.2)) ≤
          t * ∑ i, (frobInner (U i) (A i)).re := by
  classical
  obtain ⟨s, hscard, hmass⟩ := exists_grouped_topWeightMass_fibers K
    (fun i c => t * schmidtWeights (A i) c)
    (fun i c => schmidtWeights (B i) c)
    (fun i c => mul_nonneg ht (schmidtWeights_nonneg _ _))
    (fun i c => schmidtWeights_nonneg _ _)
    (fun i => by rw [sum_schmidtWeights, hB i, one_pow])
  choose V hV _ hgram using fun i => exists_schmidt_coordinates (A i)
  choose U hU hUrank _ hinner hupper using fun i =>
    exists_normalized_spectral_support (A i) (V i) (s i) (hA i) (hV i) (hgram i)
  refine ⟨U, hU, ?_, ?_⟩
  · calc
      ∑ i, (U i).rank ≤ ∑ i, ((s i).card + 1) :=
        Finset.sum_le_sum fun i _ => hUrank i
      _ = (∑ i, (s i).card) + Fintype.card δ := by simp [Finset.sum_add_distrib]
      _ ≤ K + Fintype.card δ := Nat.add_le_add_right hscard _
  · have hle (i : δ) : (∑ c ∈ s i, schmidtWeights (A i) c) ≤
        (frobInner (U i) (A i)).re := by
      have hnonneg : 0 ≤ ∑ c ∈ s i, schmidtWeights (A i) c :=
        Finset.sum_nonneg fun c _ => schmidtWeights_nonneg _ _
      have hsqrt := Real.sq_sqrt hnonneg
      have hroot0 := Real.sqrt_nonneg (∑ c ∈ s i, schmidtWeights (A i) c)
      have hroot1 := (hinner i).trans (hupper i)
      nlinarith [hinner i, mul_nonneg hroot0 (sub_nonneg.mpr hroot1)]
    calc
      _ ≤ ∑ i, ∑ c ∈ s i, t * schmidtWeights (A i) c := by
        simpa only [mul_assoc] using hmass
      _ = t * ∑ i, ∑ c ∈ s i, schmidtWeights (A i) c := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i) ht

section Actual
variable {ιA ιB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

omit [DecidableEq εB] in
/-- PVM freezing with a total environment Schmidt-rank bound. -/
theorem exists_pvm_frozen_of_choi_rank
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    {F : Matrix (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (ιA × ιB) ℂ}
    (hM : IsIsometry M) (hF : IsIsometry F)
    {K : ℕ} (hK : (tensorChoiMatrix F).rank ≤ K)
    {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hq : 1 - ε ≤ scorePVM M (channelOf
      (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id))) :
    ∃ u : (ιA × ιB) → εA × εB → ℂ, (∀ i, IsUnitVector (u i)) ∧
      (∑ i, schmidtRank (u i)) ≤ K + Fintype.card (ιA × ιB) ∧
      ‖F - flagIsometry u * Mᴴ‖ / Real.sqrt (Fintype.card (ιA × ιB) : ℝ) ≤
        2 * Real.sqrt ε := by
  classical
  have hout : Nonempty (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) := by
    rcases isEmpty_or_nonempty (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) with he | hn
    · let := he
      let i : ιA × ιB := Classical.choice inferInstance
      have hi := congrArg (fun X : Matrix (ιA × ιB) (ιA × ιB) ℂ => X i i) hF
      simp [Matrix.mul_apply] at hi
    · exact hn
  obtain ⟨⟨⟨_, eA⟩, ⟨_, eB⟩⟩⟩ := hout
  let : Nonempty εA := ⟨eA⟩
  let : Nonempty εB := ⟨eB⟩
  let A : (ιA × ιB) → Matrix εA εB ℂ := fun i => resourceMatrix (pvmEnvironment M F i)
  let B : (ιA × ιB) → Matrix ιA ιB ℂ := pvmConjugateColumnMatrix M
  let t : ℝ := (Fintype.card (ιA × ιB) : ℝ)⁻¹
  obtain ⟨U, hU, hUr, hmass⟩ := exists_unit_blocks_of_grouped_spectrum A B
    (fun i => norm_resourceMatrix_pvmEnvironment_le_one hF hM i)
    (fun i => norm_conjugate_pvmColumnMatrix hM i) t (inv_nonneg.mpr (Nat.cast_nonneg _)) K
  let u : (ιA × ιB) → εA × εB → ℂ := fun i e => U i e.1 e.2
  have hu (i : ιA × ιB) : IsUnitVector (u i) :=
    (isUnitVector_iff_norm_resourceMatrix (u i)).mpr (hU i)
  have hM' : IsIsometry Mᴴ := by
    rw [IsIsometry, Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hM
  have hCu : IsIsometry (flagIsometry u * Mᴴ) :=
    (isIsometry_flagIsometry u hu).mul hM'
  let q : ℝ := scorePVM M (channelOf
    (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id))
  have hspec : schmidtMass K (tensorChoiMatrix (pvmProjectedDilation M F)) ≤
      t * ∑ i, (frobInner (U i) (A i)).re := by
    rw [pvmProjectedDilation, schmidtMass_tensorChoiMatrix_flag_mul_adjoint]
    rw [← topWeightMass_reindex (Equiv.prodComm (εA × ιA) (ιA × ιB)) K] at hmass
    exact hmass
  have hinner : (frobInner (tensorChoiMatrix (flagIsometry u * Mᴴ))
      (tensorChoiMatrix F)).re = t * ∑ i, (frobInner (U i) (A i)).re := by
    rw [frobInner_tensorChoiMatrix, frobInner_flag_mul_adjoint]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, Complex.re_sum]
    simp only [t, frobInner, A, u, resourceMatrix_apply, Fintype.sum_prod_type, Complex.re_sum]
  have hqinner : q ^ 2 ≤ (frobInner (tensorChoiMatrix (flagIsometry u * Mᴴ))
      (tensorChoiMatrix F)).re := by
    rw [hinner]
    exact (scorePVM_sq_le_schmidtMass_pvmProjected M hF hK).trans hspec
  have hres : ‖tensorChoiMatrix F - tensorChoiMatrix (flagIsometry u * Mᴴ)‖ ^ 2 ≤
      4 * ε := by
    rw [frobNorm_sub_sq, norm_tensorChoiMatrix_of_isometry hF,
      norm_tensorChoiMatrix_of_isometry hCu]
    have hq0 : 0 ≤ q := scorePVM_channelOf_regrouped_nonneg F M
    change 1 - ε ≤ q at hq
    have hs : (1 - ε) ^ 2 ≤ q ^ 2 :=
      (sq_le_sq₀ (sub_nonneg.mpr hε.2) hq0).mpr hq
    nlinarith [sq_nonneg ε]
  refine ⟨u, hu, hUr, ?_⟩
  rw [← norm_tensorChoiMatrix, tensorChoiMatrix_sub]
  nlinarith [Real.sq_sqrt hε.1, Real.sqrt_nonneg ε,
    norm_nonneg (tensorChoiMatrix F - tensorChoiMatrix (flagIsometry u * Mᴴ))]

end Actual

section Protocol
variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- PVM-F for the original protocol: all message dimensions are charged and
all original private/environment dimensions remain arbitrary finite types. -/
theorem PureProtocol.exists_pvm_frozen
    [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hq : 1 - ε ≤ scorePVM M P.operationalChannel) :
    ∃ u : (ιA × ιB) → εA × εB → ℂ, (∀ i, IsUnitVector (u i)) ∧
      (∑ i, schmidtRank (u i)) ≤ K + Fintype.card (ιA × ιB) ∧
      ‖P.globalIsometry - flagIsometry u * Mᴴ‖ /
        Real.sqrt (Fintype.card (ιA × ιB) : ℝ) ≤ 2 * Real.sqrt ε := by
  apply exists_pvm_frozen_of_choi_rank hM P.isIsometry_globalIsometry _ hε hq
  rw [rank_tensorChoiMatrix]
  exact P.rank_normalizedLabChoiMatrix_le_of_hasFootprint hK

end Protocol
end NLQCLean
