import NLQCLean.Approx.SharpFreezing
import NLQCLean.Bounds.SwapFloor

/-!
# Spectral footprint floors for unitary targets

The laboratory Choi coefficients use inverse square-root logical-input
normalization. Their squared Schmidt weights therefore sum to one. The
spectral floor uses the saturating finite-support definition of Schmidt mass.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius ComplexOrder

/-- Once the allowed support covers the index type, top mass is total mass. -/
theorem topWeightMass_eq_sum_of_card_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {K : ℕ} (hK : Fintype.card ι ≤ K) :
    topWeightMass K w = ∑ i, w i := by
  apply le_antisymm (topWeightMass_le_sum K w hw)
  exact sum_le_topWeightMass w (by simpa using hK)

/-- A positive flat spectrum saturates at its full finite cardinality. -/
theorem topWeightMass_const_eq_min {ι : Type*} [Fintype ι]
    (K : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    topWeightMass K (fun _ : ι ↦ b) = (min K (Fintype.card ι) : ℕ) * b := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (show min K (Fintype.card ι) ≤ (Finset.univ : Finset ι).card by simp)
  apply le_antisymm
  · by_cases hK : K ≤ Fintype.card ι
    · simpa [Nat.min_eq_left hK] using
        topWeightMass_le_mul K (fun _ : ι ↦ b) hb (fun _ ↦ le_rfl)
    · have htotal := topWeightMass_le_sum K (fun _ : ι ↦ b) (fun _ ↦ hb)
      simpa [Nat.min_eq_right (Nat.le_of_not_ge hK)] using htotal
  · have hallowed : s.card ≤ K := hcard.trans_le (Nat.min_le_left _ _)
    simpa [hcard] using sum_le_topWeightMass (fun _ : ι ↦ b) hallowed

/-- The normalized laboratory Choi convention has probability Schmidt mass. -/
theorem sum_schmidtWeights_normalizedLabChoiMatrix {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq a] [DecidableEq i] [DecidableEq j] [Nonempty i] [Nonempty j]
    {U : Matrix (a × b) (i × j) ℂ} (hU : IsIsometry U) :
    ∑ x, schmidtWeights (normalizedLabChoiMatrix U) x = 1 := by
  rw [sum_schmidtWeights, norm_normalizedLabChoiMatrix_of_isometry hU, one_pow]

/-- Choi normalization preserves the unnormalized operator-Schmidt rank. -/
theorem rank_normalizedLabChoiMatrix_eq {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Nonempty i] [Nonempty j]
    (U : Matrix (a × b) (i × j) ℂ) :
    (normalizedLabChoiMatrix U).rank = (labChoiMatrix U).rank := by
  have hD : 0 < (Fintype.card (i × j) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (((Real.sqrt (Fintype.card (i × j) : ℝ))⁻¹ : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (Real.sqrt_pos.mpr hD).ne'
  exact Matrix.rank_smul_of_mem_nonZeroDivisors (labChoiMatrix U)
    (mem_nonZeroDivisors_of_ne_zero hc)

/-- Retaining the full norm of a unit vector requires its full Schmidt rank. -/
theorem rank_le_of_one_le_schmidtMass {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (hM : ‖M‖ = 1) {K : ℕ}
    (hmass : 1 ≤ schmidtMass K M) : M.rank ≤ K := by
  have hupper : schmidtMass K M ≤ 1 := by
    have h := topWeightMass_le_sum K (schmidtWeights M) (schmidtWeights_nonneg M)
    simpa only [sum_schmidtWeights, hM, one_pow, schmidtMass] using h
  have heq : schmidtMass K M = 1 := le_antisymm hupper hmass
  obtain ⟨W, hW, hrank, hinner⟩ := exists_schmidt_truncation M K (by linarith)
  have hdist : ‖M - W‖ ^ 2 = 0 := by
    rw [frobNorm_sub_sq, hM, hW, hinner, heq]
    norm_num
  have hMW : M = W := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdist))
  simpa only [hMW] using hrank

/-- Missing any positive spectral weight loses at least its lower bound. -/
theorem topWeightMass_le_sum_sub_of_lt_card {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {K : ℕ} {δ : ℝ}
    (hδ : ∀ i, δ ≤ w i) (hK : K < Fintype.card ι) :
    topWeightMass K w ≤ (∑ i, w i) - δ := by
  classical
  apply topWeightMass_le
  intro s hs
  obtain ⟨j, hj, hjs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < (Finset.univ : Finset ι).card by simpa using hs.trans_lt hK)
  have hsub : s ⊆ (Finset.univ : Finset ι).erase j := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨by intro hij; subst i; exact hjs hi, Finset.mem_univ _⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦ hw i)
  have herase := Finset.sum_erase_add (Finset.univ : Finset ι) w hj
  linarith [hδ j]

/-- Positive weights and error below every weight force full spectral size. -/
theorem card_le_of_spectral_threshold {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (hM : ‖M‖ = 1)
    {K : ℕ} {ε δ : ℝ} (hδ : ∀ i, δ ≤ schmidtWeights M i)
    (hε : ε < δ) (hmass : 1 - ε ≤ schmidtMass K M) : Fintype.card m ≤ K := by
  by_contra hK
  have hupper := topWeightMass_le_sum_sub_of_lt_card (schmidtWeights M)
    (schmidtWeights_nonneg M) hδ (Nat.lt_of_not_ge hK)
  rw [sum_schmidtWeights, hM, one_pow] at hupper
  change schmidtMass K M ≤ 1 - δ at hupper
  linarith

/-- Full left Schmidt rank gives a positive lower bound on every weight. -/
theorem exists_pos_schmidtWeight_lower_bound_of_full_rank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [Nonempty m]
    (M : Matrix m n ℂ) (hM : M.rank = Fintype.card m) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, t ≤ schmidtWeights M i := by
  classical
  have hcard : Fintype.card {i // schmidtWeights M i ≠ 0} = Fintype.card m := by
    obtain ⟨V, _, hV', hgram⟩ := exists_schmidt_coordinates M
    have hVV : V * Vᴴ = 1 := by
      simpa only [IsIsometry, Matrix.conjTranspose_conjTranspose] using hV'
    have hback : V * (Vᴴ * M) = M := by
      rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
    have hrank : (Vᴴ * M).rank = M.rank := by
      apply le_antisymm (Matrix.rank_mul_le_right _ _)
      calc
        M.rank = (V * (Vᴴ * M)).rank := congrArg Matrix.rank hback.symm
        _ ≤ (Vᴴ * M).rank := Matrix.rank_mul_le_right _ _
    have hdiag : (Matrix.diagonal (fun i ↦ (schmidtWeights M i : ℂ))).rank =
        Fintype.card m := by
      rw [← hgram, Matrix.rank_self_mul_conjTranspose, hrank, hM]
    simpa only [Matrix.rank_diagonal, Fintype.card_subtype, Complex.ofReal_ne_zero] using hdiag
  have hpos (i : m) : 0 < schmidtWeights M i := by
    apply lt_of_le_of_ne (schmidtWeights_nonneg M i)
    intro hi
    have hc := Fintype.card_subtype_lt (p := fun j ↦ schmidtWeights M j ≠ 0)
      (x := i) (by simp [hi.symm])
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image (Finset.univ : Finset m)
    (schmidtWeights M) Finset.univ_nonempty
  exact ⟨schmidtWeights M i, hpos i, fun j ↦ hi j (Finset.mem_univ j)⟩

/-- Entrywise conjugation cannot increase matrix rank. -/
theorem rank_map_star_le {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : (M.map star).rank ≤ M.rank := by
  classical
  obtain ⟨J, B, _, hfac⟩ := exists_isometry_rank_factorization M
  have hconj : M.map star = J.map star * B.map star := by
    ext i j
    change star (M i j) = ∑ k, star (J i k) * star (B k j)
    have hij := congrArg (fun X : Matrix m n ℂ ↦ X i j) hfac
    rw [hij]
    simp only [Matrix.mul_apply, star_sum, star_mul, mul_comm]
  rw [hconj]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (J.map star))

/-- Entrywise double conjugation is the original coefficient matrix. -/
theorem map_star_star_matrix {m n : Type*} (M : Matrix m n ℂ) :
    (M.map star).map star = M := Matrix.map_involutive star_involutive M

/-- Entrywise conjugation preserves Schmidt rank. -/
theorem rank_map_star {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : (M.map star).rank = M.rank := by
  apply le_antisymm (rank_map_star_le M)
  simpa only [map_star_star_matrix] using
    rank_map_star_le (M.map star)

/-- Entrywise conjugation conjugates the Frobenius overlap. -/
theorem frobInner_map_star {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : frobInner (A.map star) (B.map star) = star (frobInner A B) := by
  simp only [frobInner, Matrix.map_apply, star_star, star_sum, star_mul']

private theorem schmidtMass_map_star_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (K : ℕ) :
    schmidtMass K (M.map star) ≤ schmidtMass K M := by
  by_cases hpos : 0 < schmidtMass K (M.map star)
  · obtain ⟨W, hW, hrank, hinner⟩ := exists_schmidt_truncation (M.map star) K hpos
    have hnorm : ‖W.map star‖ = 1 :=
      (Matrix.frobenius_norm_map_eq W star norm_star).trans hW
    have hinner' : frobInner (W.map star) M =
        (Real.sqrt (schmidtMass K (M.map star)) : ℂ) := by
      have h := frobInner_map_star W (M.map star)
      rw [map_star_star_matrix, hinner] at h
      simpa only [Complex.star_def, Complex.conj_ofReal] using h
    have h := norm_frobInner_sq_le_schmidtMass M (W.map star) hnorm
      ((rank_map_star_le W).trans hrank)
    rwa [hinner', norm_complex_sqrt_sq hpos.le] at h
  · exact (le_of_not_gt hpos).trans (schmidtMass_nonneg K M)

/-- Complex conjugation does not change target Schmidt mass. -/
theorem schmidtMass_map_star {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (K : ℕ) :
    schmidtMass K (M.map star) = schmidtMass K M := by
  apply le_antisymm (schmidtMass_map_star_le M K)
  simpa only [map_star_star_matrix] using
    schmidtMass_map_star_le (M.map star) K

/-- The SWAP mass includes saturation when K exceeds the full rank. -/
theorem schmidtMass_swapUnitary_eq_min (ι : Type*) [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (K : ℕ) :
    schmidtMass K (normalizedLabChoiMatrix (swapUnitary ι)) =
      min ((K : ℝ) / Fintype.card (ι × ι)) 1 := by
  have hcoord := schmidtMass_eq_topWeightMass_of_coordinates
    (normalizedLabChoiMatrix (swapUnitary ι)) (1 : Matrix (ι × ι) (ι × ι) ℂ)
    (fun _ : ι × ι ↦ (Fintype.card (ι × ι) : ℝ)⁻¹)
    isIsometry_one (by simpa using (isIsometry_one (n := ι × ι) (𝕜 := ℂ)))
    (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simpa using normalizedLabChoiMatrix_swapUnitary_gram ι) K
  rw [hcoord, topWeightMass_const_eq_min K (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hD : 0 < (Fintype.card (ι × ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hK : K ≤ Fintype.card (ι × ι)
  · have hKD : (K : ℝ) / Fintype.card (ι × ι) ≤ 1 :=
      (div_le_one hD).mpr (by exact_mod_cast hK)
    rw [Nat.min_eq_left hK, min_eq_left hKD]
    exact (div_eq_mul_inv _ _).symm
  · have hDK : Fintype.card (ι × ι) ≤ K := Nat.le_of_not_ge hK
    have hKD : 1 ≤ (K : ℝ) / Fintype.card (ι × ι) :=
      (one_le_div hD).mpr (by exact_mod_cast hDK)
    rw [Nat.min_eq_right hDK, min_eq_right hKD]
    exact mul_inv_cancel₀ hD.ne'

section Protocol

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

/-- The spectral floor in the original charged pure protocol model. -/
theorem PureProtocol.unitary_spectral_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (P.scoreU_le_schmidtMass U hU hK)

/-- Exact score one requires the operator-Schmidt rank of normalized Choi U. -/
theorem PureProtocol.unitary_exact_schmidt_rank_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hscore : 1 ≤ scoreU U P.operationalChannel) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (P.scoreU_le_schmidtMass U hU hK))

/-- A lower bound on every Choi Schmidt weight gives a deterministic threshold. -/
theorem PureProtocol.unitary_full_spectral_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε δ : ℝ}
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hδ : ∀ i, δ ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < δ) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    hδ hε (P.unitary_spectral_floor U hU hK hscore)

/-- Score affinity selects a pure component, retaining the common local maps
and the Schmidt-number/message footprint of a finite mixed resource. -/
theorem MixedResource.scoreU_le_schmidtMass {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U)
    {K R : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K) :
    scoreU U (m.mixedChannel VA VB DA DB) ≤
      schmidtMass K (normalizedLabChoiMatrix U) := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB U
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact hk.trans (P.scoreU_le_schmidtMass U hU hPK)

/-- Unitary spectral floor for a finite mixed resource and common local maps. -/
theorem MixedResource.unitary_spectral_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hscore : 1 - ε ≤ scoreU U (m.mixedChannel VA VB DA DB)) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (m.scoreU_le_schmidtMass VA VB DA DB hVA hVB hDA hDB U hU hR hK)

/-- Exact score one also forces full Choi Schmidt rank for finite mixtures. -/
theorem MixedResource.unitary_exact_schmidt_rank_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U)
    {K R : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hscore : 1 ≤ scoreU U (m.mixedChannel VA VB DA DB)) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (m.scoreU_le_schmidtMass VA VB DA DB hVA hVB hDA hDB U hU hR hK))

/-- Finite mixed spectral threshold with all original register universes. -/
theorem MixedResource.unitary_full_spectral_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U)
    {K R : ℕ} {ε δ : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hδ : ∀ i, δ ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < δ) (hscore : 1 - ε ≤ scoreU U (m.mixedChannel VA VB DA DB)) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    hδ hε (m.unitary_spectral_floor VA VB DA DB hVA hVB hDA hDB U hU hR hK hscore)

end Protocol
end NLQCLean
