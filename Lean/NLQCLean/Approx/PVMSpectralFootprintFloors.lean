import NLQCLean.Approx.PVMRankFloor
import NLQCLean.Approx.SpectralFootprintFloors
import NLQCLean.LinearAlgebra.FlaggedSchmidtWeights

/-!
# Target spectral allocation for ordered rank-one PVMs

A single selected support of the flagged product spectrum is grouped by
target Schmidt coordinates. Environment weight has total mass at most one
in each block. The resulting target allocations share one charged rank budget.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- The ordinary target-vector coefficient matrix across the laboratory cut. -/
def pvmColumnCoefficientMatrix {ιA ιB : Type*}
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) : Matrix ιA ιB ℂ :=
  fun a b ↦ M (a, b) i

/-- The conjugate matrix arising in Choi projection has the target's mass. -/
theorem schmidtMass_pvmConjugateColumnMatrix_eq {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA]
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) (K : ℕ) :
    schmidtMass K (pvmConjugateColumnMatrix M i) =
      schmidtMass K (pvmColumnCoefficientMatrix M i) :=
  schmidtMass_map_star (pvmColumnCoefficientMatrix M i) K

/-- The target column and its conjugate have the same Schmidt rank. -/
theorem rank_pvmConjugateColumnMatrix_eq {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) :
    (pvmConjugateColumnMatrix M i).rank = (pvmColumnCoefficientMatrix M i).rank :=
  rank_map_star (pvmColumnCoefficientMatrix M i)

/-- Finitely many full-rank blocks have one positive target-dependent weight
lower bound. The bound is not uniform over target families. -/
theorem exists_pos_uniform_schmidtWeight_lower_bound_of_full_rank
    {δ a b : Type*} [Fintype δ] [Fintype a] [Fintype b]
    [DecidableEq a] [Nonempty δ] [Nonempty a]
    (B : δ → Matrix a b ℂ) (hB : ∀ i, (B i).rank = Fintype.card a) :
    ∃ t : ℝ, 0 < t ∧ ∀ i j, t ≤ schmidtWeights (B i) j := by
  classical
  have hpos (i : δ) (j : a) : 0 < schmidtWeights (B i) j := by
    obtain ⟨t, ht, hweights⟩ := exists_pos_schmidtWeight_lower_bound_of_full_rank (B i) (hB i)
    exact ht.trans_le (hweights j)
  obtain ⟨ij, _, hij⟩ := Finset.exists_min_image (Finset.univ : Finset (δ × a))
    (fun ij ↦ schmidtWeights (B ij.1) ij.2) Finset.univ_nonempty
  exact ⟨schmidtWeights (B ij.1) ij.2, hpos ij.1 ij.2,
    fun i j ↦ hij (i, j) (Finset.mem_univ _)⟩

/-- Group product-weight support by target coordinates when the environment
weights have blockwise total mass at most one. -/
theorem exists_target_topWeightMass_support
    {δ a e : Type*} [Fintype δ] [Fintype a] [Fintype e]
    (K : ℕ) (lam : δ → a → ℝ) (c : δ → e → ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j) (hc : ∀ i j, 0 ≤ c i j)
    (hc_sum : ∀ i, ∑ j, c i j ≤ 1) :
    ∃ S : Finset (δ × a), S.card ≤ K ∧
      topWeightMass K (fun p : δ × (a × e) ↦ lam p.1 p.2.1 * c p.1 p.2.2) ≤
        ∑ p ∈ S, lam p.1 p.2 := by
  classical
  let w : δ × (a × e) → ℝ := fun p ↦ lam p.1 p.2.1 * c p.1 p.2.2
  let reassoc : (δ × a) × e ≃ δ × (a × e) := Equiv.prodAssoc δ a e
  obtain ⟨J, hJcard, hJmass⟩ :=
    exists_topWeightMass_support K (fun p : (δ × a) × e ↦ w (reassoc p))
  let S : Finset (δ × a) := J.image Prod.fst
  refine ⟨S, Finset.card_image_le.trans hJcard, ?_⟩
  have hsub : J ⊆ S ×ˢ (Finset.univ : Finset e) := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_univ _⟩
  have hselected : ∑ p ∈ J, w (reassoc p) ≤ ∑ p ∈ S, lam p.1 p.2 := by
    calc
      ∑ p ∈ J, w (reassoc p) ≤
          ∑ p ∈ S ×ˢ (Finset.univ : Finset e), w (reassoc p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ ↦ mul_nonneg (hlam p.1.1 p.1.2) (hc p.1.1 p.2))
      _ = ∑ p ∈ S, lam p.1 p.2 * ∑ j, c p.1 j := by
        rw [Finset.sum_product]
        simp only [w, reassoc, Equiv.prodAssoc_apply, ← Finset.mul_sum]
      _ ≤ ∑ p ∈ S, lam p.1 p.2 :=
        Finset.sum_le_sum fun p _ ↦ by
          simpa using mul_le_mul_of_nonneg_left (hc_sum p.1) (hlam p.1 p.2)
  rw [← topWeightMass_reindex reassoc K w, hJmass]
  exact hselected

/-- The target-coordinate selection gives natural allocations sharing one
budget; zero allocations and oversized ranks use saturating top mass. -/
theorem exists_target_topWeightMass_allocation
    {δ a e : Type*} [Fintype δ] [Fintype a] [Fintype e]
    (K : ℕ) (lam : δ → a → ℝ) (c : δ → e → ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j) (hc : ∀ i j, 0 ≤ c i j)
    (hc_sum : ∀ i, ∑ j, c i j ≤ 1) :
    ∃ k : δ → ℕ, (∑ i, k i) ≤ K ∧
      topWeightMass K (fun p : δ × (a × e) ↦ lam p.1 p.2.1 * c p.1 p.2.2) ≤
        ∑ i, topWeightMass (k i) (lam i) := by
  classical
  obtain ⟨S, hScard, hmass⟩ := exists_target_topWeightMass_support K lam c hlam hc hc_sum
  refine ⟨fun i ↦ (groupedFiberSupport S i).card, ?_, ?_⟩
  · rw [sum_card_groupedFiberSupport]
    exact hScard
  · calc
      _ ≤ ∑ i, ∑ j ∈ groupedFiberSupport S i, lam i j := by
        rw [sum_groupedFiberSupport]
        exact hmass
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ sum_le_topWeightMass (lam i) le_rfl

/-- A nonnegative common scalar can be removed from every selected support. -/
theorem topWeightMass_mul_left {ι : Type*} [Fintype ι]
    (K : ℕ) (w : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    topWeightMass K (fun i ↦ t * w i) = t * topWeightMass K w := by
  apply le_antisymm
  · apply topWeightMass_le
    intro s hs
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_topWeightMass w hs) ht
  · obtain ⟨s, hs, hsum⟩ := exists_topWeightMass_support K w
    rw [hsum, Finset.mul_sum]
    exact sum_le_topWeightMass (fun i ↦ t * w i) hs

/-- The projected PVM Choi spectrum admits a target Schmidt allocation. -/
theorem exists_schmidt_allocation_of_flagged_spectrum
    {δ m n a b : Type*} [Fintype δ] [Fintype m] [Fintype n]
    [Fintype a] [Fintype b] [DecidableEq m] [DecidableEq a]
    (A : δ → Matrix m n ℂ) (B : δ → Matrix a b ℂ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ k : δ → ℕ, (∑ i, k i) ≤ K ∧
      topWeightMass K (fun p : (m × a) × δ ↦
        t * (schmidtWeights (A p.2) p.1.1 * schmidtWeights (B p.2) p.1.2)) ≤
          t * ∑ i, schmidtMass (k i) (B i) := by
  let lam := fun i ↦ schmidtWeights (B i)
  let c := fun i ↦ schmidtWeights (A i)
  obtain ⟨k, hk, hmass⟩ := exists_target_topWeightMass_allocation K lam c
    (fun i j ↦ schmidtWeights_nonneg _ _) (fun i j ↦ schmidtWeights_nonneg _ _)
    (fun i ↦ by
      rw [sum_schmidtWeights]
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hA i) 2)
  refine ⟨k, hk, ?_⟩
  let E : (m × a) × δ ≃ δ × (a × m) :=
    (Equiv.prodComm (m × a) δ).trans
      (Equiv.prodCongr (Equiv.refl δ) (Equiv.prodComm m a))
  have hreindex : topWeightMass K (fun p : (m × a) × δ ↦
      schmidtWeights (A p.2) p.1.1 * schmidtWeights (B p.2) p.1.2) =
        topWeightMass K (fun p : δ × (a × m) ↦ lam p.1 p.2.1 * c p.1 p.2.2) := by
    rw [← topWeightMass_reindex E K]
    congr 1
    funext p
    simp [E, lam, c, mul_comm]
  rw [topWeightMass_mul_left K _ ht, hreindex]
  exact mul_le_mul_of_nonneg_left hmass ht

/-- If an allocation captures all normalized blocks, it covers their ranks. -/
theorem sum_rank_le_of_schmidt_allocation {δ a b : Type*}
    [Fintype δ] [Fintype a] [Fintype b] [DecidableEq a]
    (B : δ → Matrix a b ℂ) (hB : ∀ i, ‖B i‖ = 1) (k : δ → ℕ) {K : ℕ}
    (hk : (∑ i, k i) ≤ K)
    (hmass : (Fintype.card δ : ℝ) ≤ ∑ i, schmidtMass (k i) (B i)) :
    (∑ i, (B i).rank) ≤ K := by
  have hle (i : δ) : schmidtMass (k i) (B i) ≤ 1 := by
    have h := topWeightMass_le_sum (k i) (schmidtWeights (B i))
      (schmidtWeights_nonneg (B i))
    simpa only [schmidtMass, sum_schmidtWeights, hB i, one_pow] using h
  have hsum : ∑ i, (1 - schmidtMass (k i) (B i)) = 0 := by
    have hnonneg := Finset.sum_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset δ)) ↦ sub_nonneg.mpr (hle i))
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hnonneg ⊢
    linarith
  have heq (i : δ) : 1 ≤ schmidtMass (k i) (B i) := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset δ)) ↦ sub_nonneg.mpr (hle j))).mp hsum i
      (Finset.mem_univ i)
    linarith
  exact (Finset.sum_le_sum fun i _ ↦ rank_le_of_one_le_schmidtMass (B i) (hB i) (heq i)).trans hk

/-- A flat left Gram spectrum has the usual `k / d` upper mass bound. -/
theorem schmidtMass_le_div_card_of_flat_gram {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] (B : Matrix a b ℂ)
    (hB : B * Bᴴ = Matrix.diagonal (fun _ : a ↦ ((Fintype.card a : ℝ)⁻¹ : ℂ)))
    (k : ℕ) : schmidtMass k B ≤ (k : ℝ) / Fintype.card a := by
  rw [schmidtMass_eq_topWeightMass_of_coordinates B (1 : Matrix a a ℂ)
    (fun _ : a ↦ (Fintype.card a : ℝ)⁻¹) isIsometry_one
    (by simpa using (isIsometry_one (n := a) (𝕜 := ℂ)))
    (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) (by simpa using hB), div_eq_mul_inv]
  exact topWeightMass_le_mul k _ (inv_nonneg.mpr (Nat.cast_nonneg _)) (fun _ ↦ le_rfl)

/-- Under a common positive lower spectral weight, a deficient total
allocation loses at least one weight in one block. -/
theorem sum_schmidtMass_le_card_sub_of_budget_lt
    {δ a b : Type*} [Fintype δ] [Fintype a] [Fintype b] [DecidableEq a]
    (B : δ → Matrix a b ℂ) (hB : ∀ i, ‖B i‖ = 1) (k : δ → ℕ)
    {K : ℕ} {t : ℝ} (ht : ∀ i j, t ≤ schmidtWeights (B i) j)
    (hk : (∑ i, k i) ≤ K) (hK : K < Fintype.card δ * Fintype.card a) :
    ∑ i, schmidtMass (k i) (B i) ≤ (Fintype.card δ : ℝ) - t := by
  classical
  have hex : ∃ i, k i < Fintype.card a := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset δ)) ↦ h i)
    have hfull : Fintype.card δ * Fintype.card a ≤ ∑ i, k i := by
      simpa [Finset.sum_const, Nat.nsmul_eq_mul] using hsum
    omega
  obtain ⟨i, hi⟩ := hex
  have hle (j : δ) : schmidtMass (k j) (B j) ≤ 1 := by
    have h := topWeightMass_le_sum (k j) (schmidtWeights (B j)) (schmidtWeights_nonneg _)
    simpa only [schmidtMass, sum_schmidtWeights, hB j, one_pow] using h
  have hstrict : schmidtMass (k i) (B i) ≤ 1 - t := by
    have h := topWeightMass_le_sum_sub_of_lt_card (schmidtWeights (B i))
      (schmidtWeights_nonneg _) (ht i) hi
    simpa only [schmidtMass, sum_schmidtWeights, hB i, one_pow] using h
  have hrest := Finset.sum_le_sum (s := (Finset.univ : Finset δ).erase i)
    (fun j _ ↦ hle j)
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset δ)
    (fun j ↦ schmidtMass (k j) (B j)) (Finset.mem_univ i)
  have hcard : ((Finset.univ : Finset δ).erase i).card + 1 = Fintype.card δ := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i)
  have hcardR : (((Finset.univ : Finset δ).erase i).card : ℝ) + 1 = Fintype.card δ := by
    exact_mod_cast hcard
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hrest
  linarith

section Pure

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB] [Nonempty ιA] [Nonempty ιB]

/-- The full target spectral allocation in the charged pure protocol model. -/
theorem PureProtocol.pvm_spectral_allocation
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    ∃ k : (ιA × ιB) → ℕ, (∑ i, k i) ≤ K ∧
      (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤
        ∑ i, schmidtMass (k i) (pvmConjugateColumnMatrix M i) := by
  let A := fun i ↦ resourceMatrix (pvmEnvironment M P.globalIsometry i)
  let B := pvmConjugateColumnMatrix M
  let t : ℝ := (Fintype.card (ιA × ιB) : ℝ)⁻¹
  obtain ⟨k, hk, hmass⟩ := exists_schmidt_allocation_of_flagged_spectrum A B
    (fun i ↦ norm_resourceMatrix_pvmEnvironment_le_one
      P.isIsometry_globalIsometry hM i) K (inv_nonneg.mpr (Nat.cast_nonneg _))
  refine ⟨k, hk, ?_⟩
  have hsquare : (1 - ε) ^ 2 ≤ (scorePVM M P.operationalChannel) ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hε.2) ((sub_nonneg.mpr hε.2).trans hscore)).mpr hscore
  have hbound : (1 - ε) ^ 2 ≤ t * ∑ i, schmidtMass (k i) (B i) := by
    apply hsquare.trans
    apply (P.scorePVM_sq_le_schmidtMass_pvmProjected M hK).trans
    rw [pvmProjectedDilation, schmidtMass_tensorChoiMatrix_flag_mul_adjoint]
    exact hmass
  have hD : 0 < (Fintype.card (ιA × ιB) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdiv : (1 - ε) ^ 2 ≤ (∑ i, schmidtMass (k i) (B i)) /
      Fintype.card (ιA × ιB) := by simpa [t, div_eq_mul_inv, mul_comm] using hbound
  simpa only [mul_comm] using (le_div_iff₀ hD).mp hdiv

/-- At exact score, the charged rank covers the sum of target Schmidt ranks. -/
theorem PureProtocol.pvm_exact_schmidt_rank_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hscore : 1 ≤ scorePVM M P.operationalChannel) :
    (∑ i, (pvmConjugateColumnMatrix M i).rank) ≤ K := by
  obtain ⟨k, hk, hmass⟩ := P.pvm_spectral_allocation M hM hK
    (ε := 0) (by norm_num) (by simpa using hscore)
  apply sum_rank_le_of_schmidt_allocation (pvmConjugateColumnMatrix M)
    (fun i ↦ norm_conjugate_pvmColumnMatrix hM i) k hk
  simpa using hmass

/-- The maximally entangled column spectrum forces a cubic dimension floor.
The basis's flat Gram identities are explicit hypotheses of this lemma. -/
theorem PureProtocol.maximallyEntangledPVM_footprint_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA ↦ ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) * Fintype.card ιA * (1 - ε) ^ 2 ≤ K := by
  obtain ⟨k, hk, hmass⟩ := P.pvm_spectral_allocation M hM hK hε hscore
  have hsum : (∑ i, schmidtMass (k i) (pvmConjugateColumnMatrix M i)) ≤
      (K : ℝ) / Fintype.card ιA := by
    calc
      _ ≤ ∑ i, (k i : ℝ) / Fintype.card ιA := Finset.sum_le_sum fun i _ ↦
        schmidtMass_le_div_card_of_flat_gram _ (hflat i) _
      _ = ((∑ i, k i : ℕ) : ℝ) / Fintype.card ιA := by
        simp only [Nat.cast_sum, Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hk) (Nat.cast_nonneg _)
  have hd : 0 < (Fintype.card ιA : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (le_div_iff₀ hd).mp (hmass.trans hsum)
  nlinarith

/-- A target-dependent full-rank spectral threshold for PVMs. -/
theorem PureProtocol.pvm_full_spectral_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} {ε t : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hthreshold : ε < t / (2 * Fintype.card (ιA × ιB)))
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    Fintype.card (ιA × ιB) * Fintype.card ιA ≤ K := by
  by_contra hKfull
  obtain ⟨k, hk, hmass⟩ := P.pvm_spectral_allocation M hM hK hε hscore
  have hupper := sum_schmidtMass_le_card_sub_of_budget_lt
    (pvmConjugateColumnMatrix M) (fun i ↦ norm_conjugate_pvmColumnMatrix hM i)
    k ht hk (Nat.lt_of_not_ge hKfull)
  have hD : 0 < (Fintype.card (ιA × ιB) : ℝ) := by exact_mod_cast Fintype.card_pos
  have he := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hD)).mp hthreshold
  nlinarith [hmass.trans hupper, mul_nonneg hD.le (sq_nonneg ε)]

end Pure

section Mixed

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB] [Nonempty ιA] [Nonempty ιB]

/-- Finite mixed resources retain the same spectral-allocation inequality. -/
theorem MixedResource.pvm_spectral_allocation {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    ∃ k : (ιA × ιB) → ℕ, (∑ i, k i) ≤ K ∧
      (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤
        ∑ i, schmidtMass (k i) (pvmConjugateColumnMatrix M i) := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.pvm_spectral_allocation M hM hPK hε (hscore.trans hk)

/-- Exact score requires the summed target Schmidt ranks for finite mixtures. -/
theorem MixedResource.pvm_exact_schmidt_rank_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hscore : 1 ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    (∑ i, (pvmConjugateColumnMatrix M i).rank) ≤ K := by
  obtain ⟨k, hk, hmass⟩ := m.pvm_spectral_allocation VA VB DA DB hVA hVB hDA hDB
    M hM hR hK (ε := 0) (by norm_num) (by simpa using hscore)
  apply sum_rank_le_of_schmidt_allocation (pvmConjugateColumnMatrix M)
    (fun i ↦ norm_conjugate_pvmColumnMatrix hM i) k hk
  simpa using hmass

/-- The cubic flat-column floor for finite mixed resources and common maps. -/
theorem MixedResource.maximallyEntangledPVM_footprint_floor {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA ↦ ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) * Fintype.card ιA * (1 - ε) ^ 2 ≤ K := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.maximallyEntangledPVM_footprint_floor M hM hflat hPK hε (hscore.trans hk)

/-- The deterministic full-rank PVM threshold survives finite mixing. -/
theorem MixedResource.pvm_full_spectral_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} {ε t : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hthreshold : ε < t / (2 * Fintype.card (ιA × ιB)))
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    Fintype.card (ιA × ιB) * Fintype.card ιA ≤ K := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.pvm_full_spectral_floor M hM hPK hε ht hthreshold (hscore.trans hk)

end Mixed
end NLQCLean
