import NLQCLean.Models.ProjectiveProbability

/-!
# Score one is exact two-sided PVM implementation

The converse is proved from normalized joint
probabilities and linearity of the actual dilation. Exactness concerns all
input density matrices; it imposes no condition on the discarded state.
-/

namespace NLQCLean
open Matrix

section Frozen
variable {n δ εA εB : Type*}
variable [Fintype n] [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

omit [Fintype n] [Fintype εA] [Fintype εB] [DecidableEq n] [DecidableEq εA] [DecidableEq εB] in
/-- Each frozen output block is the intended rank-one amplitude, or zero
when the two labels disagree. -/
theorem outcomeBlock_flag_mul_adjoint_apply
    (ω : δ → εA × εB → ℂ) (M : Matrix n δ ℂ)
    (a b : δ) (e : εA × εB) (j : n) :
    outcomeBlock (flagIsometry ω * Mᴴ) a b e j =
      if a = b then ω a e * star (M j a) else 0 := by
  by_cases hab : a = b <;> simp [outcomeBlock_apply, Matrix.mul_apply, flagIsometry_apply,
    Matrix.conjTranspose_apply, ite_mul, mul_ite, hab]

omit [Fintype n] [DecidableEq n] [DecidableEq εA] [DecidableEq εB] in
/-- The actual POVM effects of a frozen dilation are the intended PVM
projectors, with all mismatched effects zero. -/
theorem outcomeBlock_flag_mul_adjoint_gram
    (ω : δ → εA × εB → ℂ) (hω : ∀ i, IsUnitVector (ω i))
    (M : Matrix n δ ℂ) (a b : δ) :
    (outcomeBlock (flagIsometry ω * Mᴴ) a b)ᴴ *
      outcomeBlock (flagIsometry ω * Mᴴ) a b =
        if a = b then pvmProj M a else 0 := by
  by_cases hab : a = b
  · subst b
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      outcomeBlock_flag_mul_adjoint_apply, ite_true, star_mul, star_star,
      pvmProj, pureState_apply, pvmColumn_apply]
    calc
      _ = (M j a * star (M k a)) * ∑ e, ω a e * star (ω a e) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
      _ = _ := by rw [(isUnitVector_iff_sum _).mp (hω a), mul_one]
  · ext j k
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hab]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Frozen flags imply exactness on every density matrix. In fact the
probability identity holds on every input matrix. -/
theorem twoSidedExact_flag_mul_adjoint
    (ω : δ → εA × εB → ℂ) (hω : ∀ i, IsUnitVector (ω i))
    (M : Matrix n δ ℂ) : TwoSidedExact (flagIsometry ω * Mᴴ) M := by
  have hprob (ρ : Matrix n n ℂ) (a b : δ) :
      outcomeProb (flagIsometry ω * Mᴴ) ρ a b =
        if a = b then (pvmProj M a * ρ).trace else 0 := by
    rw [outcomeProb, Matrix.trace_mul_cycle, outcomeBlock_flag_mul_adjoint_gram ω hω]
    split_ifs <;> simp
  constructor
  · intro ρ _ i
    simp [hprob]
  · intro ρ _
    apply Finset.sum_eq_zero
    intro ab hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    simp [hprob, hab]

end Frozen

section ScoreOne
variable {δ εA εB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB] [Nonempty δ]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]
variable {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}

omit [DecidableEq εA] [DecidableEq εB] in
/-- An average of normalized success probabilities equals one only when
every basis input has success probability one. -/
theorem outcomeProb_self_eq_one_of_scorePVM_eq_one
    (hF : IsIsometry F) (hM : IsIsometry M)
    (hq : scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) = 1)
    (i : δ) : (outcomeProb F (pvmProj M i) i i).re = 1 := by
  let p : δ → ℝ := fun j => (outcomeProb F (pvmProj M j) j j).re
  have hp (j : δ) : p j ≤ 1 :=
    outcomeProb_le_one hF (isState_pureState (isUnitVector_pvmColumn hM j)) j j
  have hD : (Fintype.card δ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ j, p j = (Fintype.card δ : ℝ) := by
    change (Fintype.card δ : ℝ)⁻¹ * ∑ j,
      (channelOf (F.submatrix (outputRegroup δ δ εA εB) id) (pvmProj M j) (j,j) (j,j)).re = 1 at hq
    simp only [channelOf_regrouped_diag] at hq
    simpa only [mul_one] using (inv_mul_eq_iff_eq_mul₀ hD).mp hq
  have hz : ∑ j, (1 - p j) = 0 := by simp [Finset.sum_sub_distrib, hsum]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hp j))).mp hz i
    (Finset.mem_univ i)
  change p i = 1
  linarith

omit [DecidableEq εA] [DecidableEq εB] in
/-- Every wrong joint outcome block annihilates a perfectly recognized
basis vector. This includes both mismatches and a wrong common label. -/
theorem outcomeBlock_mulVec_eq_zero_of_scorePVM_eq_one
    (hF : IsIsometry F) (hM : IsIsometry M)
    (hq : scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) = 1)
    (i a b : δ) (hab : (a,b) ≠ (i,i)) :
    outcomeBlock F a b *ᵥ pvmColumn M i = 0 := by
  let p : δ × δ → ℝ := fun ab => (outcomeProb F (pvmProj M i) ab.1 ab.2).re
  have hρ : IsState (pvmProj M i) := isState_pureState (isUnitVector_pvmColumn hM i)
  have hp (ab : δ × δ) : 0 ≤ p ab := outcomeProb_nonneg F hρ ab.1 ab.2
  have hs : ∑ ab, p ab = 1 := sum_outcomeProb_re_eq_one hF hρ
  have hi : p (i,i) = 1 := outcomeProb_self_eq_one_of_scorePVM_eq_one hF hM hq i
  have he := Finset.sum_erase_add (Finset.univ : Finset (δ × δ)) p (Finset.mem_univ (i,i))
  have hz : ∑ ab ∈ Finset.univ.erase (i,i), p ab = 0 := by rw [hi, hs] at he; linarith
  have habmem : (a,b) ∈ (Finset.univ : Finset (δ × δ)).erase (i,i) := by simp [hab]
  have hpzero := (Finset.sum_eq_zero_iff_of_nonneg (fun ab _ => hp ab)).mp hz (a,b) habmem
  have hnorm : ∑ e, Complex.normSq ((outcomeBlock F a b *ᵥ pvmColumn M i) e) = 0 := by
    simpa only [p, pvmProj, outcomeProb_pureState, Complex.ofReal_re] using hpzero
  funext e
  exact eq_zero_of_sum_normSq_eq_zero hnorm e

omit [DecidableEq εA] [DecidableEq εB] in
/-- Score one supplies the actual, individually normalized flagged dilation.
No exactness premise is assumed. -/
theorem exists_frozen_pvm_of_scorePVM_eq_one
    (hF : IsIsometry F) (hM : IsIsometry M)
    (hq : scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) = 1) :
    ∃ ω : δ → εA × εB → ℂ, (∀ i, IsUnitVector (ω i)) ∧
      F = flagIsometry ω * Mᴴ := by
  let ω : δ → εA × εB → ℂ := fun i => outcomeBlock F i i *ᵥ pvmColumn M i
  have hω (i : δ) : IsUnitVector (ω i) := by
    simpa only [IsUnitVector, ω, pvmProj, outcomeProb_pureState, Complex.ofReal_re] using
      outcomeProb_self_eq_one_of_scorePVM_eq_one hF hM hq i
  have hFM : F * M = flagIsometry ω := by
    ext p i
    rcases p with ⟨⟨a,eA⟩,⟨b,eB⟩⟩
    change (outcomeBlock F a b *ᵥ pvmColumn M i) (eA,eB) = _
    by_cases ha : a = i
    · subst a
      by_cases hb : b = i
      · subst b; simp [flagIsometry_apply, ω]
      · have hk := outcomeBlock_mulVec_eq_zero_of_scorePVM_eq_one hF hM hq i i b (by simp [hb])
        simp [hk, flagIsometry_apply, hb]
    · have hk := outcomeBlock_mulVec_eq_zero_of_scorePVM_eq_one hF hM hq i a b (by simp [ha])
      simp [hk, flagIsometry_apply, ha]
  refine ⟨ω, hω, ?_⟩
  have hM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hM
  rw [← hFM, Matrix.mul_assoc, hM', Matrix.mul_one]

omit [DecidableEq εA] [DecidableEq εB] in
/-- The average success score is one iff this dilation
performs the ordered two-sided rank-one PVM on every input state. -/
theorem scorePVM_eq_one_iff_twoSidedExact
    (hF : IsIsometry F) (hM : IsIsometry M) :
    scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) = 1 ↔
      TwoSidedExact F M := by
  constructor
  · intro hq
    obtain ⟨ω, hω, hFω⟩ := exists_frozen_pvm_of_scorePVM_eq_one hF hM hq
    rw [hFω]
    exact twoSidedExact_flag_mul_adjoint ω hω M
  · exact scorePVM_channelOf_regrouped_eq_one_of_twoSidedExact hM

end ScoreOne
end NLQCLean
