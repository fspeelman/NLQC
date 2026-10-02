import NLQCLean.Models.ProjectiveProtocolScore

/-!
# Worst-case joint total variation for the PVM task

This file keeps the two output labels jointly: the
actual distribution is the real diagonal of the operational channel on
`δ × δ`, while the ideal distribution is supported on `(i,i)` with weight
`Tr(pvmProj M i * ρ)`.  The worst-case error is the real supremum over every
input density matrix.
-/

namespace NLQCLean

open Matrix
open scoped ComplexOrder

noncomputable section

section Distributions

variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- The actual joint output distribution, retaining both classical labels. -/
def pvmActualDist
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (ρ : Matrix δ δ ℂ) (ab : δ × δ) : ℝ :=
  (N ρ ab ab).re

/-- The ideal ordered rank-one PVM distribution.  Its support is the
diagonal set of joint labels, rather than either one-party marginal. -/
def pvmIdealDist (M ρ : Matrix δ δ ℂ) (ab : δ × δ) : ℝ :=
  if ab.1 = ab.2 then ((pvmProj M ab.1 * ρ).trace).re else 0

/-- A channel has physical joint PVM outcome statistics when its diagonal
is a probability distribution for every density-matrix input. -/
structure IsPVMOutcomeChannel
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) : Prop where
  nonneg : ∀ {ρ : Matrix δ δ ℂ}, IsState ρ → ∀ ab, 0 ≤ pvmActualDist N ρ ab
  sum_eq_one : ∀ {ρ : Matrix δ δ ℂ}, IsState ρ → ∑ ab, pvmActualDist N ρ ab = 1

theorem pvmIdealDist_nonneg (M : Matrix δ δ ℂ)
    {ρ : Matrix δ δ ℂ} (hρ : IsState ρ) (ab : δ × δ) :
    0 ≤ pvmIdealDist M ρ ab := by
  rcases ab with ⟨a, b⟩
  by_cases hab : a = b
  · subst b
    rw [pvmIdealDist, ite_eq_left rfl, trace_pvmProj_mul_eq_diag]
    exact (Complex.nonneg_iff.mp (hρ.1.conjTranspose_mul_mul_same M).diag_nonneg).1
  · simp [pvmIdealDist, hab]

theorem sum_pvmIdealDist_eq_one {M : Matrix δ δ ℂ} (hM : IsIsometry M)
    {ρ : Matrix δ δ ℂ} (hρ : IsState ρ) :
    ∑ ab, pvmIdealDist M ρ ab = 1 := by
  have hMM : M * Mᴴ = 1 := mul_eq_one_comm.mp hM
  calc
    ∑ ab, pvmIdealDist M ρ ab = ∑ a, ((pvmProj M a * ρ).trace).re := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ => by simp [pvmIdealDist]
    _ = (Mᴴ * ρ * M).trace.re := by
      simp_rw [trace_pvmProj_mul_eq_diag]
      rw [← Complex.re_sum]
      rfl
    _ = 1 := by
      rw [Matrix.trace_mul_cycle, hMM, Matrix.one_mul, hρ.2]
      rfl

omit [DecidableEq δ] in
@[simp] theorem pvmActualDist_channelOf_regrouped
    {εA εB : Type*} [Fintype εA] [Fintype εB]
    [DecidableEq εA] [DecidableEq εB]
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ)
    (ρ : Matrix δ δ ℂ) (ab : δ × δ) :
    pvmActualDist (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) ρ ab =
      (outcomeProb F ρ ab.1 ab.2).re := by
  rcases ab with ⟨a, b⟩
  rw [pvmActualDist, channelOf_regrouped_diag]

theorem isPVMOutcomeChannel_channelOf_regrouped
    {εA εB : Type*} [Fintype εA] [Fintype εB]
    [DecidableEq εA] [DecidableEq εB]
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} (hF : IsIsometry F) :
    IsPVMOutcomeChannel
      (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) := by
  constructor
  · intro ρ hρ ab
    rw [pvmActualDist_channelOf_regrouped]
    exact outcomeProb_nonneg F hρ ab.1 ab.2
  · intro ρ hρ
    simpa only [pvmActualDist_channelOf_regrouped] using
      sum_outcomeProb_re_eq_one hF hρ

omit [DecidableEq δ] in
/-- Physical joint-outcome statistics are closed under honest finite convex
mixtures.  Zero weights are allowed. -/
theorem IsPVMOutcomeChannel.sum_smul {κ : Type*} [Fintype κ]
    (w : κ → ℝ)
    (N : κ → Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (hN : ∀ k, IsPVMOutcomeChannel (N k))
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    IsPVMOutcomeChannel (∑ k, ((w k : ℂ)) • N k) := by
  constructor
  · intro ρ hρ ab
    simp only [pvmActualDist, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
      Complex.re_ofReal_mul]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) ((hN k).nonneg hρ ab)
  · intro ρ hρ
    simp only [pvmActualDist, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
      Complex.re_ofReal_mul]
    rw [Finset.sum_comm]
    calc
      ∑ k, ∑ ab, w k * (N k ρ ab ab).re =
          ∑ k, w k * ∑ ab, (N k ρ ab ab).re := by
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      _ = ∑ k, w k * 1 := by
        exact Finset.sum_congr rfl fun k _ => by
          congr 1
          change ∑ ab, pvmActualDist (N k) ρ ab = 1
          exact (hN k).sum_eq_one hρ
      _ = 1 := by simpa using hsum

end Distributions

section TotalVariation

variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- Total variation of the actual and ideal joint distributions on one
input density matrix. -/
def pvmInputTV (M : Matrix δ δ ℂ)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (ρ : Matrix δ δ ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ ab, |pvmActualDist N ρ ab - pvmIdealDist M ρ ab|

/-- Worst-case joint total-variation error, with the supremum taken over all
input density matrices. -/
def pvmTVError (M : Matrix δ δ ℂ)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) : ℝ :=
  sSup {e : ℝ | ∃ ρ : Matrix δ δ ℂ, IsState ρ ∧ e = pvmInputTV M N ρ}

theorem pvmInputTV_nonneg (M : Matrix δ δ ℂ)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (ρ : Matrix δ δ ℂ) :
    0 ≤ pvmInputTV M N ρ := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem pvmInputTV_le_one {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N)
    {ρ : Matrix δ δ ℂ} (hρ : IsState ρ) :
    pvmInputTV M N ρ ≤ 1 := by
  unfold pvmInputTV
  calc
    (1 / 2 : ℝ) * ∑ ab, |pvmActualDist N ρ ab - pvmIdealDist M ρ ab| ≤
        (1 / 2 : ℝ) * ∑ ab, (pvmActualDist N ρ ab + pvmIdealDist M ρ ab) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ab _ => ?_) (by norm_num)
      apply abs_le.mpr
      constructor
      · have ha := hN.nonneg hρ ab
        have hi := pvmIdealDist_nonneg M hρ ab
        linarith
      · have ha := hN.nonneg hρ ab
        have hi := pvmIdealDist_nonneg M hρ ab
        linarith
    _ = 1 := by
      rw [Finset.sum_add_distrib, hN.sum_eq_one hρ, sum_pvmIdealDist_eq_one hM hρ]
      norm_num

theorem pvmTVError_bddAbove {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N) :
    BddAbove {e : ℝ | ∃ ρ : Matrix δ δ ℂ, IsState ρ ∧ e = pvmInputTV M N ρ} := by
  refine ⟨1, ?_⟩
  rintro e ⟨ρ, hρ, rfl⟩
  exact pvmInputTV_le_one hM hN hρ

theorem pvmInputTV_le_pvmTVError {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N)
    {ρ : Matrix δ δ ℂ} (hρ : IsState ρ) :
    pvmInputTV M N ρ ≤ pvmTVError M N := by
  apply le_csSup (pvmTVError_bddAbove hM hN)
  exact ⟨ρ, hρ, rfl⟩

theorem pvmTVError_mem_Icc [Nonempty δ] {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N) :
    pvmTVError M N ∈ Set.Icc (0 : ℝ) 1 := by
  let i : δ := Classical.choice inferInstance
  have hρ : IsState (pvmProj M i) :=
    isState_pureState (isUnitVector_pvmColumn hM i)
  constructor
  · exact (pvmInputTV_nonneg M N (pvmProj M i)).trans
      (pvmInputTV_le_pvmTVError hM hN hρ)
  · apply csSup_le
    · exact ⟨pvmInputTV M N (pvmProj M i), pvmProj M i, hρ, rfl⟩
    · rintro e ⟨ρ, hρ', rfl⟩
      exact pvmInputTV_le_one hM hN hρ'

/-- A target basis state gives the ideal point mass at `(i,i)`. -/
theorem pvmIdealDist_pvmProj {M : Matrix δ δ ℂ} (hM : IsIsometry M)
    (i : δ) (ab : δ × δ) :
    pvmIdealDist M (pvmProj M i) ab = if ab = (i, i) then 1 else 0 := by
  rcases ab with ⟨a, b⟩
  by_cases hab : a = b
  · subst b
    by_cases hai : a = i
    · subst a
      rw [pvmIdealDist, ite_eq_left rfl, ite_eq_left rfl]
      change (pvmProj M i * pureState (pvmColumn M i)).trace.re = 1
      rw [trace_pvmProj_pureState, pvmColumn_inner_self hM]
      simp
    · have hia : i ≠ a := Ne.symm hai
      rw [pvmIdealDist, ite_eq_left rfl, ite_eq_right (by simp [hai])]
      change (pvmProj M a * pureState (pvmColumn M i)).trace.re = 0
      rw [trace_pvmProj_pureState, pvmColumn_inner_eq_zero hM hia]
      simp
  · rw [pvmIdealDist, ite_eq_right hab, ite_eq_right]
    intro heq
    exact hab ((congrArg Prod.fst heq).trans (congrArg Prod.snd heq).symm)

/-- Total variation from a point mass is one minus the mass assigned to its
point. -/
theorem half_sum_abs_sub_pointMass {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) (i : α) :
    (1 / 2 : ℝ) * ∑ j, |p j - if j = i then 1 else 0| = 1 - p i := by
  have hpi : p i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have hiabs : |p i - 1| = 1 - p i := by
    rw [abs_of_nonpos (sub_nonpos.mpr hpi), neg_sub]
  have hrest : ∑ j ∈ (Finset.univ : Finset α).erase i,
      |p j - if j = i then 1 else 0| = 1 - p i := by
    have heq : ∑ j ∈ (Finset.univ : Finset α).erase i,
        |p j - if j = i then 1 else 0| =
          ∑ j ∈ (Finset.univ : Finset α).erase i, p j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji, abs_of_nonneg (hp j)]
    rw [heq]
    have herase := Finset.sum_erase_add (Finset.univ : Finset α) p (Finset.mem_univ i)
    linarith
  have hsplit : ∑ j, |p j - if j = i then 1 else 0| =
      ∑ j ∈ (Finset.univ : Finset α).erase i,
        |p j - if j = i then 1 else 0| + |p i - 1| := by
    calc
      _ = ∑ j ∈ (Finset.univ : Finset α).erase i,
          |p j - if j = i then 1 else 0| +
          |p i - if i = i then 1 else 0| :=
        (Finset.sum_erase_add (Finset.univ : Finset α)
          (fun j => |p j - if j = i then 1 else 0|) (Finset.mem_univ i)).symm
      _ = _ := by simp
  rw [hsplit, hrest, hiabs]
  ring

theorem pvmInputTV_pvmProj {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N) (i : δ) :
    pvmInputTV M N (pvmProj M i) =
      1 - (N (pvmProj M i) (i, i) (i, i)).re := by
  have hρ : IsState (pvmProj M i) :=
    isState_pureState (isUnitVector_pvmColumn hM i)
  simpa only [pvmInputTV, pvmActualDist, pvmIdealDist_pvmProj hM] using
    half_sum_abs_sub_pointMass
      (fun ab => pvmActualDist N (pvmProj M i) ab)
      (hN.nonneg hρ) (hN.sum_eq_one hρ) (i, i)

/-- eq:pvm-error-implies-score: worst-case joint TV dominates one
minus the average basis success score. -/
theorem one_sub_scorePVM_le_pvmTVError [Nonempty δ]
    {M : Matrix δ δ ℂ} {N}
    (hM : IsIsometry M) (hN : IsPVMOutcomeChannel N) :
    1 - scorePVM M N ≤ pvmTVError M N := by
  have hD : (Fintype.card δ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hi (i : δ) :
      1 - (N (pvmProj M i) (i, i) (i, i)).re ≤ pvmTVError M N := by
    rw [← pvmInputTV_pvmProj hM hN i]
    exact pvmInputTV_le_pvmTVError hM hN
      (isState_pureState (isUnitVector_pvmColumn hM i))
  calc
    1 - scorePVM M N = (Fintype.card δ : ℝ)⁻¹ *
        ∑ i, (1 - (N (pvmProj M i) (i, i) (i, i)).re) := by
      simp only [scorePVM, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
      field_simp
    _ ≤ (Fintype.card δ : ℝ)⁻¹ * ∑ _i : δ, pvmTVError M N :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = pvmTVError M N := by simp [hD]

/-- The worst-case error of an arbitrary physical purified dilation lies in
the unit interval.  The environments remain unrestricted finite types. -/
theorem pvmTVError_channelOf_regrouped_mem_Icc [Nonempty δ]
    {εA εB : Type*} [Fintype εA] [Fintype εB]
    [DecidableEq εA] [DecidableEq εB]
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) :
    pvmTVError M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) ∈
      Set.Icc (0 : ℝ) 1 :=
  pvmTVError_mem_Icc hM (isPVMOutcomeChannel_channelOf_regrouped hF)

/-- The score/TV bridge specialized to an arbitrary physical purified
dilation, still with both output labels in the distribution. -/
theorem one_sub_scorePVM_channelOf_regrouped_le_pvmTVError [Nonempty δ]
    {εA εB : Type*} [Fintype εA] [Fintype εB]
    [DecidableEq εA] [DecidableEq εB]
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) :
    1 - scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) ≤
      pvmTVError M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) :=
  one_sub_scorePVM_le_pvmTVError hM
    (isPVMOutcomeChannel_channelOf_regrouped hF)

end TotalVariation

section Phases

variable {δ : Type*} [Fintype δ] [DecidableEq δ]

theorem pvmIdealDist_mul_diagonal_phase
    (M ρ : Matrix δ δ ℂ) (z : δ → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) (ab : δ × δ) :
    pvmIdealDist (M * Matrix.diagonal z) ρ ab = pvmIdealDist M ρ ab := by
  simp only [pvmIdealDist, pvmProj_mul_diagonal_phase M z hz]

theorem pvmInputTV_mul_diagonal_phase
    (M : Matrix δ δ ℂ) (z : δ → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (ρ : Matrix δ δ ℂ) :
    pvmInputTV (M * Matrix.diagonal z) N ρ = pvmInputTV M N ρ := by
  simp only [pvmInputTV, pvmIdealDist_mul_diagonal_phase M ρ z hz]

theorem pvmTVError_mul_diagonal_phase
    (M : Matrix δ δ ℂ) (z : δ → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    pvmTVError (M * Matrix.diagonal z) N = pvmTVError M N := by
  simp only [pvmTVError, pvmInputTV_mul_diagonal_phase M z hz]

end Phases

section Protocols

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

theorem isPVMOutcomeChannel_operationalChannel
    {η : ρA × ρB → ℂ} (hη : IsUnitVector η)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    IsPVMOutcomeChannel (operationalChannel η VA VB DA DB) := by
  simpa only [operationalChannel, globalIsometryRegrouped] using
    isPVMOutcomeChannel_channelOf_regrouped
      (isIsometry_globalIsometry hη hVA hVB hDA hDB)

theorem PureProtocol.isPVMOutcomeChannel
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB) :
    IsPVMOutcomeChannel P.operationalChannel :=
  isPVMOutcomeChannel_operationalChannel P.resource_unit
    P.encA_isometry P.encB_isometry P.decA_isometry P.decB_isometry

theorem MixedResource.isPVMOutcomeChannel_mixedChannel {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    IsPVMOutcomeChannel (m.mixedChannel VA VB DA DB) := by
  rw [MixedResource.mixedChannel]
  exact IsPVMOutcomeChannel.sum_smul m.weight
    (fun k => operationalChannel (m.component k) VA VB DA DB)
    (fun k => isPVMOutcomeChannel_operationalChannel (m.component_unit k)
      hVA hVB hDA hDB)
    m.weight_nonneg m.weight_sum

theorem PureProtocol.pvmTVError_mem_Icc [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    pvmTVError M P.operationalChannel ∈ Set.Icc (0 : ℝ) 1 :=
  NLQCLean.pvmTVError_mem_Icc hM P.isPVMOutcomeChannel

theorem PureProtocol.one_sub_scorePVM_le_pvmTVError [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    1 - scorePVM M P.operationalChannel ≤ pvmTVError M P.operationalChannel :=
  NLQCLean.one_sub_scorePVM_le_pvmTVError hM P.isPVMOutcomeChannel

theorem MixedResource.pvmTVError_mem_Icc [Nonempty ιA] [Nonempty ιB] {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    pvmTVError M (m.mixedChannel VA VB DA DB) ∈ Set.Icc (0 : ℝ) 1 :=
  NLQCLean.pvmTVError_mem_Icc hM
    (m.isPVMOutcomeChannel_mixedChannel hVA hVB hDA hDB)

theorem MixedResource.one_sub_scorePVM_le_pvmTVError
    [Nonempty ιA] [Nonempty ιB] {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    1 - scorePVM M (m.mixedChannel VA VB DA DB) ≤
      pvmTVError M (m.mixedChannel VA VB DA DB) :=
  NLQCLean.one_sub_scorePVM_le_pvmTVError hM
    (m.isPVMOutcomeChannel_mixedChannel hVA hVB hDA hDB)

end Protocols

end

end NLQCLean
