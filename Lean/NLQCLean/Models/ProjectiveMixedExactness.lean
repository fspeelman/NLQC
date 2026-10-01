import NLQCLean.Models.ProjectiveProtocolScore

/-!
# Exact PVM semantics for finite mixed resources

Exactness is stated directly for the diagonal joint
outcome probabilities of a channel.  For a purified channel this is
equivalent to `TwoSidedExact`; for an actual finite common-map mixed resource,
score one is equivalent to this all-input channel task.  Components of weight
zero are never required to be exact.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

section ChannelTask

variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- The exact two-sided ordered rank-one PVM task at channel level.

Only diagonal matrix entries of the classical joint output are probabilities.
Both parties' labels are retained, and the second field is the literal total
probability of unequal labels. -/
structure TwoSidedExactChannel
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (M : Matrix δ δ ℂ) : Prop where
  agree : ∀ ρ : Matrix δ δ ℂ, IsState ρ → ∀ i : δ,
    N ρ (i, i) (i, i) = (pvmProj M i * ρ).trace
  disagree : ∀ ρ : Matrix δ δ ℂ, IsState ρ →
    ∑ p ∈ Finset.univ.filter (fun p : δ × δ => p.1 ≠ p.2),
      N ρ p p = 0

variable {εA εB : Type*} [Fintype εA] [Fintype εB]
variable [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Regrouping the two laboratories and tracing out their environments turns
the dilation-level all-state task into exactly the channel-level task. -/
theorem twoSidedExactChannel_channelOf_regrouped_iff
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) (M : Matrix δ δ ℂ) :
    TwoSidedExactChannel
        (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) M ↔
      TwoSidedExact F M := by
  constructor
  · intro h
    constructor
    · intro ρ hρ i
      simpa only [channelOf_regrouped_diag] using h.agree ρ hρ i
    · intro ρ hρ
      have hdiag (p : δ × δ) :
          channelOf (F.submatrix (outputRegroup δ δ εA εB) id) ρ p p =
            outcomeProb F ρ p.1 p.2 := by
        rcases p with ⟨a, b⟩
        exact channelOf_regrouped_diag F ρ a b
      simpa only [hdiag] using h.disagree ρ hρ
  · intro h
    constructor
    · intro ρ hρ i
      simpa only [channelOf_regrouped_diag] using h.agree ρ hρ i
    · intro ρ hρ
      have hdiag (p : δ × δ) :
          channelOf (F.submatrix (outputRegroup δ δ εA εB) id) ρ p p =
            outcomeProb F ρ p.1 p.2 := by
        rcases p with ⟨a, b⟩
        exact channelOf_regrouped_diag F ρ a b
      simpa only [hdiag] using h.disagree ρ hρ

/-- Every exact channel has score one.  No dilation or channel-to-unitary
identification is used. -/
theorem scorePVM_eq_one_of_twoSidedExactChannel [Nonempty δ]
    {N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ}
    {M : Matrix δ δ ℂ} (hM : IsIsometry M)
    (hex : TwoSidedExactChannel N M) : scorePVM M N = 1 := by
  have hterm (i : δ) : (N (pvmProj M i) (i, i) (i, i)).re = 1 := by
    rw [hex.agree (pvmProj M i)
      (isState_pureState (isUnitVector_pvmColumn hM i)) i]
    change ((pvmProj M i * pureState (pvmColumn M i)).trace).re = 1
    rw [trace_pvmProj_pureState, pvmColumn_inner_self hM, Complex.normSq_one]
    rfl
  simp [scorePVM, hterm, Fintype.card_ne_zero]

/-- Exact channel tasks are closed under a finite real convex combination.
The premise deliberately asks for exactness only at nonzero weights. -/
theorem twoSidedExactChannel_sum_smul
    {κ : Type*} [Fintype κ]
    (w : κ → ℝ)
    (N : κ → Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (M : Matrix δ δ ℂ) (hsum : ∑ k, w k = 1)
    (hex : ∀ k, w k ≠ 0 → TwoSidedExactChannel (N k) M) :
    TwoSidedExactChannel (∑ k, ((w k : ℂ)) • N k) M := by
  constructor
  · intro ρ hρ i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    calc
      ∑ k, (w k : ℂ) * N k ρ (i, i) (i, i) =
          ∑ k, (w k : ℂ) * (pvmProj M i * ρ).trace := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : w k = 0
        · simp [hk]
        · rw [(hex k hk).agree ρ hρ i]
      _ = (pvmProj M i * ρ).trace := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum]
        simp
  · intro ρ hρ
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : w k = 0
    · simp [hk]
    · rw [← Finset.mul_sum, (hex k hk).disagree ρ hρ, mul_zero]

end ChannelTask

section MixedTask

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable {n : ℕ}

/-- The all-input two-sided PVM task for the actual finite mixed channel with
common encoders and decoders. -/
def MixedResource.PerformsPVM
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  TwoSidedExactChannel (m.mixedChannel VA VB DA DB) M

omit [DecidableEq εA] in
/-- If the mixed score is one, every component with positive weight has
score one.  Components with zero weight are explicitly excluded. -/
theorem MixedResource.component_scorePVM_eq_one_of_pos
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M)
    (hq : scorePVM M (m.mixedChannel VA VB DA DB) = 1)
    (k : Fin n) (hk : 0 < m.weight k) :
    scorePVM M (operationalChannel (m.component k) VA VB DA DB) = 1 := by
  let q : Fin n → ℝ := fun j =>
    scorePVM M (operationalChannel (m.component j) VA VB DA DB)
  have hqle (j : Fin n) : q j ≤ 1 :=
    (scorePVM_channelOf_regrouped_mem_Icc
      (isIsometry_globalIsometry (m.component_unit j) hVA hVB hDA hDB) hM).2
  have havg : ∑ j, m.weight j * q j = 1 := by
    rw [← m.scorePVM_mixedChannel VA VB DA DB M]
    exact hq
  have hzero : ∑ j, m.weight j * (1 - q j) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, m.weight_sum, havg, sub_self]
  have hterm : m.weight k * (1 - q k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (m.weight_nonneg j) (sub_nonneg.mpr (hqle j)))).mp
      hzero k (Finset.mem_univ k)
  have : 1 - q k = 0 := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hk)
  exact (sub_eq_zero.mp this).symm

omit [DecidableEq εA] in
/-- Score one makes the actual finite common-map mixed channel exact on every
input state.  Positive components use pure score-one exactness; zero-weight
components vanish from the channel and impose no condition. -/
theorem MixedResource.performsPVM_of_scorePVM_eq_one
    [Nonempty ιA] [Nonempty ιB]
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M)
    (hq : scorePVM M (m.mixedChannel VA VB DA DB) = 1) :
    m.PerformsPVM VA VB DA DB M := by
  apply twoSidedExactChannel_sum_smul m.weight
    (fun k => operationalChannel (m.component k) VA VB DA DB) M m.weight_sum
  intro k hk
  have hkpos : 0 < m.weight k := lt_of_le_of_ne (m.weight_nonneg k) (Ne.symm hk)
  have hqk := m.component_scorePVM_eq_one_of_pos hVA hVB hDA hDB hM hq k hkpos
  apply (twoSidedExactChannel_channelOf_regrouped_iff
    (globalIsometry (m.component k) VA VB DA DB) M).2
  exact (scorePVM_eq_one_iff_twoSidedExact
    (isIsometry_globalIsometry (m.component_unit k) hVA hVB hDA hDB) hM).mp hqk

omit [DecidableEq εA] in
/-- For finite mixed resources, score one is equivalent to the
all-state two-sided PVM task. -/
theorem MixedResource.scorePVM_eq_one_iff_performsPVM
    [Nonempty ιA] [Nonempty ιB]
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    scorePVM M (m.mixedChannel VA VB DA DB) = 1 ↔
      m.PerformsPVM VA VB DA DB M := by
  constructor
  · exact m.performsPVM_of_scorePVM_eq_one hVA hVB hDA hDB hM
  · exact scorePVM_eq_one_of_twoSidedExactChannel hM

end MixedTask

section MixedSmoothness

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : WithTop ℕ∞} {n : ℕ}

omit [DecidableEq ρA] [DecidableEq εA] [DecidableEq εB] in
/-- Joint smoothness for a finite mixture with arbitrary smooth real weights,
pure components, target, and common protocol maps.  Positivity and
normalization of the weights are irrelevant to this ambient statement. -/
theorem ContDiff.scorePVM_finiteMixture_joint
    {M : E → Matrix (ιA × ιB) (ιA × ιB) ℂ}
    {w : E → Fin n → ℝ} {η : E → Fin n → (ρA × ρB → ℂ)}
    {VA : E → Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : E → Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : E → Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : E → Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hM : ContDiff ℝ r M)
    (hw : ∀ k, ContDiff ℝ r (fun x => w x k))
    (hη : ∀ k, ContDiff ℝ r (fun x => η x k))
    (hVA : ContDiff ℝ r VA) (hVB : ContDiff ℝ r VB)
    (hDA : ContDiff ℝ r DA) (hDB : ContDiff ℝ r DB) :
    ContDiff ℝ r (fun x => scorePVM (M x)
      (∑ k, ((w x k : ℂ)) • operationalChannel (η x k)
        (VA x) (VB x) (DA x) (DB x))) := by
  have heq : (fun x => scorePVM (M x)
      (∑ k, ((w x k : ℂ)) • operationalChannel (η x k)
        (VA x) (VB x) (DA x) (DB x))) =
      fun x => ∑ k, w x k * scorePVM (M x)
        (operationalChannel (η x k) (VA x) (VB x) (DA x) (DB x)) := by
    funext x
    exact scorePVM_sum_smul (M x) (w x)
      (fun k => operationalChannel (η x k) (VA x) (VB x) (DA x) (DB x))
  rw [heq]
  exact _root_.ContDiff.sum fun k _ => (hw k).mul
    (ContDiff.scorePVM_operationalChannel_joint hM (hη k) hVA hVB hDA hDB)

end MixedSmoothness

end NLQCLean
