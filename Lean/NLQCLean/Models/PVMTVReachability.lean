import NLQCLean.Models.ProjectiveTV
import NLQCLean.Models.PVMMixedReachability

/-!
# Joint-TV reachability for ordered rank-one PVMs

Reachability is the classical complement of the assertion that
every physical protocol has worst-case joint output total-variation error
strictly above `e`. Both output labels are retained, and arbitrary finite
original registers are quantified after the gap.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

/-- A strict joint-TV lower bound for every pure PVM protocol of footprint
at most `K`. -/
def PureStrictPVMTVGap {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB),
    P.HasFootprint K → e < pvmTVError M P.operationalChannel

/-- The same joint-TV gap for finite mixed resources with common local maps.
The charged quantity is the common component-rank bound times both complete
message dimensions. -/
def MixedStrictPVMTVGap {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
    ∀ R : ℕ, m.schmidtNumberLE R →
      R * Fintype.card μA * Fintype.card μB ≤ K →
      e < pvmTVError M (m.mixedChannel VA VB DA DB)

/-- Some arbitrary-finite-register pure PVM protocol has joint-TV error at
most `e`. -/
def purePVMTVReachable (d K : ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ¬ PureStrictPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e}

/-- Some finite mixed PVM resource with common local maps has joint-TV error
at most `e`. -/
def mixedPVMTVReachable (d K : ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ¬ MixedStrictPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e}

section OriginalRegisters

variable {d K n : ℕ} {e : ℝ}
variable {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
variable {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Direct TV-reachability membership for an arbitrary original pure
protocol. -/
theorem PureProtocol.mem_purePVMTVReachable
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hK : P.HasFootprint K)
    (he : pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel ≤ e) :
    M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  intro h
  exact (not_lt_of_ge he) (h ρA ρB κA κB μA μB εA εB P hK)

/-- Direct TV-reachability membership for an arbitrary finite mixed resource
and its actual common-map channel. -/
theorem MixedResource.mem_mixedPVMTVReachable (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ}
    {DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ≤ e) :
    M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  intro h
  exact (not_lt_of_ge he)
    (h ρA ρB κA κB μA μB εA εB n m VA VB DA DB
      hVA hVB hDA hDB R hR hK)

end OriginalRegisters

/-- Joint-TV accuracy implies membership in the pure PVM score-reachable
set, via the actual worst-case joint-distribution inequality. -/
theorem purePVMTVReachable_subset_purePVMReachable {d : ℕ} [NeZero d]
    (K : ℕ) (e : ℝ) :
    purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ⊆
      purePVMReachable d K e := by
  intro M hM
  by_contra hn
  apply hM
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  by_contra he
  have htv : pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel ≤ e :=
    le_of_not_gt he
  have hbridge := P.one_sub_scorePVM_le_pvmTVError
    (Matrix.mem_unitaryGroup_iff'.mp M.2)
  have hs : 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel := by
    linarith
  exact hn (P.mem_purePVMReachable hP hs)

/-- Joint-TV accuracy is converted on the actual mixed channel before using
the mixed PVM score-reachable set. -/
theorem mixedPVMTVReachable_subset_mixedPVMReachable {d : ℕ} [NeZero d]
    (K : ℕ) (e : ℝ) :
    mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ⊆
      mixedPVMReachable d K e := by
  intro M hM
  by_contra hn
  apply hM
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  by_contra he
  have htv : pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ≤ e :=
    le_of_not_gt he
  have hbridge := m.one_sub_scorePVM_le_pvmTVError hVA hVB hDA hDB
    (Matrix.mem_unitaryGroup_iff'.mp M.2)
  have hs : 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) := by
    linarith
  exact hn (m.mem_mixedPVMReachable VA VB DA DB hVA hVB hDA hDB hR hK hs)

/-- The matrix-level joint-TV phase identity, packaged for unitary-group
elements without specializing the finite outcome type. -/
theorem pvmTVError_unitary_mul_phase {δ : Type*} [Fintype δ] [DecidableEq δ]
    (M Δ : Matrix.unitaryGroup δ ℂ)
    (hΔ : (Δ : Matrix δ δ ℂ) ∈ phaseUnitaries δ)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    pvmTVError ((M * Δ : Matrix.unitaryGroup δ ℂ) : Matrix δ δ ℂ) N =
      pvmTVError (M : Matrix δ δ ℂ) N := by
  obtain ⟨z, hz, hΔeq⟩ := hΔ
  have hzsq : ∀ i, Complex.normSq (z i) = 1 := by
    intro i
    rw [Complex.normSq_eq_norm_sq, hz i]
    norm_num
  have hmul : ((M * Δ : Matrix.unitaryGroup δ ℂ) : Matrix δ δ ℂ) =
      (M : Matrix δ δ ℂ) * (Δ : Matrix δ δ ℂ) := rfl
  rw [hmul, hΔeq]
  exact pvmTVError_mul_diagonal_phase (M : Matrix δ δ ℂ) z hzsq N

set_option maxHeartbeats 800000 in
/-- Pure joint-TV reachability is invariant under independent unit phases on
the columns of the target basis lift. -/
theorem mul_phase_mem_purePVMTVReachable_iff {d K : ℕ} {e : ℝ}
    (M Δ : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hΔ : (Δ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈
      phaseUnitaries (Fin d × Fin d)) :
    M * Δ ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ↔
      M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  constructor
  · intro h hgap
    apply h
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
    rw [pvmTVError_unitary_mul_phase M Δ hΔ]
    exact hgap ρA ρB κA κB μA μB εA εB P hP
  · intro h hgap
    apply h
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
    have hg := hgap ρA ρB κA κB μA μB εA εB P hP
    rw [pvmTVError_unitary_mul_phase M Δ hΔ] at hg
    exact hg

set_option maxHeartbeats 800000 in
/-- Mixed joint-TV reachability with common maps has the same independent
column-phase invariance. -/
theorem mul_phase_mem_mixedPVMTVReachable_iff {d K : ℕ} {e : ℝ}
    (M Δ : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hΔ : (Δ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈
      phaseUnitaries (Fin d × Fin d)) :
    M * Δ ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e ↔
      M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e := by
  constructor
  · intro h hgap
    apply h
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      n m VA VB DA DB hVA hVB hDA hDB R hR hK
    rw [pvmTVError_unitary_mul_phase M Δ hΔ]
    exact hgap ρA ρB κA κB μA μB εA εB n m VA VB DA DB
      hVA hVB hDA hDB R hR hK
  · intro h hgap
    apply h
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      n m VA VB DA DB hVA hVB hDA hDB R hR hK
    have hg := hgap ρA ρB κA κB μA μB εA εB n m VA VB DA DB
      hVA hVB hDA hDB R hR hK
    rw [pvmTVError_unitary_mul_phase M Δ hΔ] at hg
    exact hg

end NLQCLean
