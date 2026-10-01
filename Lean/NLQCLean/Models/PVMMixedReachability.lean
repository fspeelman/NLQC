import NLQCLean.Models.PVMPhysicalReachability

/-!
# Pure and finite-mixed PVM reachability coincide

Affineness of the ordered PVM score selects a pure component
without changing the common local maps.  Its Schmidt rank and both message
dimensions obey the original footprint charge; the resource support remains
otherwise arbitrary.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section ArbitraryRegisters

variable {d n : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- An arbitrary finite mixed PVM implementation admits an equally accurate
pure component with the same common maps and footprint budget. -/
theorem MixedResource.mem_purePVMReachable (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R K : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {e : ℝ} {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :
    M ∈ purePVMReachable d K e := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB (M : Matrix _ _ ℂ)
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  apply P.mem_purePVMReachable ?_ (he.trans hk)
  exact (hasFootprint_iff K (m.component k)).mpr
    ((Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hK)

end ArbitraryRegisters

/-- Finite mixed PVM reachability, with one common local implementation for
all pure components of the shared resource. -/
def mixedPVMReachable (d K : ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ∃ s : Fin 8 → ℕ, ∃ n : ℕ,
    ∃ m : MixedResource (Fin (s 0)) (Fin (s 1)) n,
    ∃ VA : Matrix (Fin (s 2) × Fin (s 4)) (Fin d × Fin (s 0)) ℂ,
    ∃ VB : Matrix (Fin (s 3) × Fin (s 5)) (Fin d × Fin (s 1)) ℂ,
    ∃ DA : Matrix ((Fin d × Fin d) × Fin (s 6)) (Fin (s 2) × Fin (s 5)) ℂ,
    ∃ DB : Matrix ((Fin d × Fin d) × Fin (s 7)) (Fin (s 3) × Fin (s 4)) ℂ,
    IsIsometry VA ∧ IsIsometry VB ∧ IsIsometry DA ∧ IsIsometry DB ∧
    ∃ R : ℕ, m.schmidtNumberLE R ∧ R * s 4 * s 5 ≤ K ∧
      1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)}

theorem mixedPVMReachable_subset_purePVMReachable (d K : ℕ) (e : ℝ) :
    mixedPVMReachable d K e ⊆ purePVMReachable d K e := by
  rintro M ⟨s, n, m, VA, VB, DA, DB, hVA, hVB, hDA, hDB, R, hR, hK, he⟩
  exact m.mem_purePVMReachable VA VB DA DB hVA hVB hDA hDB hR
    (by simpa only [Fintype.card_fin] using hK) he

theorem purePVMReachable_subset_mixedPVMReachable (d K : ℕ) (e : ℝ) :
    purePVMReachable d K e ⊆ mixedPVMReachable d K e := by
  rintro M ⟨s, P, hK, he⟩
  let m : MixedResource (Fin (s 0)) (Fin (s 1)) 1 :=
    { weight := fun _ => 1
      weight_nonneg := fun _ => zero_le_one
      weight_sum := by simp
      component := fun _ => P.resource
      component_unit := fun _ => P.resource_unit }
  refine ⟨s, 1, m, P.encA, P.encB, P.decA, P.decB,
    P.encA_isometry, P.encB_isometry, P.decA_isometry, P.decB_isometry,
    schmidtRank P.resource, fun _ => le_rfl, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using (hasFootprint_iff K P.resource).mp hK
  · rw [m.scorePVM_mixedChannel]
    simpa [m, PureProtocol.operationalChannel] using he

/-- Finite mixed and pure PVM targets coincide at every footprint and score
threshold. -/
theorem mixedPVMReachable_eq_purePVMReachable (d K : ℕ) (e : ℝ) :
    mixedPVMReachable d K e = purePVMReachable d K e :=
  Set.Subset.antisymm (mixedPVMReachable_subset_purePVMReachable d K e)
    (purePVMReachable_subset_mixedPVMReachable d K e)

theorem measurableSet_mixedPVMReachable (d K : ℕ) (e : ℝ) :
    MeasurableSet (mixedPVMReachable d K e) := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact measurableSet_purePVMReachable d K e

/-- Mixed PVM reachability is invariant under independent phases on the
columns of the basis lift. -/
theorem mul_phase_mem_mixedPVMReachable_iff {d K : ℕ} {e : ℝ}
    (M Δ : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hΔ : (Δ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈
      phaseUnitaries (Fin d × Fin d)) :
    M * Δ ∈ mixedPVMReachable d K e ↔ M ∈ mixedPVMReachable d K e := by
  rw [mixedPVMReachable_eq_purePVMReachable,
    mul_phase_mem_purePVMReachable_iff M Δ hΔ]

section ArbitraryRegisters

variable {d n : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Membership covers finite mixed PVM protocols on arbitrary original
resource, private, message, and discarded-output registers. -/
theorem MixedResource.mem_mixedPVMReachable (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R K : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {e : ℝ} {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :
    M ∈ mixedPVMReachable d K e :=
  purePVMReachable_subset_mixedPVMReachable d K e
    (m.mem_purePVMReachable VA VB DA DB hVA hVB hDA hDB hR hK he)

end ArbitraryRegisters

end NLQCLean
