import NLQCLean.Models.PhysicalReachability

/-!
# Pure and finite-mixed reachability coincide

Component selection preserves the original rank/message
footprint. Conversely a pure resource is a one-component mixed resource.
No bound on the local support dimension of a mixed resource is imposed.
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

/-- An arbitrary finite mixed implementation admits an equally accurate pure component. -/
theorem MixedResource.mem_pureReachable (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × eA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R K : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {e : ℝ} {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : 1 - e ≤ scoreU (U : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :
    U ∈ pureReachable d K e := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB (U : Matrix _ _ ℂ)
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  apply P.mem_pureReachable ?_ (he.trans hk)
  exact (hasFootprint_iff K (m.component k)).mpr
    ((Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hK)

end ArbitraryRegisters

/-- Finite mixed reachability, with a common local implementation on every component. -/
def mixedReachable (d K : ℕ) (e : ℝ) : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ s : Fin 8 → ℕ, ∃ n : ℕ, ∃ m : MixedResource (Fin (s 0)) (Fin (s 1)) n,
    ∃ VA : Matrix (Fin (s 2) × Fin (s 4)) (Fin d × Fin (s 0)) ℂ,
    ∃ VB : Matrix (Fin (s 3) × Fin (s 5)) (Fin d × Fin (s 1)) ℂ,
    ∃ DA : Matrix (Fin d × Fin (s 6)) (Fin (s 2) × Fin (s 5)) ℂ,
    ∃ DB : Matrix (Fin d × Fin (s 7)) (Fin (s 3) × Fin (s 4)) ℂ,
    IsIsometry VA ∧ IsIsometry VB ∧ IsIsometry DA ∧ IsIsometry DB ∧
    ∃ R : ℕ, m.schmidtNumberLE R ∧ R * s 4 * s 5 ≤ K ∧
      1 - e ≤ scoreU (U : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)}

theorem mixedReachable_subset_pureReachable (d K : ℕ) (e : ℝ) :
    mixedReachable d K e ⊆ pureReachable d K e := by
  rintro U ⟨s, n, m, VA, VB, DA, DB, hVA, hVB, hDA, hDB, R, hR, hK, he⟩
  exact m.mem_pureReachable VA VB DA DB hVA hVB hDA hDB hR
    (by simpa only [Fintype.card_fin] using hK) he

theorem pureReachable_subset_mixedReachable (d K : ℕ) (e : ℝ) :
    pureReachable d K e ⊆ mixedReachable d K e := by
  rintro U ⟨s, P, hK, he⟩
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
  · rw [m.scoreU_mixedChannel]
    simpa [m, PureProtocol.operationalChannel] using he

/-- The finite-mixed and pure targets coincide for every budget and score threshold. -/
theorem mixedReachable_eq_pureReachable (d K : ℕ) (e : ℝ) :
    mixedReachable d K e = pureReachable d K e :=
  Set.Subset.antisymm (mixedReachable_subset_pureReachable d K e)
    (pureReachable_subset_mixedReachable d K e)

theorem measurableSet_mixedReachable (d K : ℕ) (e : ℝ) : MeasurableSet (mixedReachable d K e) := by
  rw [mixedReachable_eq_pureReachable]
  exact measurableSet_pureReachable d K e

section ArbitraryRegisters

variable {d n : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Membership covers mixed protocols on arbitrary original private/register dimensions. -/
theorem MixedResource.mem_mixedReachable (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × eA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R K : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    {e : ℝ} {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (he : 1 - e ≤ scoreU (U : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :
    U ∈ mixedReachable d K e :=
  pureReachable_subset_mixedReachable d K e (m.mem_pureReachable VA VB DA DB hVA hVB hDA hDB hR hK he)

end ArbitraryRegisters
end NLQCLean
