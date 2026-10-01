import NLQCLean.Exact.PVMScalarCriticalValues
import NLQCLean.Invariants.PVMRotationFamily
import NLQCLean.Models.ProjectiveMixedExactness

/-!
# An exactly hard ordered rank-one PVM

The union of exact-witness invariant values over all finite shapes is
null, while the explicit rotation family attains the whole interval
[1−1/D, 1]. Choose a rotation parameter whose invariant avoids the null set.
That single ordered PVM is chosen before any resource budget. No pure or finite
mixed protocol, with arbitrary finite original registers, has score one on it or
performs it exactly. There is no external mathematical premise.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- A rotation parameter whose invariant lies outside every exact-witness value. -/
theorem exists_pvmRotation_purity_not_mem {d : ℕ} (hd : 2 ≤ d) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧
      pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ (pvmRotationBasis hd s) ∉ exactPVMPurityValues d := by
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hlt : 1 - 1 / (d : ℝ) ^ 2 < 1 := by
    have : 0 < 1 / (d : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨v, hv, hvN⟩ :=
    exists_mem_Ioo_not_mem_of_volume_eq_zero (volume_exactPVMPurityValues_eq_zero d) hlt
  obtain ⟨s, hs0, hs1, hval⟩ := exists_pvmRotationBasis_purity_eq hd hv.1.le hv.2.le
  exact ⟨s, hs0, hs1, by rw [hval]; exact hvN⟩

section Exclusion

variable {d : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}

theorem PureProtocol.scorePVM_lt_one_of_pvmMeanPurity_not_mem
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hM : IsIsometry M) (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d) :
    scorePVM M P.operationalChannel < 1 :=
  lt_of_le_of_ne (P.scorePVM_mem_Icc hM).2 fun h =>
    hN (P.pvmMeanPurity_mem_of_scorePVM_eq_one hM h)

theorem PureProtocol.not_performsPVM_of_pvmMeanPurity_not_mem
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hM : IsIsometry M) (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d) :
    ¬ P.PerformsPVM M := fun h =>
  (P.scorePVM_lt_one_of_pvmMeanPurity_not_mem hM hN).ne
    ((P.scorePVM_eq_one_iff_performsPVM hM).mpr h)

theorem MixedResource.scorePVM_lt_one_of_pvmMeanPurity_not_mem {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ} {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ}
    {DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hM : IsIsometry M) (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d) :
    scorePVM M (m.mixedChannel VA VB DA DB) < 1 := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  exact lt_of_le_of_lt hk (P.scorePVM_lt_one_of_pvmMeanPurity_not_mem hM hN)

theorem MixedResource.not_performsPVM_of_pvmMeanPurity_not_mem {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ} {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ}
    {DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hM : IsIsometry M) (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d) :
    ¬ m.PerformsPVM VA VB DA DB M := fun h =>
  (m.scorePVM_lt_one_of_pvmMeanPurity_not_mem hVA hVB hDA hDB hM hN).ne
    ((m.scorePVM_eq_one_iff_performsPVM hVA hVB hDA hDB hM).mpr h)

end Exclusion

/-- No pure protocol with arbitrary finite registers performs the two-sided PVM exactly. -/
def NoFinitePurePVMImplementation {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB),
    ¬ P.PerformsPVM M

/-- No finite mixed resource with common isometric local maps performs the PVM exactly. -/
def NoFiniteMixedPVMImplementation {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
    ¬ m.PerformsPVM VA VB DA DB M

/-- For every `d ≥ 2` there is one ordered rank-one PVM,
given by a unitary basis lift, that no finite pure or finite mixed architecture
performs exactly. -/
theorem exists_pvm_no_finite_exact_implementation (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
      NoFinitePurePVMImplementation M ∧ NoFiniteMixedPVMImplementation M := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨s, hs0, hs1, hN⟩ := exists_pvmRotation_purity_not_mem hd
  have hs1' : s ≤ 1 := by linarith
  have hM := isIsometry_pvmRotationBasis hd hs0 hs1'
  refine ⟨pvmRotationBasis hd s, pvmRotationBasis_mem_unitaryGroup hd hs0 hs1', ?_, ?_⟩
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    exact P.not_performsPVM_of_pvmMeanPurity_not_mem hM hN
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n m VA VB DA DB hVA hVB hDA hDB
    exact m.not_performsPVM_of_pvmMeanPurity_not_mem hVA hVB hDA hDB hM hN

end NLQCLean
