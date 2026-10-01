/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Bounds.AlmostEveryPhysical
import NLQCLean.Exact.UnitaryWitnessHaar
import NLQCLean.Exact.PVMWitnessHaar

/-!
# Almost every target has no finite exact implementation

For every `d ≥ 2`, the four exactly reachable sets (pure and finite mixed,
unitary score and PVM score) are Haar-null for every finite budget `K`. This
follows from vector-valued Sard applied to the normal thickening of the smooth
zero-leakage witness maps. A countable intersection over budgets then gives a
single conull set of targets lying outside every exactly reachable set.

Feeding this all-budgets event into the physical derivations of
`NLQCLean.Bounds.AlmostEveryPhysical` yields the complete almost-every exact
impossibility conclusions, with no hypotheses: arbitrary finite original
registers in eight independent universes, pure protocols and finite mixed
resources with common local maps, both charged messages, nonimplementation,
and positive normalized diamond error (unitary channels) or positive
worst-case joint-TV error (ordered two-sided PVM tasks).

No external geometric proposition is used. The earlier conditional theorems
`ae_unitary_no_finite_exact_implementation` and
`ae_pvm_no_finite_exact_implementation`, and their four-input wrappers
`ae_unitary_no_finite_exact_implementation_of_external` and
`ae_pvm_no_finite_exact_implementation_of_external`, are kept unchanged.

## Main results

* `ae_not_mem_reachable_zero_unconditional`: for almost every target, no
  finite budget reaches score error zero, in any of the four reachability
  models.
* `ae_unitary_no_finite_exact_implementation_unconditional`: for almost every
  fixed unitary, no finite budget admits an exact pure or finite mixed
  implementation on any finite registers.
* `ae_pvm_no_finite_exact_implementation_unconditional`: for almost every fixed
  basis lift, no finite budget admits a pure or finite mixed protocol on any
  finite registers performing the ordered two-sided PVM task exactly.

The suffix `_unconditional` separates these names from the conditional
theorems with the same stem. The three theorems above have no premises; the
dimension condition `2 ≤ d` is part of each statement.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory

/-- For every `d ≥ 2` and almost every target, no finite budget reaches score
error zero, for pure and finite mixed unitary reachability and for pure and
finite mixed PVM reachability. The conull set is independent of the budget. -/
theorem ae_not_mem_reachable_zero_unconditional :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      T ∉ purePVMReachable d K 0 ∧ T ∉ mixedPVMReachable d K 0 := by
  intro d hd
  refine ae_all_iff.mpr fun K => ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (unitaryHaar_pureReachable_zero hd K),
    measure_eq_zero_iff_ae_notMem.mp (unitaryHaar_mixedReachable_zero hd K),
    measure_eq_zero_iff_ae_notMem.mp (unitaryHaar_purePVMReachable_zero hd K),
    measure_eq_zero_iff_ae_notMem.mp (unitaryHaar_mixedPVMReachable_zero hd K)]
    with T h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- For almost every fixed unitary, no finite budget admits an exact pure or finite
mixed implementation on any finite registers: the channel differs from `Ad_T`,
equivalently its normalized diamond error is positive. No hypotheses. -/
theorem ae_unitary_no_finite_exact_implementation_unconditional :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
        (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
          P.HasFootprint K →
          P.operationalChannel ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ))) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix (Fin d × εA) (κA × μB) ℂ) (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          m.mixedChannel VA VB DA DB ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ))) :=
  ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable fun d hd =>
    (ae_not_mem_reachable_zero_unconditional d hd).mono fun _ hT K => ⟨(hT K).1, (hT K).2.1⟩

/-- For almost every fixed basis lift, no finite budget admits a pure or finite mixed
protocol on any finite registers performing the two-sided ordered PVM task exactly;
equivalently its worst-case joint-TV error is positive. No hypotheses. -/
theorem ae_pvm_no_finite_exact_implementation_unconditional :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      M ∉ purePVMReachable d K 0 ∧ M ∉ mixedPVMReachable d K 0 ∧
      ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
        (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
            (Fin d × Fin d) (Fin d × Fin d) εA εB,
          P.HasFootprint K →
          ¬ P.PerformsPVM (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
          (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          ¬ m.PerformsPVM VA VB DA DB (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :=
  ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable fun d hd =>
    (ae_not_mem_reachable_zero_unconditional d hd).mono fun _ hM K => ⟨(hM K).2.2.1, (hM K).2.2.2⟩

end NLQCLean
