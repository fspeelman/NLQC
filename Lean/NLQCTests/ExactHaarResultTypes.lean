/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM

/-!
# Frozen types of the unconditional almost-every exact results

The two theorems below copy the complete physical conclusions of the frozen
almost-every exact impossibility statements in `NLQCTests.QuantitativeResultTypes`
and drop only the four external premises. They are proved by the public result
aliases alone, so those aliases are callable with no geometry parameter at all.
The full alias types and their axiom lists are frozen with `#guard_msgs`; only
`propext`, `Classical.choice` and `Quot.sound` may occur.

The former four-input statements remain frozen in
`NLQCTests.QuantitativeResultTypes`, proved by the retained compatibility
wrappers.
-/

set_option format.width 120

namespace NLQCTests

open Matrix MeasureTheory
open NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-! ## Complete physical conclusions with no premises -/

theorem reference_ae_unitary_exact_impossibility_unconditional :
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
  NLQCLean.Results.Unitary.ae_no_finite_exact_implementation

theorem reference_ae_pvm_exact_impossibility_unconditional :
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
  NLQCLean.Results.PVM.ae_no_finite_exact_implementation

/-! ## Frozen full types of the public aliases -/

/--
info: Results.Unitary.ae_no_finite_exact_implementation : ∀ (d : ℕ),
  2 ≤ d →
    ∀ᵐ (T : ↥(unitaryGroup (Fin d × Fin d) ℂ)) ∂unitaryHaar (Fin d × Fin d),
      ∀ (K : ℕ),
        T ∉ pureReachable d K 0 ∧
          T ∉ mixedReachable d K 0 ∧
            ∀ (ρA : Type u_1) (ρB : Type u_2) (κA : Type u_3) (κB : Type u_4) (μA : Type u_5) (μB : Type u_6)
              (εA : Type u_7) (εB : Type u_8) [inst : Fintype ρA] [inst_1 : Fintype ρB] [inst_2 : Fintype κA]
              [inst_3 : Fintype κB] [inst_4 : Fintype μA] [inst_5 : Fintype μB] [inst_6 : Fintype εA]
              [inst_7 : Fintype εB] [inst_8 : DecidableEq ρA] [inst_9 : DecidableEq ρB] [inst_10 : DecidableEq κA]
              [inst_11 : DecidableEq κB] [inst_12 : DecidableEq μA] [inst_13 : DecidableEq μB]
              [inst_14 : DecidableEq εA] [inst_15 : DecidableEq εB],
              (∀ (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB),
                  P.HasFootprint K →
                    P.operationalChannel ≠ adConj ↑T ∧ 0 < diamondError P.operationalChannel (adConj ↑T)) ∧
                ∀ (n : ℕ) (m : MixedResource ρA ρB n) (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
                  (VB : Matrix (κB × μB) (Fin d × ρB) ℂ) (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
                  (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
                  IsIsometry VA →
                    IsIsometry VB →
                      IsIsometry DA →
                        IsIsometry DB →
                          ∀ (R : ℕ),
                            m.schmidtNumberLE R →
                              R * Fintype.card μA * Fintype.card μB ≤ K →
                                m.mixedChannel VA VB DA DB ≠ adConj ↑T ∧
                                  0 < diamondError (m.mixedChannel VA VB DA DB) (adConj ↑T)
-/
#guard_msgs (whitespace := lax) in
#check @Results.Unitary.ae_no_finite_exact_implementation

/--
info: Results.PVM.ae_no_finite_exact_implementation : ∀ (d : ℕ),
  2 ≤ d →
    ∀ᵐ (M : ↥(unitaryGroup (Fin d × Fin d) ℂ)) ∂unitaryHaar (Fin d × Fin d),
      ∀ (K : ℕ),
        M ∉ purePVMReachable d K 0 ∧
          M ∉ mixedPVMReachable d K 0 ∧
            ∀ (ρA : Type u_1) (ρB : Type u_2) (κA : Type u_3) (κB : Type u_4) (μA : Type u_5) (μB : Type u_6)
              (εA : Type u_7) (εB : Type u_8) [inst : Fintype ρA] [inst_1 : Fintype ρB] [inst_2 : Fintype κA]
              [inst_3 : Fintype κB] [inst_4 : Fintype μA] [inst_5 : Fintype μB] [inst_6 : Fintype εA]
              [inst_7 : Fintype εB] [inst_8 : DecidableEq ρA] [inst_9 : DecidableEq ρB] [inst_10 : DecidableEq κA]
              [inst_11 : DecidableEq κB] [inst_12 : DecidableEq μA] [inst_13 : DecidableEq μB]
              [inst_14 : DecidableEq εA] [inst_15 : DecidableEq εB],
              (∀ (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB),
                  P.HasFootprint K → ¬P.PerformsPVM ↑M ∧ 0 < pvmTVError (↑M) P.operationalChannel) ∧
                ∀ (n : ℕ) (m : MixedResource ρA ρB n) (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
                  (VB : Matrix (κB × μB) (Fin d × ρB) ℂ) (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
                  (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
                  IsIsometry VA →
                    IsIsometry VB →
                      IsIsometry DA →
                        IsIsometry DB →
                          ∀ (R : ℕ),
                            m.schmidtNumberLE R →
                              R * Fintype.card μA * Fintype.card μB ≤ K →
                                ¬m.PerformsPVM VA VB DA DB ↑M ∧ 0 < pvmTVError (↑M) (m.mixedChannel VA VB DA DB)
-/
#guard_msgs (whitespace := lax) in
#check @Results.PVM.ae_no_finite_exact_implementation

/-! ## Axiom surface -/

/-- info: 'NLQCLean.Results.Unitary.ae_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Results.Unitary.ae_no_finite_exact_implementation

/-- info: 'NLQCLean.Results.PVM.ae_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Results.PVM.ae_no_finite_exact_implementation

/-- info: 'NLQCTests.reference_ae_unitary_exact_impossibility_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_ae_unitary_exact_impossibility_unconditional

/-- info: 'NLQCTests.reference_ae_pvm_exact_impossibility_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_ae_pvm_exact_impossibility_unconditional

end NLQCTests
