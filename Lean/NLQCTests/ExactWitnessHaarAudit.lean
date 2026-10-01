/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Bounds.AlmostEveryExact

/-!
# Audit of the exact reachable-set Haar nullity

Explicit reference statements check that, for every `d ≥ 2` and every budget
`K`, including `K = 0` and budgets below the PVM floor `d² ≤ 4K`, all four
exactly reachable sets are Haar-null, and that one conull set of targets avoids
every exactly reachable set for all budgets at once. The generic smooth
rank-deficient cover theorem is checked on arbitrary witness sets. Full types
and axiom lists are frozen with `#guard_msgs`; only `propext`,
`Classical.choice` and `Quot.sound` may occur.
-/

set_option format.width 120

namespace NLQCTests.ExactWitnessHaarAudit

open Matrix MeasureTheory
open NLQCLean

/-! ## Haar nullity of the exactly reachable sets -/

theorem reference_unitaryHaar_pureReachable_zero (d K : ℕ) (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d) (pureReachable d K 0) = 0 :=
  unitaryHaar_pureReachable_zero hd K

theorem reference_unitaryHaar_mixedReachable_zero (d K : ℕ) (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d) (mixedReachable d K 0) = 0 :=
  unitaryHaar_mixedReachable_zero hd K

theorem reference_unitaryHaar_purePVMReachable_zero (d K : ℕ) (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d) (purePVMReachable d K 0) = 0 :=
  unitaryHaar_purePVMReachable_zero hd K

theorem reference_unitaryHaar_mixedPVMReachable_zero (d K : ℕ) (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d) (mixedPVMReachable d K 0) = 0 :=
  unitaryHaar_mixedPVMReachable_zero hd K

/-- The zero budget is included; no `1 ≤ K` premise is present. -/
example : unitaryHaar (Fin 2 × Fin 2) (pureReachable 2 0 0) = 0 ∧
    unitaryHaar (Fin 2 × Fin 2) (mixedReachable 2 0 0) = 0 ∧
    unitaryHaar (Fin 2 × Fin 2) (purePVMReachable 2 0 0) = 0 ∧
    unitaryHaar (Fin 2 × Fin 2) (mixedPVMReachable 2 0 0) = 0 :=
  ⟨unitaryHaar_pureReachable_zero le_rfl 0, unitaryHaar_mixedReachable_zero le_rfl 0,
    unitaryHaar_purePVMReachable_zero le_rfl 0, unitaryHaar_mixedPVMReachable_zero le_rfl 0⟩

/-- Budgets at and above the PVM floor `d² ≤ 4K` are covered as well as those below. -/
example : unitaryHaar (Fin 3 × Fin 3) (purePVMReachable 3 2 0) = 0 ∧
    unitaryHaar (Fin 3 × Fin 3) (purePVMReachable 3 3 0) = 0 ∧
    unitaryHaar (Fin 3 × Fin 3) (mixedPVMReachable 3 100 0) = 0 :=
  ⟨unitaryHaar_purePVMReachable_zero (by norm_num) 2,
    unitaryHaar_purePVMReachable_zero (by norm_num) 3,
    unitaryHaar_mixedPVMReachable_zero (by norm_num) 100⟩

/-! ## One conull set for all budgets -/

theorem reference_ae_not_mem_reachable_zero :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      T ∉ purePVMReachable d K 0 ∧ T ∉ mixedPVMReachable d K 0 :=
  ae_not_mem_reachable_zero_unconditional

/-- The exceptional set is the countable union over all budgets, and it is null. -/
example (d : ℕ) (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d) (⋃ K : ℕ, pureReachable d K 0 ∪ mixedReachable d K 0 ∪
      purePVMReachable d K 0 ∪ mixedPVMReachable d K 0) = 0 := by
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [ae_not_mem_reachable_zero_unconditional d hd] with T hT
  simp only [Set.mem_iUnion, Set.mem_union, not_exists]
  intro K h
  rcases h with ((h | h) | h) | h
  exacts [(hT K).1 h, (hT K).2.1 h, (hT K).2.2.1 h, (hT K).2.2.2 h]

/-! ## Frozen full types -/

/--
info: @unitaryHaar_pureReachable_zero : ∀ {d : ℕ}, 2 ≤ d → ∀ (K : ℕ), (unitaryHaar (Fin d × Fin d)) (pureReachable d K 0) = 0
-/
#guard_msgs (whitespace := lax) in
#check @unitaryHaar_pureReachable_zero

/--
info: @unitaryHaar_mixedReachable_zero : ∀ {d : ℕ},
  2 ≤ d → ∀ (K : ℕ), (unitaryHaar (Fin d × Fin d)) (mixedReachable d K 0) = 0
-/
#guard_msgs (whitespace := lax) in
#check @unitaryHaar_mixedReachable_zero

/--
info: @unitaryHaar_purePVMReachable_zero : ∀ {d : ℕ},
  2 ≤ d → ∀ (K : ℕ), (unitaryHaar (Fin d × Fin d)) (purePVMReachable d K 0) = 0
-/
#guard_msgs (whitespace := lax) in
#check @unitaryHaar_purePVMReachable_zero

/--
info: @unitaryHaar_mixedPVMReachable_zero : ∀ {d : ℕ},
  2 ≤ d → ∀ (K : ℕ), (unitaryHaar (Fin d × Fin d)) (mixedPVMReachable d K 0) = 0
-/
#guard_msgs (whitespace := lax) in
#check @unitaryHaar_mixedPVMReachable_zero

/--
info: ae_not_mem_reachable_zero_unconditional : ∀ (d : ℕ),
  2 ≤ d →
    ∀ᵐ (T : ↥(unitaryGroup (Fin d × Fin d) ℂ)) ∂unitaryHaar (Fin d × Fin d),
      ∀ (K : ℕ),
        T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧ T ∉ purePVMReachable d K 0 ∧ T ∉ mixedPVMReachable d K 0
-/
#guard_msgs (whitespace := lax) in
#check @ae_not_mem_reachable_zero_unconditional

/--
info: @volume_image_normalThickening_eq_zero : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [inst_5 : NormedAddCommGroup V] [inst_6 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V},
  ContDiff ℝ (↑⊤) f →
    ∀ {T : Set E} {r : ℕ},
      (∀ x ∈ T, Module.finrank ℝ ↥(↑(fderiv ℝ f x)).range ≤ r) →
        r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2 →
          volume (normalThickening L f '' T ×ˢ Set.univ) = 0
-/
#guard_msgs (whitespace := lax) in
#check @volume_image_normalThickening_eq_zero

/--
info: @unitaryHaar_eq_zero_of_rankDeficient_cover : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {E : Type u_2} {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [inst_5 : NormedAddCommGroup V] [inst_6 : NormedSpace ℝ V] {ι : Type u_4} [Countable ι] (L : ι → V ≃ₗ[ℝ] Matrix n n ℂ)
  (f : ι → E → V) (T : ι → Set E) {r : ℕ},
  (∀ (i : ι), ContDiff ℝ (↑⊤) (f i)) →
    (∀ (i : ι), ∀ x ∈ T i, Module.finrank ℝ ↥(↑(fderiv ℝ (f i) x)).range ≤ r) →
      r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2 →
        ∀ {S : Set ↥(unitaryGroup n ℂ)},
          MeasurableSet S → (∀ U ∈ S, ∃ i, ∃ x ∈ T i, (L i) (f i x) = ↑U) → (unitaryHaar n) S = 0
-/
#guard_msgs (whitespace := lax) in
#check @unitaryHaar_eq_zero_of_rankDeficient_cover

/--
info: ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable : (∀ (d : ℕ),
    2 ≤ d →
      ∀ᵐ (T : ↥(unitaryGroup (Fin d × Fin d) ℂ)) ∂unitaryHaar (Fin d × Fin d),
        ∀ (K : ℕ), T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0) →
  ∀ (d : ℕ),
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
#check @ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable

/--
info: ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable : (∀ (d : ℕ),
    2 ≤ d →
      ∀ᵐ (M : ↥(unitaryGroup (Fin d × Fin d) ℂ)) ∂unitaryHaar (Fin d × Fin d),
        ∀ (K : ℕ), M ∉ purePVMReachable d K 0 ∧ M ∉ mixedPVMReachable d K 0) →
  ∀ (d : ℕ),
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
#check @ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable

/-! ## Axiom surface -/

/-- info: 'NLQCLean.unitaryHaar_pureReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unitaryHaar_pureReachable_zero

/-- info: 'NLQCLean.unitaryHaar_mixedReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unitaryHaar_mixedReachable_zero

/-- info: 'NLQCLean.unitaryHaar_purePVMReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unitaryHaar_purePVMReachable_zero

/-- info: 'NLQCLean.unitaryHaar_mixedPVMReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unitaryHaar_mixedPVMReachable_zero

/-- info: 'NLQCLean.ae_not_mem_reachable_zero_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ae_not_mem_reachable_zero_unconditional

/-- info: 'NLQCLean.volume_image_normalThickening_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms volume_image_normalThickening_eq_zero

/-- info: 'NLQCLean.unitaryHaar_eq_zero_of_rankDeficient_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unitaryHaar_eq_zero_of_rankDeficient_cover

/-- info: 'NLQCLean.ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable

/-- info: 'NLQCLean.ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable

/-- info: 'NLQCLean.ae_unitary_no_finite_exact_implementation_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ae_unitary_no_finite_exact_implementation_unconditional

/-- info: 'NLQCLean.ae_pvm_no_finite_exact_implementation_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ae_pvm_no_finite_exact_implementation_unconditional

end NLQCTests.ExactWitnessHaarAudit
