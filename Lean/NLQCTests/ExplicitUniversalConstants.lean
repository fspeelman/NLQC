/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM

/-!
# Frozen types of the explicit universal unitary and measurement constants

Each theorem restates an explicit-constant universal or near-SWAP conclusion with its full
statement and is proved by the reader-facing alias. The axiom checks confirm that no external
premise remains.
-/

namespace NLQCTests.ExplicitUniversalConstants

open Matrix MeasureTheory
open NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

theorem reference_universal_explicit :
    ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
          (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) ∧
      (MixedUniversalScore d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
          (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) :=
  NLQCLean.Results.Unitary.universal_explicit_resource_bound

theorem reference_universal_explicit_of_eight :
    ∀ (d K : ℕ), 8 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
          (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) ∧
      (MixedUniversalScore d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
          (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) :=
  NLQCLean.Results.Unitary.universal_explicit_resource_bound_of_eight

theorem reference_universal_diamond_explicit :
    ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
          (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) ∧
      (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 51)
          (Real.sqrt (Real.log (1 / e) - 420) / 46)) ≤ K) :=
  NLQCLean.Results.Unitary.universal_explicit_diamond_resource_bound

theorem reference_universal_diamond_explicit_of_eight :
    ∀ (d K : ℕ), 8 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
          (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) ∧
      (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        (d : ℝ) ^ 2 * max (1 - e) (max (Real.sqrt (Real.log (1 / e)) / 24)
          (Real.sqrt (Real.log (1 / e) - 92) / 22)) ≤ K) :=
  NLQCLean.Results.Unitary.universal_explicit_diamond_resource_bound_of_eight

theorem reference_universal_resource_explicit : StrongUniversalResourceBound (1 / 51) :=
  NLQCLean.Results.Unitary.universal_resource_bound_explicit

theorem reference_universal_diamond_resource_explicit :
    StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (1 / 51) :=
  NLQCLean.Results.Unitary.universal_diamond_resource_bound_explicit

theorem reference_universal_qubits_explicit : StrongUniversalQubitBound 6 :=
  NLQCLean.Results.Unitary.universal_qubit_bound_explicit

theorem reference_universal_diamond_qubits_explicit :
    StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} 6 :=
  NLQCLean.Results.Unitary.universal_diamond_qubit_bound_explicit

theorem reference_universal_qubits_explicit_of_three :
    ∀ (n K : ℕ), 3 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e ∨ MixedUniversalScore (2 ^ n) K e ∨
        PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e ∨
        MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e) →
        2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - 5 ≤ Real.logb 2 K :=
  NLQCLean.Results.Unitary.universal_qubit_bound_explicit_of_three

theorem reference_restricted_haar_explicit : StrongRestrictedHaarBound 336 :=
  NLQCLean.Results.Unitary.restricted_haar_bound_explicit

theorem reference_restricted_diamond_haar_explicit :
    StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} 336 :=
  NLQCLean.Results.Unitary.restricted_diamond_haar_bound_explicit

theorem reference_restricted_haar_split :
    ∀ d K : ℕ, 2 ≤ d → (d : ℝ) ^ 2 / 2 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (595 / 3 * (K : ℝ) ^ 2 + 687 / 20 * (d : ℝ) ^ 4) *
            e ^ (3 / 32 * (d : ℝ) ^ 4))) ∧
        unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ mixedReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (595 / 3 * (K : ℝ) ^ 2 + 687 / 20 * (d : ℝ) ^ 4) *
            e ^ (3 / 32 * (d : ℝ) ^ 4))) :=
  fun d K hd => NLQCLean.Results.Unitary.restricted_haar_split_bound d K hd hd

theorem reference_restricted_haar_split_of_eight :
    ∀ d K : ℕ, 8 ≤ d → (d : ℝ) ^ 2 / 2 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (595 / 3 * (K : ℝ) ^ 2 + 703 / 20 * (d : ℝ) ^ 4) *
            e ^ (7 / 16 * (d : ℝ) ^ 4))) ∧
        unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ mixedReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (595 / 3 * (K : ℝ) ^ 2 + 703 / 20 * (d : ℝ) ^ 4) *
            e ^ (7 / 16 * (d : ℝ) ^ 4))) :=
  fun d K hd => NLQCLean.Results.Unitary.restricted_haar_split_bound_of_eight d K (by omega) hd

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_explicit_of_eight' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_explicit_of_eight

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_diamond_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_diamond_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_diamond_explicit_of_eight'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_diamond_explicit_of_eight

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_resource_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_resource_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_diamond_resource_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_diamond_resource_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_qubits_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_qubits_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_diamond_qubits_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_diamond_qubits_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_universal_qubits_explicit_of_three'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_universal_qubits_explicit_of_three

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_restricted_haar_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_restricted_haar_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_restricted_diamond_haar_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_restricted_diamond_haar_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_restricted_haar_split' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_restricted_haar_split

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_restricted_haar_split_of_eight' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_restricted_haar_split_of_eight

theorem reference_pvm_universal_explicit :
    ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤
          (K : ℝ)) ∧
      (MixedPVMUniversalScore d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤
          (K : ℝ)) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤
          (K : ℝ)) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤
          (K : ℝ)) :=
  NLQCLean.Results.PVM.universal_explicit_resource_bound

theorem reference_pvm_universal_explicit_of_three :
    ∀ (d K : ℕ), 3 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤
          (K : ℝ)) ∧
      (MixedPVMUniversalScore d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤
          (K : ℝ)) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤
          (K : ℝ)) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤
          (K : ℝ)) :=
  NLQCLean.Results.PVM.universal_explicit_resource_bound_of_three

theorem reference_pvm_universal_max_explicit :
    ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e →
        1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalScore d K e →
        1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) :=
  NLQCLean.Results.PVM.universal_max_resource_bound_explicit

theorem reference_pvm_universal_qubits_explicit :
    ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 6) ≤
          Real.logb 2 K) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 6) ≤
          Real.logb 2 K) :=
  NLQCLean.Results.PVM.universal_qubit_bound_explicit

theorem reference_pvm_universal_qubits_explicit_of_two :
    ∀ (n K : ℕ), 2 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 5) ≤
          Real.logb 2 K) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 5) ≤
          Real.logb 2 K) :=
  NLQCLean.Results.PVM.universal_qubit_bound_explicit_of_two

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_pvm_universal_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_pvm_universal_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_pvm_universal_explicit_of_three' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_pvm_universal_explicit_of_three

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_pvm_universal_max_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_pvm_universal_max_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_pvm_universal_qubits_explicit' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_pvm_universal_qubits_explicit

/--
info: 'NLQCTests.ExplicitUniversalConstants.reference_pvm_universal_qubits_explicit_of_two'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reference_pvm_universal_qubits_explicit_of_two

end NLQCTests.ExplicitUniversalConstants
