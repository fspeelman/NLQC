/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM

/-!
# Quantitative result types with three external inputs

The semialgebraic projection proposition is proved by
`NLQCLean.semialgebraicProjectionTheorem`. Each theorem below restates a
frozen quantitative, near-SWAP or almost-every rate conclusion from
`NLQCTests.QuantitativeResultTypes` or `NLQCTests.ResultInventory`, with the
conclusion text unchanged and only the three remaining explicit premises
`LRTTheorem44`, `SemialgebraicSmoothStratificationTheorem` and
`SemialgebraicComponentBoundTheorem`. The 28 statements with a reader-facing
alias are proved by that alias; the two joint almost-every supporting exports
are proved by their `NLQCLean.ProvedProjection` wrappers. No projection
premise, helper structure or typeclass argument appears. The two almost-every
exact impossibility conclusions need no external input at all; their
premise-free types are frozen in `NLQCTests.ExactHaarResultTypes`.
-/

namespace NLQCTests.ReducedInputResultTypes

open Matrix MeasureTheory
open NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-! ### Closed projection proof -/

/--
info: 'NLQCLean.semialgebraicProjectionTheorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.semialgebraicProjectionTheorem

/-! ### Public alias types -/

#check @NLQCLean.Results.Unitary.exists_full_group_score_haar_bound
#check @NLQCLean.Results.Unitary.exists_full_group_resource_bound
#check @NLQCLean.Results.Unitary.exists_full_group_qubit_bound
#check @NLQCLean.Results.Unitary.exists_full_group_diamond_haar_bound
#check @NLQCLean.Results.Unitary.exists_full_group_diamond_resource_bound
#check @NLQCLean.Results.Unitary.exists_full_group_diamond_qubit_bound
#check @NLQCLean.Results.PVM.exists_full_group_score_haar_bound
#check @NLQCLean.Results.PVM.exists_full_group_tv_haar_bound
#check @NLQCLean.Results.PVM.exists_universal_resource_bound
#check @NLQCLean.Results.PVM.exists_universal_qubit_bound
#check @NLQCLean.Results.Unitary.exists_ae_forbidden_error_threshold
#check @NLQCLean.Results.PVM.exists_ae_forbidden_error_threshold
#check @NLQCLean.Results.Unitary.exists_ae_resource_bound
#check @NLQCLean.Results.Unitary.exists_ae_diamond_resource_bound
#check @NLQCLean.Results.PVM.exists_ae_resource_bound
#check @NLQCLean.Results.PVM.exists_ae_tv_resource_bound
#check @NLQCLean.Results.Unitary.exists_ae_physical_resource_bound
#check @NLQCLean.Results.PVM.exists_ae_physical_resource_bound
#check @NLQCLean.Results.Unitary.exists_ae_qubit_bound
#check @NLQCLean.Results.Unitary.exists_ae_diamond_qubit_bound
#check @NLQCLean.Results.PVM.exists_ae_qubit_bound
#check @NLQCLean.Results.PVM.exists_ae_tv_qubit_bound
#check @NLQCLean.Results.Unitary.exists_restricted_haar_bound
#check @NLQCLean.Results.Unitary.exists_restricted_diamond_haar_bound
#check @NLQCLean.Results.Unitary.exists_universal_resource_bound
#check @NLQCLean.Results.Unitary.exists_universal_diamond_resource_bound
#check @NLQCLean.Results.Unitary.exists_universal_qubit_bound
#check @NLQCLean.Results.Unitary.exists_universal_diamond_qubit_bound

/-! ### Reduced-input statements -/

theorem reduced_full_group_unitary_score_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (pureReachable d K e) ∧ MeasurableSet (mixedReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (pureReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) :=
  NLQCLean.Results.Unitary.exists_full_group_score_haar_bound
    hLRT hStratification hComponents

theorem reduced_full_group_unitary_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.Unitary.exists_full_group_resource_bound
    hLRT hStratification hComponents

theorem reduced_full_group_unitary_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.Unitary.exists_full_group_qubit_bound
    hLRT hStratification hComponents

theorem reduced_full_group_unitary_diamond_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (pureDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (mixedDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) :=
  NLQCLean.Results.Unitary.exists_full_group_diamond_haar_bound
    hLRT hStratification hComponents

theorem reduced_full_group_unitary_diamond_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.Unitary.exists_full_group_diamond_resource_bound
    hLRT hStratification hComponents

theorem reduced_full_group_unitary_diamond_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.Unitary.exists_full_group_diamond_qubit_bound
    hLRT hStratification hComponents

theorem reduced_full_group_pvm_score_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (purePVMReachable d K e) ∧ MeasurableSet (mixedPVMReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (purePVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedPVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) :=
  NLQCLean.Results.PVM.exists_full_group_score_haar_bound
    hLRT hStratification hComponents

theorem reduced_full_group_pvm_tv_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure
          (purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((pvmCodimension d : ℝ) / 2))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure
          (mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((pvmCodimension d : ℝ) / 2))) :=
  NLQCLean.Results.PVM.exists_full_group_tv_haar_bound
    hLRT hStratification hComponents

theorem reduced_full_group_pvm_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.PVM.exists_universal_resource_bound
    hLRT hStratification hComponents

theorem reduced_full_group_pvm_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.PVM.exists_universal_qubit_bound
    hLRT hStratification hComponents

theorem reduced_ae_unitary_forbidden_error
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.Results.Unitary.exists_ae_forbidden_error_threshold
    hLRT hStratification hComponents

theorem reduced_ae_pvm_forbidden_error
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        M ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.Results.PVM.exists_ae_forbidden_error_threshold
    hLRT hStratification hComponents

theorem reduced_ae_joint_forbidden_error
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.ProvedProjection.exists_ae_forbidden_error_constant_of_external
    hLRT hStratification hComponents

theorem reduced_ae_joint_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.ProvedProjection.exists_ae_resource_constant_of_external
    hLRT hStratification hComponents

theorem reduced_ae_unitary_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.Unitary.exists_ae_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_unitary_diamond_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.Unitary.exists_ae_diamond_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_pvm_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.PVM.exists_ae_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_pvm_tv_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.PVM.exists_ae_tv_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_unitary_physical_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
            P.HasFootprint K →
            (1 - e ≤ scoreU (T : Matrix _ _ ℂ) P.operationalChannel ∨
              diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ)) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n)
            (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
            (DA : Matrix (Fin d × εA) (κA × μB) ℂ) (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
            IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
            ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
            (1 - e ≤ scoreU (T : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
              diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ)) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.Unitary.exists_ae_physical_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_pvm_physical_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
              (Fin d × Fin d) (Fin d × Fin d) εA εB,
            P.HasFootprint K →
            (1 - e ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel ∨
              pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n)
            (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
            (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
            (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
            IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
            ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
            (1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
              pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.Results.PVM.exists_ae_physical_resource_bound
    hLRT hStratification hComponents

theorem reduced_ae_unitary_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.Unitary.exists_ae_qubit_bound
    hLRT hStratification hComponents

theorem reduced_ae_unitary_diamond_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.Unitary.exists_ae_diamond_qubit_bound
    hLRT hStratification hComponents

theorem reduced_ae_pvm_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.PVM.exists_ae_qubit_bound
    hLRT hStratification hComponents

theorem reduced_ae_pvm_tv_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.Results.PVM.exists_ae_tv_qubit_bound
    hLRT hStratification hComponents

theorem reduced_strong_restricted_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C :=
  NLQCLean.Results.Unitary.exists_restricted_haar_bound
    hLRT hStratification hComponents

theorem reduced_strong_restricted_diamond_haar
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧
      StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C :=
  NLQCLean.Results.Unitary.exists_restricted_diamond_haar_bound
    hLRT hStratification hComponents

theorem reduced_strong_universal_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalResourceBound c :=
  NLQCLean.Results.Unitary.exists_universal_resource_bound
    hLRT hStratification hComponents

theorem reduced_strong_universal_diamond_resource
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧
      StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} c :=
  NLQCLean.Results.Unitary.exists_universal_diamond_resource_bound
    hLRT hStratification hComponents

theorem reduced_strong_universal_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalQubitBound b :=
  NLQCLean.Results.Unitary.exists_universal_qubit_bound
    hLRT hStratification hComponents

theorem reduced_strong_universal_diamond_qubits
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧
      StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} b :=
  NLQCLean.Results.Unitary.exists_universal_diamond_qubit_bound
    hLRT hStratification hComponents

/-! ### Axioms of the reduced-input statements -/

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_score_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_score_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_diamond_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_diamond_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_diamond_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_diamond_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_unitary_diamond_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_unitary_diamond_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_pvm_score_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_pvm_score_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_pvm_tv_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_pvm_tv_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_pvm_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_pvm_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_full_group_pvm_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_full_group_pvm_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_forbidden_error'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_forbidden_error

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_forbidden_error'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_forbidden_error

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_joint_forbidden_error'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_joint_forbidden_error

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_joint_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_joint_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_diamond_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_diamond_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_tv_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_tv_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_physical_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_physical_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_physical_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_physical_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_unitary_diamond_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_unitary_diamond_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_ae_pvm_tv_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_ae_pvm_tv_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_restricted_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_restricted_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_restricted_diamond_haar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_restricted_diamond_haar

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_universal_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_universal_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_universal_diamond_resource'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_universal_diamond_resource

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_universal_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_universal_qubits

/--
info: 'NLQCTests.ReducedInputResultTypes.reduced_strong_universal_diamond_qubits'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduced_strong_universal_diamond_qubits

end NLQCTests.ReducedInputResultTypes
