/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.ProjectionTheorem
import NLQCLean.Bounds.FourInputConditional
import NLQCLean.Bounds.AlmostEveryFourInputs
import NLQCLean.Bounds.StrongHaarConditional
import NLQCLean.Bounds.StrongUniversalResources

/-!
# Quantitative bounds with the projection input proved

`semialgebraicProjectionTheorem` proves the unchanged external proposition
`SemialgebraicProjectionTheorem`. Supplying it to the canonical four-input
wrappers leaves exactly three explicit ordinary arguments, in this order:
`LRTTheorem44`, `SemialgebraicSmoothStratificationTheorem` and
`SemialgebraicComponentBoundTheorem`. These three contracts remain external.

Each theorem here has the same name as the four-input wrapper in the
`NLQCLean` namespace and exactly its conclusion, including the explicit
universe levels. The four-input wrappers remain available unchanged as
compatibility theorems.

The two almost-every exact impossibility conclusions have no wrapper here:
`NLQCLean.Bounds.AlmostEveryExact` proves them with no external input at all
(`ae_unitary_no_finite_exact_implementation_unconditional` and
`ae_pvm_no_finite_exact_implementation_unconditional`).
-/

namespace NLQCLean.ProvedProjection

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- The polynomial image-volume bound from the three remaining explicit inputs. -/
theorem polynomialImageVolumeBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) : PolynomialImageVolumeBound :=
  NLQCLean.polynomialImageVolumeBound_of_external hLRT semialgebraicProjectionTheorem
    hStratification hComponents

/-! ### Full-group unitary and PVM bounds -/

/-- Full-group unitary score Haar-fraction bound from the three remaining explicit inputs. -/
theorem exists_haar_fraction_constant_of_external
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
  NLQCLean.exists_haar_fraction_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Full-group universal unitary score resource bound from the three remaining explicit inputs. -/
theorem exists_universal_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.exists_universal_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Full-group universal unitary score qubit bound from the three remaining explicit inputs. -/
theorem exists_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.exists_universal_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Full-group unitary diamond bound, as Haar outer measure, from the three remaining explicit
inputs. -/
theorem exists_diamond_haar_constant_of_external
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
  NLQCLean.exists_diamond_haar_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Full-group universal diamond resource bound from the three remaining explicit inputs. -/
theorem exists_universal_diamond_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.exists_universal_diamond_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Full-group universal diamond qubit bound from the three remaining explicit inputs. -/
theorem exists_universal_diamond_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  NLQCLean.exists_universal_diamond_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM Haar bound for score reachability, from the three remaining explicit inputs. -/
theorem exists_pvm_haar_fraction_constant_of_external
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
  NLQCLean.exists_pvm_haar_fraction_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM Haar bound for worst-case joint TV, as Haar outer measure, from the three remaining explicit
inputs. -/
theorem exists_pvm_tv_haar_constant_of_external
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
  NLQCLean.exists_pvm_tv_haar_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM resource bound from the three remaining explicit inputs. -/
theorem exists_pvm_universal_resource_constant_of_external
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
  NLQCLean.exists_pvm_universal_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM qubit bound from the three remaining explicit inputs. -/
theorem exists_pvm_universal_qubit_constant_of_external
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
  NLQCLean.exists_pvm_universal_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-! ### Almost-every fixed-target bounds -/

/-- Unitary forbidden-error sequence from the three remaining explicit inputs. -/
theorem exists_ae_unitary_forbidden_error_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.exists_ae_unitary_forbidden_error_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM forbidden-error sequence from the three remaining explicit inputs. -/
theorem exists_ae_pvm_forbidden_error_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        M ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.exists_ae_pvm_forbidden_error_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- AF1 common constant and conull set for both models, from the three remaining explicit inputs. -/
theorem exists_ae_forbidden_error_constant_of_external
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
  NLQCLean.exists_ae_forbidden_error_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Resource rates and Unitary diamond resource rate/TV together, from the three remaining explicit inputs. -/
theorem exists_ae_resource_constant_of_external
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
  NLQCLean.exists_ae_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Unitary score resource rate from the three remaining explicit inputs. -/
theorem exists_ae_unitary_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.exists_ae_unitary_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Unitary diamond resource rate from the three remaining explicit inputs. -/
theorem exists_ae_diamond_resource_constant_of_external
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
  NLQCLean.exists_ae_diamond_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM score resource rate from the three remaining explicit inputs. -/
theorem exists_ae_pvm_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  NLQCLean.exists_ae_pvm_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM joint-TV resource rate from the three remaining explicit inputs. -/
theorem exists_ae_pvm_tv_resource_constant_of_external
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
  NLQCLean.exists_ae_pvm_tv_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Physical resource rates (unitary, score or diamond, pure and finite mixed) from the three remaining explicit
inputs. -/
theorem exists_ae_unitary_physical_resource_constant_of_external
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
  NLQCLean.exists_ae_unitary_physical_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Physical resource rates (PVM, score or joint TV, pure and finite mixed) from the three remaining explicit
inputs. -/
theorem exists_ae_pvm_physical_resource_constant_of_external
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
  NLQCLean.exists_ae_pvm_physical_resource_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Unitary score qubit rate from the three remaining explicit inputs. -/
theorem exists_ae_unitary_qubit_constant_of_external
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
  NLQCLean.exists_ae_unitary_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Unitary diamond qubit rate from the three remaining explicit inputs. -/
theorem exists_ae_diamond_qubit_constant_of_external
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
  NLQCLean.exists_ae_diamond_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM score qubit rate from the three remaining explicit inputs. -/
theorem exists_ae_pvm_qubit_constant_of_external
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
  NLQCLean.exists_ae_pvm_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- PVM joint-TV qubit rate from the three remaining explicit inputs. -/
theorem exists_ae_pvm_tv_qubit_constant_of_external
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
  NLQCLean.exists_ae_pvm_tv_qubit_constant_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-! ### Restricted near-SWAP Haar bounds -/

/-- Near-SWAP score Haar bound from the three remaining explicit inputs. -/
theorem exists_strongRestrictedHaarBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C :=
  NLQCLean.exists_strongRestrictedHaarBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- Near-SWAP diamond Haar bound from the three remaining explicit inputs. -/
theorem exists_strongRestrictedDiamondHaarBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C :=
  NLQCLean.exists_strongRestrictedDiamondHaarBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-! ### Universal `d²` resource and qubit bounds -/

/-- The strong resource bound from the three remaining explicit inputs. -/
theorem exists_strongUniversalResourceBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalResourceBound c :=
  NLQCLean.exists_strongUniversalResourceBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- The strong diamond resource bound from the three remaining explicit inputs. -/
theorem exists_strongUniversalDiamondResourceBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} c :=
  NLQCLean.exists_strongUniversalDiamondResourceBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- The strong qubit bound from the three remaining explicit inputs. -/
theorem exists_strongUniversalQubitBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalQubitBound b :=
  NLQCLean.exists_strongUniversalQubitBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

/-- The strong diamond qubit bound from the three remaining explicit inputs. -/
theorem exists_strongUniversalDiamondQubitBound_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} b :=
  NLQCLean.exists_strongUniversalDiamondQubitBound_of_external
    hLRT semialgebraicProjectionTheorem hStratification hComponents

end NLQCLean.ProvedProjection
