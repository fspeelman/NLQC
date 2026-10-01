/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.PolynomialImageVolumeFourInputs
import NLQCLean.Bounds.HaarFractionConditional
import NLQCLean.Bounds.ResourceConditional
import NLQCLean.Bounds.DiamondConditional
import NLQCLean.Bounds.PVMResourceConditional

/-!
# Quantitative unitary and PVM bounds from four external inputs

Each theorem has the same conclusion as the corresponding six-input
`*_of_lrt44_and_textbook` theorem, with only
`LRTTheorem44`, `SemialgebraicProjectionTheorem`,
`SemialgebraicSmoothStratificationTheorem` and
`SemialgebraicComponentBoundTheorem`. The existing geometry-conditional
theorems are applied to the four-input geometry derivation.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

theorem exists_haar_fraction_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_haar_fraction_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

theorem exists_universal_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_universal_resource_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

theorem exists_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_universal_qubit_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

theorem exists_diamond_haar_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_diamond_haar_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

theorem exists_universal_diamond_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_universal_diamond_resource_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

theorem exists_universal_diamond_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_universal_diamond_qubit_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM Haar bound for score reachability, from the four explicit inputs. -/
theorem exists_pvm_haar_fraction_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_pvm_haar_fraction_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM Haar bound for worst-case joint TV, as Haar outer measure, from the four explicit inputs. -/
theorem exists_pvm_tv_haar_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_pvm_tv_haar_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM resource bound from the four explicit inputs. -/
theorem exists_pvm_universal_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_pvm_universal_resource_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM qubit bound from the four explicit inputs. -/
theorem exists_pvm_universal_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_pvm_universal_qubit_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

end NLQCLean
