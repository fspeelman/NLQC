/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Semialgebraic.ProjectionTheorem
import NLQCLean.Bounds.HaarFractionConditional
import NLQCLean.Bounds.ResourceConditional
import NLQCLean.Bounds.DiamondConditional
import NLQCLean.Bounds.PVMResourceConditional
import NLQCLean.Bounds.AlmostEveryQubits
import NLQCLean.Bounds.StrongHaarConditional
import NLQCLean.Bounds.StrongUniversalResources

/-!
# Full-group, almost-every and near-SWAP quantitative bounds

The quantitative bounds for unitaries and two-sided PVM tasks with their
constants: Haar-fraction and resource bounds over the full group, almost-every
fixed-target rates, and the strong bounds on a neighborhood of SWAP. Each is
the corresponding `_of_imageVolumeBound` theorem applied to the polynomial
image-volume bound `DirectVolume.polynomialImageVolumeBound`, and carries the
explicit universe levels of its statement.

The almost-every exact impossibility results are in
`NLQCLean.Bounds.AlmostEveryExact`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-! ### Full-group unitary and PVM bounds -/

/-- Full-group unitary score Haar-fraction bound. -/
theorem exists_haar_fraction_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (pureReachable d K e) ∧ MeasurableSet (mixedReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (pureReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((unitaryCodimension d : ℝ) / 2))) :=
  NLQCLean.exists_haar_fraction_constant_of_imageVolumeBound
    NLQCLean.DirectVolume.polynomialImageVolumeBound

/-- Full-group universal unitary score resource bound. -/
theorem exists_universal_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_universal_resource_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Full-group universal unitary score qubit bound. -/
theorem exists_universal_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_universal_qubit_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Full-group unitary diamond bound, as Haar outer measure. -/
theorem exists_diamond_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (pureDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure (mixedDiamondReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          e ^ ((unitaryCodimension d : ℝ) / 2))) :=
  exists_diamond_haar_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Full-group universal diamond resource bound. -/
theorem exists_universal_diamond_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_universal_diamond_resource_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Full-group universal diamond qubit bound. -/
theorem exists_universal_diamond_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_universal_diamond_qubit_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM Haar bound for score reachability. -/
theorem exists_pvm_haar_fraction_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
        MeasurableSet (purePVMReachable d K e) ∧ MeasurableSet (mixedPVMReachable d K e) ∧
        unitaryHaar (Fin d × Fin d) (purePVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) ∧
        unitaryHaar (Fin d × Fin d) (mixedPVMReachable d K e) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
            e ^ ((pvmCodimension d : ℝ) / 2))) :=
  exists_pvm_haar_fraction_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM Haar bound for worst-case joint TV, as Haar outer measure. -/
theorem exists_pvm_tv_haar_constant :
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
  exists_pvm_tv_haar_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM resource bound. -/
theorem exists_pvm_universal_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_pvm_universal_resource_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM qubit bound. -/
theorem exists_pvm_universal_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_pvm_universal_qubit_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-! ### Almost-every fixed-target bounds -/

/-- Unitary forbidden-error sequence. -/
theorem exists_ae_unitary_forbidden_error_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  NLQCLean.exists_ae_unitary_forbidden_error_constant_of_imageVolumeBound
    NLQCLean.DirectVolume.polynomialImageVolumeBound

/-- PVM forbidden-error sequence. -/
theorem exists_ae_pvm_forbidden_error_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        M ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  exists_ae_pvm_forbidden_error_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- AF1 common constant and conull set for both models. -/
theorem exists_ae_forbidden_error_constant :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  exists_ae_forbidden_error_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Resource rates and Unitary diamond resource rate/TV together. -/
theorem exists_ae_resource_constant :
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
  exists_ae_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Unitary score resource rate. -/
theorem exists_ae_unitary_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_unitary_resource_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Unitary diamond resource rate. -/
theorem exists_ae_diamond_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_diamond_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM score resource rate. -/
theorem exists_ae_pvm_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_pvm_resource_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM joint-TV resource rate. -/
theorem exists_ae_pvm_tv_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_pvm_tv_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Physical resource rates (unitary, score or diamond, pure and finite mixed). -/
theorem exists_ae_unitary_physical_resource_constant :
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
  exists_ae_unitary_physical_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Physical resource rates (PVM, score or joint TV, pure and finite mixed). -/
theorem exists_ae_pvm_physical_resource_constant :
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
  exists_ae_pvm_physical_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Unitary score qubit rate. -/
theorem exists_ae_unitary_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_unitary_qubit_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- Unitary diamond qubit rate. -/
theorem exists_ae_diamond_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_diamond_qubit_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM score qubit rate. -/
theorem exists_ae_pvm_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_pvm_qubit_constant_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- PVM joint-TV qubit rate. -/
theorem exists_ae_pvm_tv_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_pvm_tv_qubit_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-! ### Restricted near-SWAP Haar bounds -/

/-- Near-SWAP score Haar bound. -/
theorem exists_strongRestrictedHaarBound :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C :=
  NLQCLean.exists_strongRestrictedHaarBound_of_imageVolumeBound
    NLQCLean.DirectVolume.polynomialImageVolumeBound

/-- Near-SWAP diamond Haar bound. -/
theorem exists_strongRestrictedDiamondHaarBound :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C :=
  exists_strongRestrictedDiamondHaarBound_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-! ### Universal `d²` resource and qubit bounds -/

/-- The strong resource bound. -/
theorem exists_strongUniversalResourceBound :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalResourceBound c :=
  NLQCLean.exists_strongUniversalResourceBound_of_imageVolumeBound
    NLQCLean.DirectVolume.polynomialImageVolumeBound

/-- The strong diamond resource bound. -/
theorem exists_strongUniversalDiamondResourceBound :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} c :=
  exists_strongUniversalDiamondResourceBound_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- The strong qubit bound. -/
theorem exists_strongUniversalQubitBound :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalQubitBound b :=
  exists_strongUniversalQubitBound_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

/-- The strong diamond qubit bound. -/
theorem exists_strongUniversalDiamondQubitBound :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} b :=
  exists_strongUniversalDiamondQubitBound_of_imageVolumeBound
    (NLQCLean.DirectVolume.polynomialImageVolumeBound)

end NLQCLean
