import NLQCLean.Geometry.PolynomialImageVolumeFourInputs
import NLQCLean.Bounds.AlmostEveryQubits

/-!
# Almost-every fixed-target bounds from four external inputs

Each theorem has exactly the conclusion of the corresponding
geometry-conditional theorem, with only `LRTTheorem44`,
`SemialgebraicProjectionTheorem`, `SemialgebraicSmoothStratificationTheorem` and
`SemialgebraicComponentBoundTheorem` as explicit ordinary arguments, applied through
the canonical `polynomialImageVolumeBound_of_external`.
These almost-every statements remain conditional on the four inputs.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory

/-- Unitary forbidden-error sequence from the four explicit inputs. -/
theorem exists_ae_unitary_forbidden_error_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  exists_ae_unitary_forbidden_error_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM forbidden-error sequence from the four explicit inputs. -/
theorem exists_ae_pvm_forbidden_error_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        M ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  exists_ae_pvm_forbidden_error_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- AF1 common constant and conull set for both models, from the four explicit inputs. -/
theorem exists_ae_forbidden_error_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
        ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  exists_ae_forbidden_error_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Resource rates and Unitary diamond resource rate/TV together, from the four explicit inputs. -/
theorem exists_ae_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_ae_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Unitary score resource rate from the four explicit inputs. -/
theorem exists_ae_unitary_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_unitary_resource_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Unitary diamond resource rate from the four explicit inputs. -/
theorem exists_ae_diamond_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_diamond_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM score resource rate from the four explicit inputs. -/
theorem exists_ae_pvm_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_pvm_resource_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM joint-TV resource rate from the four explicit inputs. -/
theorem exists_ae_pvm_tv_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_pvm_tv_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Physical resource rates (unitary, score or diamond, pure and finite mixed) from the four explicit inputs. -/
theorem exists_ae_unitary_physical_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_ae_unitary_physical_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Physical resource rates (PVM, score or joint TV, pure and finite mixed) from the four explicit inputs. -/
theorem exists_ae_pvm_physical_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
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
  exists_ae_pvm_physical_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Unitary score qubit rate from the four explicit inputs. -/
theorem exists_ae_unitary_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_unitary_qubit_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Unitary diamond qubit rate from the four explicit inputs. -/
theorem exists_ae_diamond_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_diamond_qubit_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM score qubit rate from the four explicit inputs. -/
theorem exists_ae_pvm_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_pvm_qubit_constant
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM joint-TV qubit rate from the four explicit inputs. -/
theorem exists_ae_pvm_tv_qubit_constant_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_pvm_tv_qubit_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- Unitary exact impossibility from the four explicit inputs. -/
theorem ae_unitary_no_finite_exact_implementation_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
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
  ae_unitary_no_finite_exact_implementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

/-- PVM exact impossibility from the four explicit inputs. -/
theorem ae_pvm_no_finite_exact_implementation_of_external
    (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
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
  ae_pvm_no_finite_exact_implementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT hProjection
      hStratification hComponents)

end NLQCLean
