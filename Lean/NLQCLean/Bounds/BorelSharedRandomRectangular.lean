import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.TwoQubitDiagonalChoi
import NLQCLean.Models.ClassicalCommunication.BorelSharedRandomness

/-!
# Rectangular diagonal gates with shared randomness

Free shared probability randomness selects actual standard-Borel protocols,
pure or with a common-map finite mixed resource, with branch-dependent
original systems; the operational channel is the measured average of the
branch channels. Local restriction to the two lowest levels commutes with this
average, so the restricted average is an actual two-qubit shared-random
protocol with the same branchwise quantum footprint, and the normalized
diamond error contracts. For almost every rectangular diagonal phase,
`log(1/ε) ≤ C Kq¹⁰` below a target threshold.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory ClassicalCommunication
open scoped Kronecker

noncomputable section

noncomputable local instance sharedRectMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance sharedRectMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (sharedRectMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance sharedRectMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance sharedRectMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance sharedRectOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance sharedRectOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace
local instance sharedRectFiniteDimensional {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : FiniteDimensional ℝ (MatrixOperation ι κ) :=
  (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
local instance sharedRectCompleteSpace {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : CompleteSpace (MatrixOperation ι κ) :=
  FiniteDimensional.complete ℝ _

section Restriction

variable {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)

/-- The fixed physical rectangular restriction, as a continuous real-linear
map of operations. -/
def rectangularRestrictionOperation :
    MatrixOperation (Fin dA × Fin dB) (Fin dA × Fin dB) →L[ℝ]
      MatrixOperation (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  operationSandwich (tensorContinuousChannels (rectangularDiagonalOutputA hA hB θ)
    (rectangularDiagonalOutputB hA hB θ))
    (adConj (twoLevelIsometry hA ⊗ₖ twoLevelIsometry hB)).toContinuousLinearMap

theorem rectangularRestrictionOperation_toLinearMap
    (Φ : MatrixOperation (Fin dA × Fin dB) (Fin dA × Fin dB)) :
    (rectangularRestrictionOperation hA hB θ Φ).toLinearMap =
      rectangularDiagonalRestrictedChannel hA hB θ Φ.toLinearMap := by
  rw [rectangularDiagonalRestrictedChannel, rectangularDiagonalDecoderChannel_eq_local_tensor]
  rfl

end Restriction

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {dA dB : ℕ} [NeZero dA] [NeZero dB]
variable {ρA ρB κA κB μA μB σA σB : α → Type*}
variable [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
variable [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
variable [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
variable [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
variable [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
variable [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
variable [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
variable [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]

/-- Restriction commutes with averaging over shared randomness. -/
theorem average_restrictRectangularDiagonal (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ)
    (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) :
    AEStronglyMeasurable (fun a => ((P a).restrictRectangularDiagonal hA hB θ).operationalChannel) μ ∧
      averageOperationalChannel μ
          (fun a => ((P a).restrictRectangularDiagonal hA hB θ).operationalChannel) =
        rectangularRestrictionOperation hA hB θ
          (averageOperationalChannel μ (fun a => (P a).operationalChannel)) := by
  have hQ : (fun a => ((P a).restrictRectangularDiagonal hA hB θ).operationalChannel) =
      fun a => rectangularRestrictionOperation hA hB θ (P a).operationalChannel := by
    funext a
    exact StandardBorelClassicalProtocol.restrictLocal_operationalChannel _ _ _ _ _ _ _ _ _ _ _
  rw [hQ]
  refine ⟨(rectangularRestrictionOperation hA hB θ).continuous.comp_aestronglyMeasurable hP, ?_⟩
  exact (rectangularRestrictionOperation hA hB θ).integral_comp_comm
    (integrable_completelyPositive_tracePreserving_family μ _ hP
      (Filter.Eventually.of_forall fun a => (P a).operationalChannel_completelyPositive)
      (Filter.Eventually.of_forall fun a => (P a).operationalChannel_tracePreserving))

/-- **Rectangular diagonal gates with shared randomness.** -/
theorem exists_ae_sharedRandomRectangularDiagonal_log_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB)),
          AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
          (∀ᵐ a ∂μ, (P a).HasQuantumFootprint Kq) →
          diamondError (averageOperationalChannel μ (fun a => (P a).operationalChannel)).toLinearMap
            (adConj (rectangularDiagonalPhase θ)) ≤ ε →
          Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10 := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨4096 / c ^ 2, by positivity, fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hθ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro Kq ε hε hε₀ α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP hK he
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  let Q := fun a => (P a).restrictRectangularDiagonal hA hB θ
  obtain ⟨hQ, havg⟩ := average_restrictRectangularDiagonal μ hA hB θ P hP
  have hKQ : ∀ᵐ a ∂μ, (Q a).HasQuantumFootprint Kq := hK
  have herr : diamondError (StandardBorelClassicalProtocol.sharedRandomOperationalChannel μ Q).toLinearMap
      (adConj ((controlledPhaseTarget (rectangularAlternatingAngleMod hA hB θ) :
        Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ ε := by
    change diamondError (averageOperationalChannel μ (fun a => (Q a).operationalChannel)).toLinearMap
      (adConj (controlledPhase (rectangularAlternatingAngleMod hA hB θ))) ≤ ε
    rw [havg, rectangularRestrictionOperation_toLinearMap,
      controlledPhase_rectangularAlternatingAngleMod hA hB θ]
    exact (diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _).trans he
  have hreach := StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError
    μ Q hQ _ (by decide) hKQ herr
  apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL
  have h := (hcharged (4 * 2 ^ 4 * Kq ^ 5) ε hε hε₀).1 hreach
  simpa only [show 4 * 2 ^ 4 = (64 : ℕ) by norm_num,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Shared-random rectangular rate. -/
theorem exists_ae_sharedRandomRectangularDiagonal_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB)),
          AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
          (∀ᵐ a ∂μ, (P a).HasQuantumFootprint Kq) →
          diamondError (averageOperationalChannel μ (fun a => (P a).operationalChannel)).toLinearMap
            (adConj (rectangularDiagonalPhase θ)) ≤ ε →
          Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10 :=
  exists_ae_sharedRandomRectangularDiagonal_log_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- Mixed branches: restriction commutes with averaging the common-map mixed
branch channels. -/
theorem average_restrictRectangularDiagonal_mixed (hA : 2 ≤ dA) (hB : 2 ≤ dB)
    (θ : Fin dA × Fin dB → ℝ)
    (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable
      (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap) μ) :
    AEStronglyMeasurable (StandardBorelClassicalProtocol.mixedBranchOperation
        (fun a => (P a).restrictRectangularDiagonal hA hB θ) m) μ ∧
      averageOperationalChannel μ (StandardBorelClassicalProtocol.mixedBranchOperation
          (fun a => (P a).restrictRectangularDiagonal hA hB θ) m) =
        rectangularRestrictionOperation hA hB θ (averageOperationalChannel μ
          (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap)) := by
  have hQ : StandardBorelClassicalProtocol.mixedBranchOperation
      (fun a => (P a).restrictRectangularDiagonal hA hB θ) m =
      fun a => rectangularRestrictionOperation hA hB θ
        ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap := by
    funext a
    apply ContinuousLinearMap.coe_injective
    rw [rectangularRestrictionOperation_toLinearMap]
    exact (P a).restrictRectangularDiagonal_mixedOperationalChannel hA hB θ (m a)
  rw [hQ]
  refine ⟨(rectangularRestrictionOperation hA hB θ).continuous.comp_aestronglyMeasurable hP, ?_⟩
  exact (rectangularRestrictionOperation hA hB θ).integral_comp_comm
    (integrable_completelyPositive_tracePreserving_family μ _ hP
      (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_completelyPositive (m a))
      (Filter.Eventually.of_forall fun a => (P a).mixedOperationalChannel_tracePreserving (m a)))

/-- **Rectangular diagonal gates with shared randomness, mixed branches.** -/
theorem exists_ae_mixedSharedRandomRectangularDiagonal_log_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB))
            (n : α → ℕ) (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
          AEStronglyMeasurable (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap) μ →
          (∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) Kq) →
          diamondError (averageOperationalChannel μ
              (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap)).toLinearMap
            (adConj (rectangularDiagonalPhase θ)) ≤ ε →
          Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10 := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨4096 / c ^ 2, by positivity, fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hθ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro Kq ε hε hε₀ α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P n m hP hK he
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  let Q := fun a => (P a).restrictRectangularDiagonal hA hB θ
  obtain ⟨hQ, havg⟩ := average_restrictRectangularDiagonal_mixed μ hA hB θ P m hP
  have hKQ : ∀ᵐ a ∂μ, (Q a).HasMixedQuantumFootprint (m a) Kq := hK
  have herr : diamondError
      (StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel μ Q m).toLinearMap
      (adConj ((controlledPhaseTarget (rectangularAlternatingAngleMod hA hB θ) :
        Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ ε := by
    change diamondError (averageOperationalChannel μ
        (StandardBorelClassicalProtocol.mixedBranchOperation Q m)).toLinearMap
      (adConj (controlledPhase (rectangularAlternatingAngleMod hA hB θ))) ≤ ε
    rw [havg, rectangularRestrictionOperation_toLinearMap,
      controlledPhase_rectangularAlternatingAngleMod hA hB θ]
    exact (diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _).trans he
  have hreach :=
    StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError
      μ Q m hQ _ (by decide) hKQ herr
  apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL
  have h := (hcharged (4 * 2 ^ 4 * Kq ^ 5) ε hε hε₀).1 hreach
  simpa only [show 4 * 2 ^ 4 = (64 : ℕ) by norm_num,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Mixed-branch shared-random rectangular rate. -/
theorem exists_ae_mixedSharedRandomRectangularDiagonal_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB))
            (n : α → ℕ) (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
          AEStronglyMeasurable (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap) μ →
          (∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) Kq) →
          diamondError (averageOperationalChannel μ
              (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap)).toLinearMap
            (adConj (rectangularDiagonalPhase θ)) ≤ ε →
          Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10 :=
  exists_ae_mixedSharedRandomRectangularDiagonal_log_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end

end NLQCLean
