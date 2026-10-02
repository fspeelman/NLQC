import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.FiniteClassicalAlmostEvery

/-!
# Fixed-target rates for arbitrary original finite classical protocols

The single target-dependent threshold precedes every original resource,
quantum message, outcome, private Kraus and decoder-environment system, in
twelve independent universes. finite compression applies directly;
no reindexing to a finite-shape class or assumed model equivalence is used.
Original diamond/joint-TV error bounds imply score bounds only. Neither
operational error is claimed to be preserved by component/outcome selection.
-/

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory

/-- All four pure/common-map mixed score classes, and their original
unitary-diamond or joint-label-TV variants, with arbitrary original systems.
This predicate contains no external premise or representation hypothesis. -/
def AllFiniteClassicalLogBound (T : unitaryGroup (Fin d × Fin d) ℂ)
    (K : ℕ) (ε C : ℝ) : Prop :=
  ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
    (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
    (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
    [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
    [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
  (∀ P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB,
    (P.HasQuantumFootprint K →
      (1 - ε ≤ scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          P.operationalChannel ∨
        diamondError P.operationalChannel
          (adConj (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ≤ ε) →
      Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
    (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m K →
      (1 - ε ≤ scoreU (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          (P.mixedOperationalChannel m) ∨
        diamondError (P.mixedOperationalChannel m)
          (adConj (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ≤ ε) →
      Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10)) ∧
  (∀ P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB,
    (P.HasQuantumFootprint K →
      (1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          P.operationalChannel ∨
        pvmTVError (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          P.operationalChannel ≤ ε) →
      Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
    (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m K →
      (1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          (P.mixedOperationalChannel m) ∨
        pvmTVError (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          (P.mixedOperationalChannel m) ≤ ε) →
      Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10))

/-- One universal constant and one threshold at each almost-every fixed
target serve every original finite architecture and all eight accuracy
predicates. Budget zero is included, not excluded by an extra premise. -/
theorem exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
        ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          AllFiniteClassicalLogBound.{u₁, u₂, u₃, u₄, u₅, u₆,
            u₇, u₈, u₉, u₁₀, u₁₁, u₁₂} T K ε C := by
  obtain ⟨c, hc, hae⟩ :=
    exists_ae_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨16 / c ^ 2, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by omega
  filter_upwards [hae d hd] with T hT
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hT
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro K ε hε hsmall
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hbound := hcharged (4 * d ^ 4 * K ^ 5) ε hε hsmall
  have hunitary (hreach : T ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (16 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound.1 hreach
  have hpvm (hreach : T ∈ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (16 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound.2.2.1 hreach
  intro ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  constructor
  · intro P
    constructor
    · intro hK haccuracy
      apply hunitary
      rcases haccuracy with hscore | herror
      · exact P.mem_pureReachable_of_quantumFootprint T hd0 hK hscore
      · exact P.mem_pureReachable_of_quantumFootprint_diamondError T hd0 hK herror
    · intro n m hK haccuracy
      apply hunitary
      rcases haccuracy with hscore | herror
      · exact P.mem_pureReachable_of_mixedQuantumFootprint m T hd0 hK hscore
      · exact P.mem_pureReachable_of_mixedQuantumFootprint_diamondError m T hd0 hK herror
  · intro P
    constructor
    · intro hK haccuracy
      apply hpvm
      rcases haccuracy with hscore | herror
      · exact P.mem_purePVMReachable_of_quantumFootprint T hd0 hK hscore
      · exact P.mem_purePVMReachable_of_quantumFootprint_pvmTVError T hd0 hK herror
    · intro n m hK haccuracy
      apply hpvm
      rcases haccuracy with hscore | herror
      · exact P.mem_purePVMReachable_of_mixedQuantumFootprint m T hd0 hK hscore
      · exact P.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError m T hd0 hK herror

/-- Applied arbitrary-register bounds retain exactly the existing three
geometry arguments. No finite/Borel instrument contract is an extra premise. -/
theorem exists_ae_arbitrary_finite_classical_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
        ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          AllFiniteClassicalLogBound.{u₁, u₂, u₃, u₄, u₅, u₆,
            u₇, u₈, u₉, u₁₀, u₁₁, u₁₂} T K ε C :=
  exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication
