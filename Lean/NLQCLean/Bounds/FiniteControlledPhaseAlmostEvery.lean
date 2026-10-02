import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.ControlledPhaseAlmostEvery
import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression

/-!
# Almost-every controlled-phase rates for finite classical instruments

The pure and common-map finite-mixed compression theorems transfer
the original target score to a charged protocol of footprint `16 Kq⁵`.
Diamond accuracy is used only to obtain that score; no operational-error
preservation is asserted for outcome or component selection. All classical
alphabets and original resource/private/environment registers remain finite
and arbitrary. Standard-Borel alphabets and shared randomness are not covered.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory ClassicalCommunication

/-- Squaring the charged lower bound after the fifth-power footprint
transfer gives the tenth-power logarithm estimate, with its exact coefficient. -/
theorem log_le_tenth_power_of_charged_sqrt_lower_bound {c L : ℝ} {Kq : ℕ}
    (hc : 0 < c) (hL : 0 ≤ L)
    (hbound : c * Real.sqrt L ≤ 16 * (Kq : ℝ) ^ 5) :
    L ≤ (256 / c ^ 2) * (Kq : ℝ) ^ 10 := by
  have hsquare := pow_le_pow_left₀ (by positivity) hbound 2
  rw [mul_pow, Real.sq_sqrt hL] at hsquare
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < c ^ 2)).mpr
  calc
    L * c ^ 2 = c ^ 2 * L := by ring
    _ ≤ (16 * (Kq : ℝ) ^ 5) ^ 2 := hsquare
    _ = 256 * (Kq : ℝ) ^ 10 := by ring

/-- One constant precedes the fixed phase; its small-error threshold precedes
all quantum budgets, errors, finite architectures and protocols.
Pure and common-map mixed score and diamond hypotheses share this threshold. -/
theorem exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂),
        ∀ [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
          [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB],
        ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
          [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
        ∀ P : FiniteClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB ηA ηB (Fin 2) (Fin 2) εA εB,
        (P.HasQuantumFootprint Kq →
          (1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (diamondError P.operationalChannel (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10)) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          (1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (diamondError (P.mixedOperationalChannel m) (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10)) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨256 / c ^ 2, by positivity, ?_⟩
  filter_upwards [hae] with θ hθ
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hθ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro Kq ε hε hε₀ ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have hε1 : ε ≤ 1 := by linarith
  have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg ((one_le_div₀ hε).mpr hε1)
  have htransfer (hreach : controlledPhaseTarget θ ∈ pureReachable 2 (2 ^ 4 * Kq ^ 5) ε) :
      Real.log (1 / ε) ≤ (256 / c ^ 2) * (Kq : ℝ) ^ 10 := by
    apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL
    have h := (hcharged (2 ^ 4 * Kq ^ 5) ε hε hε₀).1 hreach
    simpa only [show 2 ^ 4 = (16 : ℕ) by norm_num,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  refine ⟨?_, ?_⟩
  · intro hK
    exact ⟨fun hs => htransfer
      (P.mem_pureReachable_of_quantumFootprint (controlledPhaseTarget θ) (by decide) hK hs),
      fun he => htransfer
        (P.mem_pureReachable_of_quantumFootprint_diamondError
          (controlledPhaseTarget θ) (by decide) hK he)⟩
  · intro n m hK
    exact ⟨fun hs => htransfer
      (P.mem_pureReachable_of_mixedQuantumFootprint m (controlledPhaseTarget θ) (by decide) hK hs),
      fun he => htransfer
        (P.mem_pureReachable_of_mixedQuantumFootprint_diamondError
          m (controlledPhaseTarget θ) (by decide) hK he)⟩

/-- The finite-classical applied logarithm bound. No arithmetic, instrument or
compression contract is assumed. -/
theorem exists_ae_finiteControlledPhase_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂),
        ∀ [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
          [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB],
        ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
          [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
        ∀ P : FiniteClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB ηA ηB (Fin 2) (Fin 2) εA εB,
        (P.HasQuantumFootprint Kq →
          (1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (diamondError P.operationalChannel (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10)) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          (1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (diamondError (P.mixedOperationalChannel m) (adConj (controlledPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10)) :=
  exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean
