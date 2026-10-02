import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.FiniteClassicalHaar

/-!
# Almost-every fixed-target bounds for finite-shape classical protocols

The joint charged almost-every theorem supplies one dimension-independent
constant and one small-error threshold after the fixed target and before all
budgets and errors. finite pure and common-map mixed compression
transfers all four twelve-system score classes through that same threshold.
No measurability of these classes, arbitrary-register reindexing,
standard-Borel outcomes or shared-randomness representation is assumed.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix MeasureTheory

/-- One universal constant precedes the dimension and fixed target. Almost
every target has one threshold serving every quantum budget, including zero,
and all four finite-shape unitary and joint-label PVM score classes. -/
theorem exists_ae_finite_classical_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
        ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          (T ∈ finitePureScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finiteMixedScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finitePurePVMScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finiteMixedPVMScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) := by
  obtain ⟨c, hc, hae⟩ :=
    exists_ae_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨1 / c ^ 2, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by omega
  filter_upwards [hae d hd] with T hT
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hT
  refine ⟨ε₀, hε₀pos, hε₀half, fun K ε hε hsmall => ?_⟩
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hbound := hcharged (d ^ 4 * K ^ 5) ε hε hsmall
  have hunitary (hreach : T ∈ pureReachable d (d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (1 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound.1 hreach
  have hpvm (hreach : T ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (1 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound.2.2.1 hreach
  exact ⟨fun hr => hunitary (finitePureScoreReachable_subset_pureReachable hd0 ε hr),
    fun hr => hunitary (finiteMixedScoreReachable_subset_pureReachable hd0 ε hr),
    fun hr => hpvm (finitePurePVMScoreReachable_subset_purePVMReachable hd0 ε hr),
    fun hr => hpvm (finiteMixedPVMScoreReachable_subset_purePVMReachable hd0 ε hr)⟩

/-- The finite-shape almost-every applied bound retains exactly the three
original geometry arguments. The target-dependent threshold is unchanged by
compression and still precedes all budgets, errors and finite protocols. -/
theorem exists_ae_finite_classical_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
        ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          (T ∈ finitePureScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finiteMixedScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finitePurePVMScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
          (T ∈ finiteMixedPVMScoreReachable d K ε →
            Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) :=
  exists_ae_finite_classical_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication
