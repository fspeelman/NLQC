import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.NearBellUniversal
import NLQCLean.Bounds.SwapNeighborhoodAlmostEvery
import NLQCLean.Models.PVMTVReachability

/-!
# Almost-every PVM resource rates near the Bell basis

The restricted near-Bell Haar estimate has prefactor `exp (C K²)` and exponent
`d⁴/16`, as near SWAP. First Borel–Cantelli at error `exp (-A K²/d⁴)` gives, for
the PVM of Haar-almost every basis matrix in `bellNeighborhood d`, one
target-dependent threshold below which `K ≥ c d² √log(1/e)` for every budget and
pure/common-map finite-mixed score or joint total-variation implementations.

This is the measurement conclusion of the unlabeled consequences paragraph
following `cor:universal-pvm` in the robust companion, `swap.tex`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- One universal forbidden-error exponent: almost every basis matrix in the
near-Bell ball eventually avoids pure PVM score reachability. -/
theorem exists_ae_bellNeighborhood_forbidden_error_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ M ∂unitaryHaar (Fin d × Fin d), ∀ _ : NeZero d, M ∈ bellNeighborhood d →
        ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
          M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) := by
  obtain ⟨C, hC, hbound⟩ := exists_nearBell_haar_constant_of_imageVolumeBound hGeom
  let A : ℝ := 16 * (C + 1)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A, hA, fun d hd => ?_⟩
  have : NeZero d := ⟨by omega⟩
  have htail : ∀ᵐ M ∂unitaryHaar (Fin d × Fin d),
      ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ bellNeighborhood d ∩
          purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) := by
    apply ae_exists_forall_notMem_of_le_exp_neg _ _ (d ^ 3)
    intro K hK
    have hd2K : d ^ 2 ≤ K :=
      (Nat.pow_le_pow_right (by omega) (by norm_num : 2 ≤ 3)).trans hK
    obtain ⟨-, he, hehalf⟩ := strong_forbiddenError_side_conditions hA hd hd2K
    have hK3 : (d : ℝ) ^ 3 ≤ 4 * K := by
      have : ((d ^ 3 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
      push_cast at this
      linarith [Nat.cast_nonneg (α := ℝ) K]
    refine (hbound d K hd hK3 _ he hehalf).trans ((min_le_right _ _).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    refine (strong_haar_rhs_at_forbiddenError_le le_rfl
      (show 0 < d by omega)).trans ?_
    simpa using exp_neg_sq_mul_le_exp_neg (d := 1) (K := K) (by omega)
  refine htail.mono fun M hM _ hball => ?_
  obtain ⟨K₀, hK₀, hM⟩ := hM
  exact ⟨K₀, hK₀, fun K hK h => hM K hK ⟨hball, h⟩⟩

/-- **Regional near-Bell almost-every bound.** One universal constant and one
target-dependent threshold serve every budget and the pure/common-map mixed
score and joint total-variation PVM reachable sets. -/
theorem exists_ae_bellNeighborhood_resource_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        M ∈ bellNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          (M ∈ purePVMReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ mixedPVMReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨A, hA, hae⟩ := exists_ae_bellNeighborhood_forbidden_error_constant hGeom
  have hA0 : 0 < A := by linarith
  refine ⟨1 / Real.sqrt A, by positivity, fun d _ hd => ?_⟩
  refine (hae d hd).mono fun M hM hball => ?_
  obtain ⟨K₀, -, hM⟩ := hM inferInstance hball
  let K₁ := max K₀ (d ^ 4)
  have hK₀₁ : K₀ ≤ K₁ := le_max_left _ _
  have hK₁ : (d ^ 2) ^ 2 ≤ K₁ := by
    simp [K₁, ← pow_mul]
  obtain ⟨he₀, he₀half⟩ := forbiddenError_threshold_mem hA
    (show 1 ≤ d ^ 2 by nlinarith) hK₁
  have hpow : ((d ^ 2 : ℕ) : ℝ) ^ 2 = (d : ℝ) ^ 4 := by push_cast; ring
  rw [hpow] at he₀ he₀half
  refine ⟨_, he₀, he₀half, fun K e _he hee => ?_⟩
  have hf' : ∀ K' : ℕ, K₁ ≤ K' → M ∉ purePVMReachable d K'
      (Real.exp (-(A * (K' : ℝ) ^ 2 / ((d ^ 2 : ℕ) : ℝ) ^ 2))) := by
    simpa only [hpow] using fun K' hK' => hM K' (hK₀₁.trans hK')
  have hee' : e ≤ Real.exp (-(A * (K₁ : ℝ) ^ 2 / ((d ^ 2 : ℕ) : ℝ) ^ 2)) := by
    simpa only [hpow] using hee
  have hp : M ∈ purePVMReachable d K e →
      1 / Real.sqrt A * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := fun hx => by
    simpa only [Nat.cast_pow] using resource_lower_of_forbiddenError purePVMReachable_mono hA0
      (show 0 < d ^ 2 by positivity) hf' hee' hx
  have hm : M ∈ mixedPVMReachable d K e →
      1 / Real.sqrt A * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := fun hx =>
    hp (by rwa [mixedPVMReachable_eq_purePVMReachable] at hx)
  exact ⟨hp, hm,
    fun h => hp (purePVMTVReachable_subset_purePVMReachable K e h),
    fun h => hm (mixedPVMTVReachable_subset_mixedPVMReachable K e h)⟩

/-- Regional near-Bell almost-every bound. -/
theorem exists_ae_bellNeighborhood_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        M ∈ bellNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          (M ∈ purePVMReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ mixedPVMReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_bellNeighborhood_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean
