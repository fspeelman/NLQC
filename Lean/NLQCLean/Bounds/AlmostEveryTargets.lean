import NLQCLean.Bounds.AlmostEveryArithmetic
import NLQCLean.Bounds.HaarFractionConditional
import NLQCLean.Models.PVMMixedReachability

/-!
# Almost every fixed unitary avoids an exponentially small forbidden error

The pure and finite-mixed score-reachable
sets of both models grow with the footprint budget and the score error.
Smaller error means a smaller reachable set. No external input is used.

First Borel–Cantelli is applied to the
geometry-conditional full-group Haar estimate. The constant `A` precedes `d`;
the budget `K₀` depends on the target. The geometric property stays explicit.
-/

namespace NLQCLean

open MeasureTheory

/-- Reachability monotonicity, unitary pure score reachability. -/
theorem pureReachable_mono {d K K' : ℕ} {e e' : ℝ} (hK : K ≤ K') (he : e ≤ e') :
    pureReachable d K e ⊆ pureReachable d K' e' := by
  rintro U ⟨s, P, hP, hs⟩
  exact ⟨s, P, HasFootprint.mono hP hK, by linarith⟩

/-- Reachability monotonicity, unitary finite-mixed score reachability. -/
theorem mixedReachable_mono {d K K' : ℕ} {e e' : ℝ} (hK : K ≤ K') (he : e ≤ e') :
    mixedReachable d K e ⊆ mixedReachable d K' e' := by
  rw [mixedReachable_eq_pureReachable, mixedReachable_eq_pureReachable]
  exact pureReachable_mono hK he

/-- Reachability monotonicity, ordered rank-one PVM pure score reachability. -/
theorem purePVMReachable_mono {d K K' : ℕ} {e e' : ℝ} (hK : K ≤ K') (he : e ≤ e') :
    purePVMReachable d K e ⊆ purePVMReachable d K' e' := by
  rintro M ⟨s, P, hP, hs⟩
  exact ⟨s, P, HasFootprint.mono hP hK, by linarith⟩

/-- Reachability monotonicity, ordered rank-one PVM finite-mixed score reachability. -/
theorem mixedPVMReachable_mono {d K K' : ℕ} {e e' : ℝ} (hK : K ≤ K') (he : e ≤ e') :
    mixedPVMReachable d K e ⊆ mixedPVMReachable d K' e' := by
  rw [mixedPVMReachable_eq_purePVMReachable, mixedPVMReachable_eq_purePVMReachable]
  exact purePVMReachable_mono hK he

/-- Unitary forbidden-error sequence, internal form: every `A ≥ (32/3)(C+1)` works for the unitary Haar constant `C`. -/
theorem exists_unitary_forbidden_error_threshold (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 32 / 3 * (C + 1) ≤ A → ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ T ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) := by
  obtain ⟨C, hC, hHaar⟩ := exists_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, fun A hA d hd => ?_⟩
  exact ae_forbiddenError_of_haar_bound (s := fun K e => pureReachable d K e)
    (by linarith) hA hd (unitaryCodimension_half_lower hd)
    (fun K hK hq e he he' => (hHaar d K hd hK hq e he he').2.2.1)

/-- Unitary forbidden-error sequence: one universal `A`, and for almost every fixed unitary target a budget
`K₀` beyond which no pure or finite mixed protocol reaches error `exp (-A K²/d²)`.
Mixed follows from the proved equality of the reachable sets. -/
theorem exists_ae_unitary_forbidden_error_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ T ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) := by
  obtain ⟨C, hC, h⟩ := exists_unitary_forbidden_error_threshold hGeom
  refine ⟨32 / 3 * (C + 1), by linarith, fun d hd => ?_⟩
  filter_upwards [h _ le_rfl d hd] with T hT
  obtain ⟨K₀, hK₀, hT⟩ := hT
  exact ⟨K₀, hK₀, fun K hK => ⟨hT K hK, by rw [mixedReachable_eq_pureReachable]; exact hT K hK⟩⟩

end NLQCLean
