import NLQCLean.Bounds.AlmostEveryTargets
import NLQCLean.Bounds.PVMHaarFractionConditional

/-!
# Almost every fixed PVM basis lift avoids an exponentially small forbidden error

Haar measure is
on the unitary basis lifts. Only first Borel–Cantelli is used; the finite initial
budget segment never invokes the Haar estimate. The two conull sets are intersected
once, for a fixed dimension; no family indexed by real errors is intersected.
-/

namespace NLQCLean

open MeasureTheory

/-- PVM forbidden-error sequence, internal form: every `A ≥ (32/3)(C+1)` works for the PVM Haar constant `C`. -/
theorem exists_pvm_forbidden_error_threshold (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 32 / 3 * (C + 1) ≤ A → ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ M ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) := by
  obtain ⟨C, hC, hHaar⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, fun A hA d hd => ?_⟩
  exact ae_forbiddenError_of_haar_bound (s := fun K e => purePVMReachable d K e)
    (by linarith) hA hd (pvmCodimension_half_lower hd)
    (fun K hK hq e he he' => (hHaar d K hd hK hq e he he').2.2.1)

/-- PVM forbidden-error sequence: one universal `A`, and for almost every fixed basis lift a budget `K₀`
beyond which no pure or finite mixed PVM protocol reaches score error `exp (-A K²/d²)`. -/
theorem exists_ae_pvm_forbidden_error_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ M ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        M ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        M ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) := by
  obtain ⟨C, hC, h⟩ := exists_pvm_forbidden_error_threshold hGeom
  refine ⟨32 / 3 * (C + 1), by linarith, fun d hd => ?_⟩
  filter_upwards [h _ le_rfl d hd] with M hM
  obtain ⟨K₀, hK₀, hM⟩ := hM
  exact ⟨K₀, hK₀, fun K hK =>
    ⟨hM K hK, by rw [mixedPVMReachable_eq_purePVMReachable]; exact hM K hK⟩⟩

/-- AF1 common form: one `A ≥ 1`, and for almost every matrix one `K₀`, serving the
unitary and PVM score sets, pure and finite mixed, simultaneously. -/
theorem exists_ae_forbidden_error_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ T ∂unitaryHaar (Fin d × Fin d), ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ purePVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ∧
        T ∉ mixedPVMReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) := by
  obtain ⟨CU, hCU, hU⟩ := exists_unitary_forbidden_error_threshold hGeom
  obtain ⟨CP, hCP, hP⟩ := exists_pvm_forbidden_error_threshold hGeom
  have hmU := le_max_left CU CP
  have hmP := le_max_right CU CP
  refine ⟨32 / 3 * (max CU CP + 1), by linarith, fun d hd => ?_⟩
  filter_upwards [hU (32 / 3 * (max CU CP + 1)) (by linarith) d hd,
    hP (32 / 3 * (max CU CP + 1)) (by linarith) d hd] with T hTU hTP
  obtain ⟨KU, hKU, hTU⟩ := hTU
  obtain ⟨KP, hKP, hTP⟩ := hTP
  refine ⟨max KU KP, le_max_of_le_left hKU, fun K hK => ?_⟩
  have hU' := hTU K (le_of_max_le_left hK)
  have hP' := hTP K (le_of_max_le_right hK)
  refine ⟨hU', ?_, hP', ?_⟩
  · rw [mixedReachable_eq_pureReachable]
    exact hU'
  · rw [mixedPVMReachable_eq_purePVMReachable]
    exact hP'

end NLQCLean
