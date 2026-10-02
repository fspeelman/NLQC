import NLQCLean.Approx.ReachableWitnessCover
import NLQCLean.Approx.PolynomialWitnessCoverage
import NLQCLean.Approx.PVMReachableWitnessCover
import NLQCLean.Approx.PVMWitnessJacobianBound
import NLQCLean.Bounds.PVMHaarArithmetic

/-!
# Witness families (`prop:witness`)

The witness-family statement bundled in the source's form. With `δ = √(2ε)` for unitaries and
`δ = 2√ε` for measurements, and the coordinate budget `D`:

* every reachable target lies within normalized distance `δ` (Frobenius distance `dδ`) of the
  overlap image `T̂(W_δ)` of one of the witness families, whose number is at most `e^{3D}`;
* each family `W_δ ⊆ ℝ^D` is compact, of norm exactly `√6`, and cut out by seven polynomial
  equations and one weak inequality of degree at most `100`; `T̂` is a polynomial map of degree
  at most `100` on all of `ℝ^D`;
* on `W_δ` the derivative splits as `dT̂ = A + B` with `rank A ≤ ℓ`, `‖dT̂‖ ≤ D` and
  `‖B‖ ≤ δD`, with `ℓ = 4d² − 3` for unitaries and `ℓ = 3d² − 2` for measurements; these are
  Frobenius output coordinates, so the normalized bounds are smaller by the factor `d`.
-/

namespace NLQCLean

open MeasureTheory

/-- **`prop:witness`, unitaries.** -/
theorem witnessFamilies_unitary {d K : ℕ} (hd : 2 ≤ d) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    (Fintype.card (ReverseShape d K) : ℝ) ≤ Real.exp (3 * (witnessCoordinateBudget d K : ℝ)) ∧
    pureReachable d K e ∪ mixedReachable d K e ⊆ ⋃ s : ReverseShape d K,
      ReverseBlocks.witnessTargets s (by omega) (Real.sqrt (2 * e)) (d * Real.sqrt (2 * e)) ∧
    ∀ s : ReverseShape d K,
      (ReverseBlocks.witnessFormat s (by omega) (Real.sqrt (2 * e))).numEquations = 7 ∧
      (ReverseBlocks.witnessFormat s (by omega) (Real.sqrt (2 * e))).numInequalities = 1 ∧
      IsCompact (ReverseBlocks.witnessFormat s (by omega) (Real.sqrt (2 * e))).source ∧
      (∀ x ∈ (ReverseBlocks.witnessFormat s (by omega) (Real.sqrt (2 * e))).source,
        ‖x‖ = Real.sqrt 6) ∧
      (∀ x ∈ (ReverseBlocks.witnessFormat s (by omega) (Real.sqrt (2 * e))).source,
        ∃ A B : RealEuclidean (witnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4),
          fderiv ℝ (ReverseBlocks.coordinateOverlapPolynomial s (by omega)).eval x = A + B ∧
          Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤ 4 * d ^ 2 - 3 ∧
          ‖fderiv ℝ (ReverseBlocks.coordinateOverlapPolynomial s (by omega)).eval x‖ ≤
            (witnessCoordinateBudget d K : ℝ) ∧
          ‖B‖ ≤ Real.sqrt (2 * e) * witnessCoordinateBudget d K) := by
  have hd0 : 0 < d := by omega
  refine ⟨ReverseShape.card_le_exp_coordinateBudget hd0, ?_, fun s => ⟨rfl, rfl,
    ReverseBlocks.isCompact_witnessFormat_source s hd0 _,
    fun x hx => ReverseBlocks.norm_mem_witnessFormat_source s hd0 _ hx,
    fun x hx => ReverseBlocks.witnessFormat_ambient_rank_error s hd0 hd (Real.sqrt_nonneg _) hx⟩⟩
  rintro U (hU | hU)
  · exact pureReachable_subset_witnessTargets hd0 he0 he1 hU
  · exact mixedReachable_subset_witnessTargets hd0 he0 he1 hU

/-- **`prop:witness`, measurements.** The reachable basis matrices `M` are covered through
their adjoints `M†`. -/
theorem witnessFamilies_pvm {d K : ℕ} (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2) :
    (Fintype.card (PVMReverseShape d K) : ℝ) ≤
      Real.exp (3 * (pvmWitnessCoordinateBudget d K : ℝ)) ∧
    purePVMReachable d K e ∪ mixedPVMReachable d K e ⊆
      PVMReverseBlocks.inverseWitnessTargets (by omega) hfloor (2 * Real.sqrt e)
        (2 * d * Real.sqrt e) ∧
    ∀ s : PVMReverseShape d K,
      (PVMReverseBlocks.witnessFormat s (by omega) hfloor
        (PVMReverseShape.admissibleBudget_full s (by omega) hfloor) (2 * Real.sqrt e)).numEquations = 7 ∧
      (PVMReverseBlocks.witnessFormat s (by omega) hfloor
        (PVMReverseShape.admissibleBudget_full s (by omega) hfloor) (2 * Real.sqrt e)).numInequalities = 1 ∧
      IsCompact (PVMReverseBlocks.witnessFormat s (by omega) hfloor
        (PVMReverseShape.admissibleBudget_full s (by omega) hfloor) (2 * Real.sqrt e)).source ∧
      (∀ x ∈ (PVMReverseBlocks.witnessFormat s (by omega) hfloor
        (PVMReverseShape.admissibleBudget_full s (by omega) hfloor) (2 * Real.sqrt e)).source,
        ‖x‖ = Real.sqrt 6) ∧
      (∀ x ∈ (PVMReverseBlocks.witnessFormat s (by omega) hfloor
          (PVMReverseShape.admissibleBudget_full s (by omega) hfloor) (2 * Real.sqrt e)).source,
        ∃ A B : RealEuclidean (pvmWitnessCoordinateBudget d K) →L[ℝ] RealEuclidean (2 * d ^ 4),
          fderiv ℝ (PVMReverseBlocks.coordinateOverlapPolynomial s (by omega) hfloor
            (PVMReverseShape.admissibleBudget_full s (by omega) hfloor)).eval x = A + B ∧
          Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤ 3 * d ^ 2 - 2 ∧
          ‖fderiv ℝ (PVMReverseBlocks.coordinateOverlapPolynomial s (by omega) hfloor
            (PVMReverseShape.admissibleBudget_full s (by omega) hfloor)).eval x‖ ≤
            (pvmWitnessCoordinateBudget d K : ℝ) ∧
          ‖B‖ ≤ 2 * Real.sqrt e * pvmWitnessCoordinateBudget d K) := by
  have hd0 : 0 < d := by omega
  refine ⟨PVMReverseShape.card_le_exp_coordinateBudget hd0, ?_, fun s => ⟨rfl, rfl,
    PVMReverseBlocks.isCompact_witnessFormat_source s hd0 hfloor _ _,
    fun x hx => PVMReverseBlocks.norm_mem_witnessFormat_source s hd0 hfloor _ _ hx,
    fun x hx => PVMReverseBlocks.witnessFormat_ambient_rank_error s hd0 hfloor _ hd
      (by positivity) hx⟩⟩
  rintro U (hU | hU)
  · exact purePVMReachable_subset_inv_witnessTargets hd0 hfloor he0 he1 hU
  · exact mixedPVMReachable_subset_inv_witnessTargets hd0 hfloor he0 he1 hU

end NLQCLean
