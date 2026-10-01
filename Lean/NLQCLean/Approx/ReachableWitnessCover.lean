import NLQCLean.Models.MixedReachability
import NLQCLean.Approx.PolynomialWitnessCoverage
import NLQCLean.Geometry.PolynomialTubeConditional

/-!
# Compact witness targets cover physical reachability

Each enlarged target set is a compact projection of the actual
polynomial witness source. The finite family covers all pure and finite
mixed reachable targets. Only inclusion in these enlarged sets is asserted.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

namespace ReverseBlocks

/-- Points in the compact witness source attain the required distance bound. -/
def witnessTargets {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) (δ ρ : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ x ∈ (witnessFormat s hd δ).source,
    dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
      ((coordinateOverlapPolynomial s hd).eval x) ≤ ρ}

theorem continuous_coordinateOverlapPolynomial {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) :
    Continuous (coordinateOverlapPolynomial s hd).eval := by
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact (contDiff_coordinateOverlap s hd).continuous

theorem isCompact_witnessTargets {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) (δ ρ : ℝ) :
    IsCompact (witnessTargets s hd δ ρ) := by
  have hc : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      RealEuclidean (witnessCoordinateBudget d K) =>
        dist (overlapOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd).eval z.2)) :=
    ((overlapOutputCoordinates d).toContinuousLinearEquiv.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).dist
        ((continuous_coordinateOverlapPolynomial s hd).comp continuous_snd)
  have hi : IsCompact ((Set.univ ×ˢ (witnessFormat s hd δ).source) ∩
      {z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × RealEuclidean (witnessCoordinateBudget d K) |
        dist (overlapOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd).eval z.2) ≤ ρ}) :=
    (isCompact_univ.prod (isCompact_witnessFormat_source s hd δ)).inter_right
      (isClosed_le hc continuous_const)
  have hp := hi.image continuous_fst
  convert hp using 1
  ext U
  simp [witnessTargets]

theorem measurableSet_witnessTargets {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) (δ ρ : ℝ) :
    MeasurableSet (witnessTargets s hd δ ρ) :=
  (isCompact_witnessTargets s hd δ ρ).isClosed.measurableSet

end ReverseBlocks

set_option maxHeartbeats 800000 in
/-- Direct physical coverage, with the sharp freezing error and the original charged footprint. -/
theorem pureReachable_subset_witnessTargets {d K : ℕ} (hd : 0 < d)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    pureReachable d K e ⊆ ⋃ s : ReverseShape d K,
      ReverseBlocks.witnessTargets s hd (Real.sqrt (2 * e)) ((d : ℝ) * Real.sqrt (2 * e)) := by
  rintro U ⟨t, P, hP, hscore⟩
  have hU : IsIsometry (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := U.property.1
  obtain ⟨s, x, hx, hdist⟩ := P.exists_polynomial_witness_approximation hd
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hU hP he0 he1 hscore
  refine Set.mem_iUnion.mpr ⟨s, x, hx, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hdist

theorem mixedReachable_subset_witnessTargets {d K : ℕ} (hd : 0 < d)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    mixedReachable d K e ⊆ ⋃ s : ReverseShape d K,
      ReverseBlocks.witnessTargets s hd (Real.sqrt (2 * e)) ((d : ℝ) * Real.sqrt (2 * e)) := by
  rw [mixedReachable_eq_pureReachable]
  exact pureReachable_subset_witnessTargets hd he0 he1

end NLQCLean
