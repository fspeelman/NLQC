import NLQCLean.Models.PVMMixedReachability
import NLQCLean.Approx.PVMExtendedPolynomial

/-!
# Compact PVM polynomial-witness target sets

Each target is the compact projection of the eight-constraint
PVM witness source. The inverse-preimage union is defined here; the
resulting union contains all score-reachable targets.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

namespace PVMReverseBlocks

/-- Points in one compact PVM witness source attain the stated distance. -/
def witnessTargets {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (δ ρ : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ x ∈ (witnessFormat s hd hfloor δ).source,
    dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ))
      ((coordinateOverlapPolynomial s hd hfloor).eval x) ≤ ρ}

theorem continuous_coordinateOverlapPolynomial {d K : ℕ} (s : PVMReverseShape d K)
    (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    Continuous (coordinateOverlapPolynomial s hd hfloor).eval := by
  have he : (coordinateOverlapPolynomial s hd hfloor).eval = coordinateOverlap s hd hfloor :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor)
  rw [he]
  exact (contDiff_coordinateOverlap s hd hfloor).continuous

theorem isCompact_witnessTargets {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (δ ρ : ℝ) :
    IsCompact (witnessTargets s hd hfloor δ ρ) := by
  have hc : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      RealEuclidean (pvmWitnessCoordinateBudget d K) =>
        dist (overlapOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd hfloor).eval z.2)) :=
    ((overlapOutputCoordinates d).toContinuousLinearEquiv.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).dist
        ((continuous_coordinateOverlapPolynomial s hd hfloor).comp continuous_snd)
  have hi : IsCompact ((Set.univ ×ˢ (witnessFormat s hd hfloor δ).source) ∩
      {z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
          RealEuclidean (pvmWitnessCoordinateBudget d K) |
        dist (overlapOutputCoordinates d (z.1 : Matrix _ _ ℂ))
          ((coordinateOverlapPolynomial s hd hfloor).eval z.2) ≤ ρ}) :=
    (isCompact_univ.prod (isCompact_witnessFormat_source s hd hfloor δ)).inter_right
      (isClosed_le hc continuous_const)
  have hp := hi.image continuous_fst
  convert hp using 1
  ext U
  simp [witnessTargets]

theorem measurableSet_witnessTargets {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (δ ρ : ℝ) :
    MeasurableSet (witnessTargets s hd hfloor δ ρ) :=
  (isCompact_witnessTargets s hd hfloor δ ρ).isClosed.measurableSet

/-- The inverse preimage of the finite union of fixed-floor witness targets. -/
def inverseWitnessTargets {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (δ ρ : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  Inv.inv ⁻¹' ⋃ s : PVMReverseShape d K, witnessTargets s hd hfloor δ ρ

theorem inverseWitnessTargets_eq {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (δ ρ : ℝ) :
    inverseWitnessTargets hd hfloor δ ρ =
      (fun U : Matrix.unitaryGroup (Fin d × Fin d) ℂ => U⁻¹) ⁻¹'
        ⋃ s : PVMReverseShape d K, witnessTargets s hd hfloor δ ρ :=
  rfl

end PVMReverseBlocks

end NLQCLean
