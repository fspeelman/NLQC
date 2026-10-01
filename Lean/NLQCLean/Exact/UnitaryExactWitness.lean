/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Approx.ReachableWitnessCover
import NLQCLean.Approx.PolynomialWitnessFamily

/-!
# Exact unitary witnesses on the zero-leakage polynomial source

At error zero, every pure or finite mixed reachable unitary is exactly the
decoded image of a point of the zero-leakage source of one member of the finite
family of polynomial witness maps indexed by `ReverseShape d K`. The decoding
is the inverse of the Frobenius-isometric output coordinates.

The differentiated map is the evaluated cubic overlap extension
`coordinateOverlapPolynomial`, globally smooth, whose full ambient derivative
(not merely its restriction to tangent directions of the source) has real rank
at most `4d² - 3` at every point of the zero-leakage source. For `d ≥ 2` this
rank plus the real dimension `(d²)²` of the Hermitian matrices is strictly
below `2(d²)²`, the real dimension of the bipartite matrix space.

No budget premise `1 ≤ K` is used: for small budgets the finite family is
simply smaller, possibly empty.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius _root_.ContDiff

namespace ReverseBlocks

variable {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d)

/-- The evaluated cubic witness polynomial is globally smooth. -/
theorem contDiff_coordinateOverlapPolynomial_eval :
    ContDiff ℝ ∞ (coordinateOverlapPolynomial s hd).eval := by
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  exact contDiff_coordinateOverlap s hd

/-- On the zero-leakage source the error term of the ambient rank-plus-error
decomposition vanishes, so the full ambient derivative itself has real rank at
most `4d² - 3`. -/
theorem finrank_range_fderiv_coordinateOverlapPolynomial_le (hd2 : 2 ≤ d)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd 0).source) :
    Module.finrank ℝ
        (LinearMap.range (fderiv ℝ (coordinateOverlapPolynomial s hd).eval x).toLinearMap) ≤
      4 * d ^ 2 - 3 := by
  obtain ⟨T, R, he, hT, _, hR⟩ := witnessFormat_ambient_rank_error s hd hd2 le_rfl hx
  have hR0 : R = 0 := norm_le_zero_iff.mp (by simpa using hR)
  rw [he, hR0, add_zero]
  exact hT

end ReverseBlocks

/-- Every exactly reachable pure unitary is the decoded polynomial output at a
point of one zero-leakage witness source. -/
theorem exists_exact_witness_of_mem_pureReachable_zero {d K : ℕ} (hd : 0 < d) :
    ∀ U ∈ pureReachable d K 0, ∃ s : ReverseShape d K,
      ∃ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
        (overlapOutputCoordinates d).symm
            ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x) =
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  intro U hU
  have hc := pureReachable_subset_witnessTargets hd le_rfl zero_lt_one hU
  simp only [mul_zero, Real.sqrt_zero] at hc
  obtain ⟨s, x, hx, hdist⟩ := Set.mem_iUnion.mp hc
  refine ⟨s, x, hx, ?_⟩
  rw [dist_le_zero] at hdist
  rw [← hdist, LinearEquiv.symm_apply_apply]

/-- Finite mixed exact reachability has the same exact witnesses. -/
theorem exists_exact_witness_of_mem_mixedReachable_zero {d K : ℕ} (hd : 0 < d) :
    ∀ U ∈ mixedReachable d K 0, ∃ s : ReverseShape d K,
      ∃ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
        (overlapOutputCoordinates d).symm
            ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x) =
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  rw [mixedReachable_eq_pureReachable]
  exact exists_exact_witness_of_mem_pureReachable_zero hd

/-- The exactly reachable unitaries, as matrices, lie in the finite union of
decoded images of the zero-leakage witness sources. -/
theorem coe_pureReachable_zero_subset_iUnion_witnessImage {d K : ℕ} (hd : 0 < d) :
    ((↑) : Matrix.unitaryGroup (Fin d × Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ''
        pureReachable d K 0 ⊆
      ⋃ s : ReverseShape d K,
        (fun x => (overlapOutputCoordinates d).symm
            ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x)) ''
          (ReverseBlocks.witnessFormat s hd 0).source := by
  rintro _ ⟨U, hU, rfl⟩
  obtain ⟨s, x, hx, he⟩ := exists_exact_witness_of_mem_pureReachable_zero hd U hU
  exact Set.mem_iUnion.mpr ⟨s, x, hx, he⟩

/-- For `d ≥ 2`, the unitary witness rank plus the Hermitian dimension `(d²)²`
is strictly below the real dimension `2(d²)²` of the bipartite matrix space. -/
theorem unitaryWitnessRank_add_card_sq_lt {d : ℕ} (hd : 2 ≤ d) :
    4 * d ^ 2 - 3 + Fintype.card (Fin d × Fin d) ^ 2 <
      2 * Fintype.card (Fin d × Fin d) ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  have h4 : 4 ≤ d ^ 2 := by nlinarith
  have hsq : (d * d) ^ 2 = d ^ 2 * d ^ 2 := by ring
  have hm : 4 * d ^ 2 ≤ d ^ 2 * d ^ 2 := Nat.mul_le_mul_right _ h4
  rw [hsq]
  omega

end NLQCLean
