/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.RankDeficientHaarNull
import NLQCLean.Exact.UnitaryExactWitness

/-!
# Exactly reachable unitaries are Haar-null

For every `d ≥ 2` and every finite budget `K`, including `K = 0`, the pure and
the finite mixed exactly reachable sets of bipartite unitaries have unitary
Haar measure zero.

Every exactly reachable unitary is the decoded output
`(overlapOutputCoordinates d).symm (p.eval x)` of one member `p` of the finite
family of cubic witness polynomials indexed by `ReverseShape d K`, at a point
`x` of its zero-leakage source. Each evaluated polynomial is globally smooth,
and its full ambient derivative has real rank at most `4d² - 3` on that source.
Since `4d² - 3 + (d²)² < 2 (d²)²` for `d ≥ 2`, the smooth rank-deficient cover
theorem applies to the Borel set `pureReachable d K 0`. Mixed reachability
coincides with pure reachability.
-/

namespace NLQCLean

open Matrix MeasureTheory

/-- For `d ≥ 2` and every budget `K`, the unitaries reachable with score one by a
pure protocol of footprint at most `K` form a Haar-null set. -/
theorem unitaryHaar_pureReachable_zero {d : ℕ} (hd : 2 ≤ d) (K : ℕ) :
    unitaryHaar (Fin d × Fin d) (pureReachable d K 0) = 0 := by
  have hd0 : 0 < d := by omega
  exact unitaryHaar_eq_zero_of_rankDeficient_cover (ι := ReverseShape d K)
    (fun _ => (overlapOutputCoordinates d).symm)
    (fun s => (ReverseBlocks.coordinateOverlapPolynomial s hd0).eval)
    (fun s => (ReverseBlocks.witnessFormat s hd0 0).source)
    (fun s => ReverseBlocks.contDiff_coordinateOverlapPolynomial_eval s hd0)
    (fun s _ hx => ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le s hd0 hd hx)
    (unitaryWitnessRank_add_card_sq_lt hd) (measurableSet_pureReachable d K 0)
    (exists_exact_witness_of_mem_pureReachable_zero hd0)

/-- For `d ≥ 2` and every budget `K`, the unitaries reachable with score one by a
finite mixed resource with common local maps and footprint at most `K` form a
Haar-null set. -/
theorem unitaryHaar_mixedReachable_zero {d : ℕ} (hd : 2 ≤ d) (K : ℕ) :
    unitaryHaar (Fin d × Fin d) (mixedReachable d K 0) = 0 := by
  rw [mixedReachable_eq_pureReachable]
  exact unitaryHaar_pureReachable_zero hd K

end NLQCLean
