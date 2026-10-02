/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.RankDeficientHaarNull
import NLQCLean.Exact.PVMExactWitness

/-!
# Exactly reachable PVM basis lifts are Haar-null

For every `d ≥ 2` and every finite budget `K`, including `K = 0`, the pure and
the finite mixed exactly PVM-reachable sets of basis unitaries have unitary
Haar measure zero.

Below the charged budget floor `d² ≤ 4K` nothing is exactly reachable. Above
it, fix one floor proof. Every exactly reachable basis unitary `M` is then the
decoded output `pvmOutputDecoding d (p.eval y) = M` of one member `p` of the
finite family of extended cubic witness polynomials indexed by
`PVMReverseShape d K`, at a point `y` of its zero-leakage source. The decoding
undoes the output coordinates and takes the conjugate transpose, so the image
is `M` itself, in the right-normal orientation of the normal-volume identity.
Each evaluated polynomial is globally smooth and its full ambient derivative has
real rank at most `3d² - 2` on that source. Since `3d² - 2 + (d²)² < 2 (d²)²`
for `d ≥ 2`, the smooth rank-deficient cover theorem applies to the Borel set
`purePVMReachable d K 0`. Mixed PVM reachability coincides with pure PVM
reachability.
-/

namespace NLQCLean

open Matrix MeasureTheory

/-- For `d ≥ 2` and every budget `K`, the basis unitaries reachable with PVM score
one by a pure protocol of footprint at most `K` form a Haar-null set. -/
theorem unitaryHaar_purePVMReachable_zero {d : ℕ} (hd : 2 ≤ d) (K : ℕ) :
    unitaryHaar (Fin d × Fin d) (purePVMReachable d K 0) = 0 := by
  have hd0 : 0 < d := by omega
  by_cases hfloor : d ^ 2 ≤ 4 * K
  · exact unitaryHaar_eq_zero_of_rankDeficient_cover (ι := PVMReverseShape d K)
      (fun _ => pvmOutputDecoding d)
      (fun s => (PVMReverseBlocks.coordinateOverlapPolynomial s hd0 hfloor (PVMReverseShape.admissibleBudget_full s hd0 hfloor)).eval)
      (fun s => (PVMReverseBlocks.witnessFormat s hd0 hfloor (PVMReverseShape.admissibleBudget_full s hd0 hfloor) 0).source)
      (fun s => PVMReverseBlocks.contDiff_coordinateOverlapPolynomial_eval s hd0 hfloor)
      (fun s _ hy =>
        PVMReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le s hd0 hfloor hd hy)
      (pvmWitnessRank_add_card_sq_lt hd) (measurableSet_purePVMReachable d K 0)
      (exists_exact_pvm_witness_of_mem_purePVMReachable_zero hd0 hfloor)
  · rw [purePVMReachable_zero_eq_empty_of_not_floor hd0 hfloor]
    exact measure_empty

/-- For `d ≥ 2` and every budget `K`, the basis unitaries reachable with PVM score
one by a finite mixed resource with common local maps and footprint at most `K`
form a Haar-null set. -/
theorem unitaryHaar_mixedPVMReachable_zero {d : ℕ} (hd : 2 ≤ d) (K : ℕ) :
    unitaryHaar (Fin d × Fin d) (mixedPVMReachable d K 0) = 0 := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact unitaryHaar_purePVMReachable_zero hd K

end NLQCLean
