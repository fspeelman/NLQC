/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Exact.UnitaryExactWitness
import NLQCLean.Exact.PVMExactWitness

/-!
# Exact zero-error witness audit

Explicit reference statements for the unitary and PVM exact witness facts:
exact decoded coverage of zero-error reachability for every budget (including
`K = 0`), the full ambient derivative rank bounds on the zero-leakage sources,
global smoothness of the differentiated polynomial maps, the strict rank-count
inequalities, and finiteness of the witness families. Axiom printouts are
guarded so that only the standard logical axioms can occur.
-/

set_option format.width 120

namespace NLQCTests

open Matrix
open scoped _root_.ContDiff
open NLQCLean

/-! ## Unitary exact witnesses -/

theorem reference_unitary_exact_witness {d K : ℕ} (hd : 0 < d) :
    ∀ U ∈ pureReachable d K 0, ∃ s : ReverseShape d K,
      ∃ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
        (overlapOutputCoordinates d).symm ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x) =
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  exists_exact_witness_of_mem_pureReachable_zero hd

theorem reference_unitary_exact_witness_mixed {d K : ℕ} (hd : 0 < d) :
    ∀ U ∈ mixedReachable d K 0, ∃ s : ReverseShape d K,
      ∃ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
        (overlapOutputCoordinates d).symm ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x) =
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  exists_exact_witness_of_mem_mixedReachable_zero hd

/-- The zero budget is covered; no `1 ≤ K` premise is present. -/
theorem reference_unitary_exact_witness_zero_budget {d : ℕ} (hd : 0 < d) :
    ∀ U ∈ pureReachable d 0 0, ∃ s : ReverseShape d 0,
      ∃ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
        (overlapOutputCoordinates d).symm ((ReverseBlocks.coordinateOverlapPolynomial s hd).eval x) =
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  exists_exact_witness_of_mem_pureReachable_zero hd

theorem reference_unitary_exact_rank {d K : ℕ} (hd : 0 < d) (hd2 : 2 ≤ d)
    (s : ReverseShape d K) :
    ∀ x ∈ (ReverseBlocks.witnessFormat s hd 0).source,
      Module.finrank ℝ
          (LinearMap.range (fderiv ℝ (ReverseBlocks.coordinateOverlapPolynomial s hd).eval x).toLinearMap) ≤
        4 * d ^ 2 - 3 :=
  fun _ hx => ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le s hd hd2 hx

/-- The rank statement is about the full derivative, viewed through the
coercion of a continuous linear map to a linear map. -/
example {d K : ℕ} (hd : 0 < d) (hd2 : 2 ≤ d) (s : ReverseShape d K)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : x ∈ (ReverseBlocks.witnessFormat s hd 0).source) :
    Module.finrank ℝ
        (LinearMap.range
          (fderiv ℝ (ReverseBlocks.coordinateOverlapPolynomial s hd).eval x :
            RealEuclidean (witnessCoordinateBudget d K) →ₗ[ℝ] RealEuclidean (2 * d ^ 4))) ≤
      4 * d ^ 2 - 3 :=
  ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le s hd hd2 hx

theorem reference_unitary_contDiff {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) :
    ContDiff ℝ ∞ (ReverseBlocks.coordinateOverlapPolynomial s hd).eval :=
  ReverseBlocks.contDiff_coordinateOverlapPolynomial_eval s hd

theorem reference_unitary_rank_count {d : ℕ} (hd : 2 ≤ d) :
    4 * d ^ 2 - 3 + Fintype.card (Fin d × Fin d) ^ 2 < 2 * Fintype.card (Fin d × Fin d) ^ 2 :=
  unitaryWitnessRank_add_card_sq_lt hd

example (d K : ℕ) : Finite (ReverseShape d K) := inferInstance

/-! ## PVM exact witnesses -/

theorem reference_pvm_output_decoding (d : ℕ) (v : RealEuclidean (2 * d ^ 4)) :
    pvmOutputDecoding d v = ((overlapOutputCoordinates d).symm v)ᴴ :=
  pvmOutputDecoding_apply d v

theorem reference_pvm_exact_witness {d K : ℕ} (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    ∀ M ∈ purePVMReachable d K 0, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor) 0).source,
        pvmOutputDecoding d ((PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval y) =
          (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  exists_exact_pvm_witness_of_mem_purePVMReachable_zero hd hfloor

theorem reference_pvm_exact_witness_mixed {d K : ℕ} (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    ∀ M ∈ mixedPVMReachable d K 0, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor) 0).source,
        pvmOutputDecoding d ((PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval y) =
          (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  exists_exact_pvm_witness_of_mem_mixedPVMReachable_zero hd hfloor

theorem reference_pvm_below_floor {d K : ℕ} (hd : 0 < d) (hK : ¬ d ^ 2 ≤ 4 * K) :
    purePVMReachable d K 0 = ∅ :=
  purePVMReachable_zero_eq_empty_of_not_floor hd hK

/-- With `d ≥ 1`, the zero budget is below the floor, so nothing is exactly reachable. -/
example {d : ℕ} (hd : 0 < d) : purePVMReachable d 0 0 = ∅ :=
  purePVMReachable_zero_eq_empty_of_not_floor hd (by
    have : 0 < d ^ 2 := pow_pos hd 2
    omega)

theorem reference_pvm_exact_rank {d K : ℕ} (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (hd2 : 2 ≤ d)
    (s : PVMReverseShape d K) :
    ∀ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor) 0).source,
      Module.finrank ℝ
          (LinearMap.range
            (fderiv ℝ (PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval y).toLinearMap) ≤
        3 * d ^ 2 - 2 :=
  fun _ hy => PVMReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le s hd hfloor hd2 hy

theorem reference_pvm_contDiff {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    ContDiff ℝ ∞ (PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval :=
  PVMReverseBlocks.contDiff_coordinateOverlapPolynomial_eval s hd hfloor

theorem reference_pvm_rank_count {d : ℕ} (hd : 2 ≤ d) :
    3 * d ^ 2 - 2 + Fintype.card (Fin d × Fin d) ^ 2 < 2 * Fintype.card (Fin d × Fin d) ^ 2 :=
  pvmWitnessRank_add_card_sq_lt hd

example (d K : ℕ) : Finite (PVMReverseShape d K) := inferInstance

/-! ## Full types -/

#check @NLQCLean.ReverseBlocks.contDiff_coordinateOverlapPolynomial_eval
#check @NLQCLean.ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le
#check @NLQCLean.exists_exact_witness_of_mem_pureReachable_zero
#check @NLQCLean.exists_exact_witness_of_mem_mixedReachable_zero
#check @NLQCLean.coe_pureReachable_zero_subset_iUnion_witnessImage
#check @NLQCLean.unitaryWitnessRank_add_card_sq_lt
#check @NLQCLean.conjTransposeRealLinearEquiv
#check @NLQCLean.pvmOutputDecoding
#check @NLQCLean.pvmOutputDecoding_apply
#check @NLQCLean.pvmOutputDecoding_overlapOutputCoordinates_conjTranspose
#check @NLQCLean.PVMReverseBlocks.contDiff_coordinateOverlapPolynomial_eval
#check @NLQCLean.PVMReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le
#check @NLQCLean.floor_of_mem_purePVMReachable
#check @NLQCLean.purePVMReachable_eq_empty_of_not_floor
#check @NLQCLean.purePVMReachable_zero_eq_empty_of_not_floor
#check @NLQCLean.exists_exact_pvm_witness_of_mem_purePVMReachable_zero
#check @NLQCLean.exists_exact_pvm_witness_of_mem_mixedPVMReachable_zero
#check @NLQCLean.coe_purePVMReachable_zero_subset_iUnion_witnessImage
#check @NLQCLean.pvmWitnessRank_add_card_sq_lt

/-! ## Guarded axioms

Each printout must list exactly the standard logical axioms. -/

/-- info: 'NLQCLean.ReverseBlocks.contDiff_coordinateOverlapPolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ReverseBlocks.contDiff_coordinateOverlapPolynomial_eval
/-- info: 'NLQCLean.ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le
/-- info: 'NLQCLean.exists_exact_witness_of_mem_pureReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exact_witness_of_mem_pureReachable_zero
/-- info: 'NLQCLean.exists_exact_witness_of_mem_mixedReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exact_witness_of_mem_mixedReachable_zero
/-- info: 'NLQCLean.coe_pureReachable_zero_subset_iUnion_witnessImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.coe_pureReachable_zero_subset_iUnion_witnessImage
/-- info: 'NLQCLean.unitaryWitnessRank_add_card_sq_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryWitnessRank_add_card_sq_lt
/-- info: 'NLQCLean.conjTransposeRealLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.conjTransposeRealLinearEquiv
/-- info: 'NLQCLean.pvmOutputDecoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmOutputDecoding
/-- info: 'NLQCLean.pvmOutputDecoding_overlapOutputCoordinates_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmOutputDecoding_overlapOutputCoordinates_conjTranspose
/-- info: 'NLQCLean.PVMReverseBlocks.contDiff_coordinateOverlapPolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PVMReverseBlocks.contDiff_coordinateOverlapPolynomial_eval
/-- info: 'NLQCLean.PVMReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PVMReverseBlocks.finrank_range_fderiv_coordinateOverlapPolynomial_le
/-- info: 'NLQCLean.floor_of_mem_purePVMReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.floor_of_mem_purePVMReachable
/-- info: 'NLQCLean.purePVMReachable_eq_empty_of_not_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purePVMReachable_eq_empty_of_not_floor
/-- info: 'NLQCLean.purePVMReachable_zero_eq_empty_of_not_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purePVMReachable_zero_eq_empty_of_not_floor
/-- info: 'NLQCLean.exists_exact_pvm_witness_of_mem_purePVMReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exact_pvm_witness_of_mem_purePVMReachable_zero
/-- info: 'NLQCLean.exists_exact_pvm_witness_of_mem_mixedPVMReachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exact_pvm_witness_of_mem_mixedPVMReachable_zero
/-- info: 'NLQCLean.coe_purePVMReachable_zero_subset_iUnion_witnessImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.coe_purePVMReachable_zero_subset_iUnion_witnessImage
/-- info: 'NLQCLean.pvmWitnessRank_add_card_sq_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmWitnessRank_add_card_sq_lt

end NLQCTests
