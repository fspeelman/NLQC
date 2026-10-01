/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Approx.PVMReachableWitnessCover
import NLQCLean.Approx.PVMWitnessJacobianBound

/-!
# Exact PVM witnesses on the zero-leakage polynomial source

At score one, the physical PVM coverage theorem forces the charged budget
floor `d² ≤ 4K`, and the extended cubic witness polynomial reproduces exactly
the output coordinates of the adjoint basis matrix `Mᴴ`. Decoding with the
inverse Frobenius-isometric coordinates and then taking the conjugate
transpose, a real-linear involution, returns `M` itself.

For one fixed floor proof, every pure or finite mixed exactly reachable basis
unitary is therefore the decoded output at a point of the zero-leakage source
of one member of the finite family indexed by `PVMReverseShape d K`. Floor
proofs are identified by proof irrelevance; they are not a family index. When
the floor fails, nothing is exactly reachable.

The differentiated map is the globally smooth extended cubic polynomial, whose
full ambient derivative has real rank at most `3d² - 2` at every point of the
zero-leakage source. For `d ≥ 2` this rank plus the Hermitian dimension
`(d²)²` is strictly below `2(d²)²`.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius _root_.ContDiff

/-- Conjugate transpose of complex matrices as a real-linear equivalence; it
is conjugate-linear over `ℂ` and involutive. -/
def conjTransposeRealLinearEquiv (m n : Type*) :
    Matrix m n ℂ ≃ₗ[ℝ] Matrix n m ℂ where
  toFun A := Aᴴ
  invFun A := Aᴴ
  map_add' := conjTranspose_add
  map_smul' r A := by ext i j; simp
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose

@[simp]
theorem conjTransposeRealLinearEquiv_apply {m n : Type*} (A : Matrix m n ℂ) :
    conjTransposeRealLinearEquiv m n A = Aᴴ :=
  rfl

@[simp]
theorem conjTransposeRealLinearEquiv_symm (m n : Type*) :
    (conjTransposeRealLinearEquiv m n).symm = conjTransposeRealLinearEquiv n m :=
  rfl

/-- Decode the PVM witness output: undo the output coordinates, then take the
conjugate transpose, so that the witness for `Mᴴ` decodes to `M`. -/
noncomputable def pvmOutputDecoding (d : ℕ) :
    RealEuclidean (2 * d ^ 4) ≃ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (overlapOutputCoordinates d).symm.trans (conjTransposeRealLinearEquiv _ _)

theorem pvmOutputDecoding_apply (d : ℕ) (v : RealEuclidean (2 * d ^ 4)) :
    pvmOutputDecoding d v = ((overlapOutputCoordinates d).symm v)ᴴ :=
  rfl

theorem pvmOutputDecoding_overlapOutputCoordinates_conjTranspose (d : ℕ)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    pvmOutputDecoding d (overlapOutputCoordinates d Mᴴ) = M := by
  rw [pvmOutputDecoding_apply, LinearEquiv.symm_apply_apply, conjTranspose_conjTranspose]

namespace PVMReverseBlocks

variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)

/-- The evaluated extended cubic PVM witness polynomial is globally smooth. -/
theorem contDiff_coordinateOverlapPolynomial_eval :
    ContDiff ℝ ∞ (coordinateOverlapPolynomial s hd hfloor).eval := by
  have he : (coordinateOverlapPolynomial s hd hfloor).eval = coordinateOverlap s hd hfloor :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor)
  rw [he]
  exact contDiff_coordinateOverlap s hd hfloor

/-- On the zero-leakage source the error term of the ambient rank-plus-error
decomposition vanishes, so the full ambient derivative itself has real rank at
most `3d² - 2`. -/
theorem finrank_range_fderiv_coordinateOverlapPolynomial_le (hd2 : 2 ≤ d)
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd hfloor 0).source) :
    Module.finrank ℝ
        (LinearMap.range (fderiv ℝ (coordinateOverlapPolynomial s hd hfloor).eval x).toLinearMap) ≤
      3 * d ^ 2 - 2 := by
  obtain ⟨T, R, he, hT, _, hR⟩ := witnessFormat_ambient_rank_error s hd hfloor hd2 le_rfl hx
  have hR0 : R = 0 := norm_le_zero_iff.mp (by simpa using hR)
  rw [he, hR0, add_zero]
  exact hT

end PVMReverseBlocks

/-- Any accurate pure PVM protocol forces the charged budget floor `d² ≤ 4K`. -/
theorem floor_of_mem_purePVMReachable {d K : ℕ} (hd : 0 < d) {e : ℝ} (he0 : 0 ≤ e)
    (he1 : e ≤ 1 / 2) {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (hM : M ∈ purePVMReachable d K e) : d ^ 2 ≤ 4 * K := by
  obtain ⟨t, P, hP, hscore⟩ := hM
  obtain ⟨hfloor, -⟩ := P.exists_pvm_extended_polynomial_witness hd
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) M.property.1 hP ⟨he0, he1⟩ hscore
  exact hfloor

/-- Below the budget floor no basis unitary is reachable to accuracy `e ≤ 1/2`. -/
theorem purePVMReachable_eq_empty_of_not_floor {d K : ℕ} (hd : 0 < d) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2) (hK : ¬ d ^ 2 ≤ 4 * K) :
    purePVMReachable d K e = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hM => hK (floor_of_mem_purePVMReachable hd he0 he1 hM)

/-- Below the budget floor no basis unitary is exactly reachable. -/
theorem purePVMReachable_zero_eq_empty_of_not_floor {d K : ℕ} (hd : 0 < d)
    (hK : ¬ d ^ 2 ≤ 4 * K) : purePVMReachable d K 0 = ∅ :=
  purePVMReachable_eq_empty_of_not_floor hd le_rfl (by norm_num) hK

/-- For one fixed floor proof, every exactly reachable pure PVM basis unitary
is the decoded extended polynomial output at a point of one zero-leakage
witness source. -/
theorem exists_exact_pvm_witness_of_mem_purePVMReachable_zero {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    ∀ M ∈ purePVMReachable d K 0, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor 0).source,
        pvmOutputDecoding d ((PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor).eval y) =
          (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  rintro M ⟨t, P, hP, hscore⟩
  -- The floor proof returned by coverage is identified with `hfloor` by proof irrelevance.
  obtain ⟨_, s, y, hy, hdist⟩ := P.exists_pvm_extended_polynomial_witness hd
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) M.property.1 hP ⟨le_rfl, by norm_num⟩ hscore
  simp only [Real.sqrt_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at hy hdist
  refine ⟨s, y, hy, ?_⟩
  rw [hdist, pvmOutputDecoding_overlapOutputCoordinates_conjTranspose]

/-- Finite mixed exact PVM reachability has the same exact witnesses. -/
theorem exists_exact_pvm_witness_of_mem_mixedPVMReachable_zero {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    ∀ M ∈ mixedPVMReachable d K 0, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor 0).source,
        pvmOutputDecoding d ((PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor).eval y) =
          (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact exists_exact_pvm_witness_of_mem_purePVMReachable_zero hd hfloor

/-- The exactly reachable PVM basis unitaries, as matrices, lie in the finite
union of decoded images of the zero-leakage witness sources. -/
theorem coe_purePVMReachable_zero_subset_iUnion_witnessImage {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    ((↑) : Matrix.unitaryGroup (Fin d × Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ''
        purePVMReachable d K 0 ⊆
      ⋃ s : PVMReverseShape d K,
        (fun y => pvmOutputDecoding d
            ((PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor).eval y)) ''
          (PVMReverseBlocks.witnessFormat s hd hfloor 0).source := by
  rintro _ ⟨M, hM, rfl⟩
  obtain ⟨s, y, hy, he⟩ := exists_exact_pvm_witness_of_mem_purePVMReachable_zero hd hfloor M hM
  exact Set.mem_iUnion.mpr ⟨s, y, hy, he⟩

/-- For `d ≥ 2`, the PVM witness rank plus the Hermitian dimension `(d²)²` is
strictly below the real dimension `2(d²)²` of the bipartite matrix space. -/
theorem pvmWitnessRank_add_card_sq_lt {d : ℕ} (hd : 2 ≤ d) :
    3 * d ^ 2 - 2 + Fintype.card (Fin d × Fin d) ^ 2 <
      2 * Fintype.card (Fin d × Fin d) ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  have h4 : 4 ≤ d ^ 2 := by nlinarith
  have hsq : (d * d) ^ 2 = d ^ 2 * d ^ 2 := by ring
  have hm : 4 * d ^ 2 ≤ d ^ 2 * d ^ 2 := Nat.mul_le_mul_right _ h4
  rw [hsq]
  omega

end NLQCLean
