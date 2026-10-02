import NLQCLean.Approx.PVMWitnessTargets

/-!
# Physical PVM reachability lies in the inverse witness cover

The extended polynomial witness approximates the adjoint of
the basis lift, so accurate targets enter the fixed-floor witness union after
inversion. Pure and finite mixed score reachability are both covered.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

namespace PVMReverseBlocks

theorem coe_unitary_inv_eq_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    ((U⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) = (U : Matrix ι ι ℂ)ᴴ :=
  rfl

/-- A witness for the adjoint basis matrix places the unitary in the inverse cover. -/
theorem mem_inverseWitnessTargets_of_adjoint {d K : ℕ} (s : PVMReverseShape d K)
    (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {δ ρ : ℝ}
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    {y : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hy : y ∈ (witnessFormat s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor) δ).source)
    (hdist : ‖(coordinateOverlapPolynomial s hd hfloor (PVMReverseShape.admissibleBudget_full s hd hfloor)).eval y -
      overlapOutputCoordinates d (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ‖ ≤ ρ) :
    U ∈ inverseWitnessTargets hd hfloor δ ρ := by
  refine Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨s, y, hy, ?_⟩)
  rw [dist_comm, dist_eq_norm, coe_unitary_inv_eq_conjTranspose]
  exact hdist

end PVMReverseBlocks

/-- One finite pure PVM protocol enters the inverse witness cover at its
score and charged footprint. -/
theorem FinPVMProtocol.mem_inverseWitnessTargets {d K : ℕ} {t : Fin 8 → ℕ}
    (P : FinPVMProtocol d t) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (hP : HasFootprint K P.resource (Fin (t 4)) (Fin (t 5)))
    (hscore : 1 - e ≤ scorePVM (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      P.operationalChannel) :
    U ∈ PVMReverseBlocks.inverseWitnessTargets hd hfloor
      (2 * Real.sqrt e) (2 * (d : ℝ) * Real.sqrt e) := by
  obtain ⟨_, s, y, hy, hdist⟩ :=
    P.exists_pvm_extended_polynomial_witness hd
      (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) U.property.1 hP ⟨he0, he1⟩ hscore
  exact PVMReverseBlocks.mem_inverseWitnessTargets_of_adjoint s hd hfloor hy hdist

/-- Accurate pure PVM protocols are covered after inversion, because the
reverse witness approximates the adjoint basis unitary. -/
theorem purePVMReachable_subset_inv_witnessTargets {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2) :
    purePVMReachable d K e ⊆
      PVMReverseBlocks.inverseWitnessTargets hd hfloor
        (2 * Real.sqrt e) (2 * (d : ℝ) * Real.sqrt e) := by
  rintro U ⟨t, P, hP, hscore⟩
  exact P.mem_inverseWitnessTargets hd hfloor he0 he1 hP hscore

/-- Finite mixed PVM reachability obeys the same inverse witness cover. -/
theorem mixedPVMReachable_subset_inv_witnessTargets {d K : ℕ} (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2) :
    mixedPVMReachable d K e ⊆
      PVMReverseBlocks.inverseWitnessTargets hd hfloor
        (2 * Real.sqrt e) (2 * (d : ℝ) * Real.sqrt e) := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact purePVMReachable_subset_inv_witnessTargets hd hfloor he0 he1

end NLQCLean
