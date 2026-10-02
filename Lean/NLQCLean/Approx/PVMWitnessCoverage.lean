import NLQCLean.Approx.PVMPhysicalReverse

/-!
# Finite physical PVM witness coverage

Every original finite-register PVM protocol produces a member of the finite
charged architecture and positive allocation family, with the sharp frozen
residual and both leakage identities.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius Kronecker MatrixOrder ComplexOrder

/-- One member of the finite witness cover of basis lifts. The target uses the
analysis adjoint and normalized Frobenius error `2√ε`. -/
def PVMReverseShape.approximationTargets {d K : ℕ} (s : PVMReverseShape d K) (ε : ℝ) :
    Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {M | ∃ x : PVMReverseBlocks s, PVMReverseBlocks.IsValid x ∧
    ‖PVMReverseBlocks.overlap x - Mᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε)}

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Physical coverage. Every arbitrary-finite-register protocol of budget
K and score at least `1-epsilon` is covered by a valid bounded six-block
witness. No original private or environment dimension appears in its type. -/
theorem PureProtocol.exists_pvm_reverse_witness
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hscore : 1 - ε ≤ scorePVM U P.operationalChannel) :
    ∃ s : PVMReverseShape d K, ∃ x : PVMReverseBlocks s, PVMReverseBlocks.IsValid x ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * Uᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨r, kA, kB, hr, hkA, hkB, Q, _, hchan⟩ :=
    P.exists_compressed_pvm_encoders
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : d * r ≤ kA * mA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : d * r ≤ kB * mB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencA)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
  let s : ReverseShape d K := ⟨r, mA, mB, hrpos, hma, hmb, hfoot⟩
  let R := Q.reindex (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm (Equiv.refl _) (Equiv.refl _)
  have hRchan : P.operationalChannel = R.operationalChannel :=
    hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm
  have hRK : NLQCLean.HasFootprint K R.resource (Fin mA) (Fin mB) := by
    refine ⟨r, mA, mB, hfoot, ?_, ?_, ?_⟩
    · simpa only [Fintype.card_fin] using schmidtRank_le_card_left R.resource
    · simp
    · simp
  obtain ⟨v, hv, hvrank, hclose⟩ := R.exists_pvm_frozen hU hRK hε
    (hRchan ▸ hscore)
  obtain ⟨a, -, x, hx, hcross⟩ := R.exists_pvm_reverse_blocks_of_frozen s hkA hkB v hv hvrank
  refine ⟨(s, a), x, hx, ?_⟩
  have hdist := norm_sub_eq_of_crossGram_eq (PVMReverseBlocks.forward x) (PVMReverseBlocks.reverse x)
    R.globalIsometry (flagIsometry v) Uᴴ
    hx.isIsometry_forward hx.isIsometry_reverse R.isIsometry_globalIsometry
    (isIsometry_flagIsometry v hv) hcross
  rw [← hdist] at hclose
  have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by
    simp [pow_two]
  rw [hD, Real.sqrt_sq (Nat.cast_nonneg d)] at hclose
  have h := (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hclose
  simpa only [mul_comm] using h

/-- Physical coverage with the cross-Gram and both leakage bounds included. -/
theorem PureProtocol.exists_pvm_reverse_witness_approximation
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hscore : 1 - ε ≤ scorePVM U P.operationalChannel) :
    ∃ s : PVMReverseShape d K, ∃ x : PVMReverseBlocks s, PVMReverseBlocks.IsValid x ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * Uᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε) ∧
      ‖PVMReverseBlocks.overlap x - Uᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε) ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * PVMReverseBlocks.overlap x‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ∧
      ‖PVMReverseBlocks.reverse x - PVMReverseBlocks.forward x * (PVMReverseBlocks.overlap x)ᴴ‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * (4 * ε) := by
  obtain ⟨s, x, hx, hclose⟩ := P.exists_pvm_reverse_witness hd U hU hK hε hscore
  refine ⟨s, x, hx, hclose, ?_⟩
  have h := hx.approximation Uᴴ (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) hclose
  simpa only [mul_pow, Real.sq_sqrt hε.1, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- Finite mixed resources are covered by a common-map component
whose PVM score is at least the mixture score. Only component Schmidt ranks
and the complete message dimensions are charged. -/
theorem MixedResource.exists_pvm_reverse_witness_approximation
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 0 < d) {K R : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : IsIsometry U)
    (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM U (m.mixedChannel VA VB DA DB)) :
    ∃ s : PVMReverseShape d K, ∃ x : PVMReverseBlocks s, PVMReverseBlocks.IsValid x ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * Uᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε) ∧
      ‖PVMReverseBlocks.overlap x - Uᴴ‖ ≤ (d : ℝ) * (2 * Real.sqrt ε) ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * PVMReverseBlocks.overlap x‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ∧
      ‖PVMReverseBlocks.reverse x - PVMReverseBlocks.forward x * (PVMReverseBlocks.overlap x)ᴴ‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * (4 * ε) := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB U
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.exists_pvm_reverse_witness_approximation hd U hU hPK hε (hscore.trans hk)

/-- Every admissible pure protocol target belongs to the finite witness cover,
whose index cardinality is bounded by `PVMReverseShape.card_le`. -/
theorem PureProtocol.mem_iUnion_pvmApproximationTargets
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hscore : 1 - ε ≤ scorePVM U P.operationalChannel) :
    U ∈ ⋃ s : PVMReverseShape d K, s.approximationTargets ε := by
  obtain ⟨s, x, hx, _, hclose, _⟩ :=
    P.exists_pvm_reverse_witness_approximation hd U hU hK hε hscore
  exact Set.mem_iUnion.mpr ⟨s, x, hx, hclose⟩

/-- The same finite cover contains all admissible finite-mixed targets. -/
theorem MixedResource.mem_iUnion_pvmApproximationTargets
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 0 < d) {K R : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : IsIsometry U)
    (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM U (m.mixedChannel VA VB DA DB)) :
    U ∈ ⋃ s : PVMReverseShape d K, s.approximationTargets ε := by
  obtain ⟨s, x, hx, _, hclose, _⟩ :=
    m.exists_pvm_reverse_witness_approximation VA VB DA DB hVA hVB hDA hDB
      hd U hU hR hK hε hscore
  exact Set.mem_iUnion.mpr ⟨s, x, hx, hclose⟩

end PhysicalCoverage

end NLQCLean
