import NLQCLean.Approx.PVMBlockSpectrum
import NLQCLean.Approx.PVMChoiProjection
import NLQCLean.Models.ProjectiveProtocolScore

/-!
# Unconditional rank floor for ordered rank-one PVMs

Every squared Schmidt weight of the good-flag Choi
projection is at most `1 / D`: an environment weight is bounded by one, a
target-column weight is bounded by one, and the normalized Choi matrix supplies
the factor `1 / D`.  The rank-`K` overlap bound therefore forces
`D * (1 - ε)^2 ≤ K`.

The spectral estimate works for every orthonormal target basis.  Explicit
identity-target corollaries record the product-basis witness needed by the
later universal lower bound.  Finite mixed resources are reduced to one pure
component using score affinity, while retaining the single charged
Schmidt-number/message footprint.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- A squared Schmidt weight is at most the total squared Frobenius norm. -/
theorem schmidtWeight_le_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m n ℂ) (i : m) :
    schmidtWeights A i ≤ ‖A‖ ^ 2 := by
  calc
    schmidtWeights A i ≤ ∑ j, schmidtWeights A j :=
      Finset.single_le_sum (fun j _ ↦ schmidtWeights_nonneg A j) (Finset.mem_univ i)
    _ = ‖A‖ ^ 2 := sum_schmidtWeights A

/-- Flat `1 / D` upper bound for the Schmidt mass of a flagged normalized
Choi matrix.  The environment blocks may vanish and need only have norm at
most one. -/
theorem schmidtMass_tensorChoiMatrix_flag_mul_adjoint_le
    {ιA ιB εA εB : Type*}
    [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB]
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq εA] [DecidableEq εB]
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    (ω : (ιA × ιB) → εA × εB → ℂ)
    (hω : ∀ i, ‖resourceMatrix (ω i)‖ ≤ 1) (K : ℕ) :
    schmidtMass K (tensorChoiMatrix (flagIsometry ω * Mᴴ)) ≤
      (K : ℝ) / Fintype.card (ιA × ιB) := by
  rw [schmidtMass_tensorChoiMatrix_flag_mul_adjoint]
  rw [div_eq_mul_inv]
  apply topWeightMass_le_mul K
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  intro p
  let A := resourceMatrix (ω p.2)
  let B : Matrix ιA ιB ℂ := fun a b ↦ star (M (a, b) p.2)
  have hB0 : 0 ≤ schmidtWeights B p.1.2 := schmidtWeights_nonneg B p.1.2
  have hA1 : schmidtWeights A p.1.1 ≤ 1 := by
    have hw := schmidtWeight_le_norm_sq A p.1.1
    have hn : ‖A‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg A) (hω p.2) 2
    simpa only [one_pow] using hw.trans hn
  have hB1 : schmidtWeights B p.1.2 ≤ 1 := by
    have hw := schmidtWeight_le_norm_sq B p.1.2
    have hBnorm : ‖B‖ = 1 := by
      have hBeq : B = pvmConjugateColumnMatrix M p.2 := by
        ext a b
        simp [B, pvmConjugateColumnMatrix]
      rw [hBeq]
      exact norm_conjugate_pvmColumnMatrix hM p.2
    rw [hBnorm, one_pow] at hw
    exact hw
  have hprod : schmidtWeights A p.1.1 * schmidtWeights B p.1.2 ≤ 1 :=
    mul_le_one₀ hA1 hB0 hB1
  simpa only [A, B, mul_one] using
    (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (Nat.cast_nonneg _)))

section Pure

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

/-- Every charged pure protocol has PVM score squared at most `K / D`. -/
theorem PureProtocol.scorePVM_sq_le_footprint_div_card
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    (scorePVM M P.operationalChannel) ^ 2 ≤
      (K : ℝ) / Fintype.card (ιA × ιB) := by
  calc
    (scorePVM M P.operationalChannel) ^ 2 ≤
        schmidtMass K
          (tensorChoiMatrix (pvmProjectedDilation M P.globalIsometry)) :=
      P.scorePVM_sq_le_schmidtMass_pvmProjected M hK
    _ ≤ (K : ℝ) / Fintype.card (ιA × ιB) := by
      rw [pvmProjectedDilation]
      exact schmidtMass_tensorChoiMatrix_flag_mul_adjoint_le M hM
        (pvmEnvironment M P.globalIsometry)
        (fun i ↦ norm_resourceMatrix_pvmEnvironment_le_one
          P.isIsometry_globalIsometry hM i) K

/-- PVM-B for pure resources, in its stronger arbitrary-orthonormal-basis
form. -/
theorem PureProtocol.pvm_footprint_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K := by
  have hleft : 0 ≤ 1 - ε := sub_nonneg.mpr hε.2
  have hscore0 : 0 ≤ scorePVM M P.operationalChannel := hleft.trans hscore
  have hsquare : (1 - ε) ^ 2 ≤ (scorePVM M P.operationalChannel) ^ 2 :=
    (sq_le_sq₀ hleft hscore0).2 hscore
  have hbound := hsquare.trans (P.scorePVM_sq_le_footprint_div_card M hM hK)
  have hD : 0 < (Fintype.card (ιA × ιB) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hmul := (le_div_iff₀ hD).mp hbound
  simpa only [mul_comm] using hmul

/-- The `ε ≤ 1/2` consequence used by the quantitative package. -/
theorem PureProtocol.quarter_card_le_of_pvm_score
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hhalf : ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) / 4 ≤ K := by
  have h := P.pvm_footprint_floor M hM hK hε hscore
  have hD : 0 ≤ (Fintype.card (ιA × ιB) : ℝ) := Nat.cast_nonneg _
  have he : (1 / 4 : ℝ) ≤ (1 - ε) ^ 2 := by
    nlinarith [sq_nonneg (ε - 1 / 2)]
  calc
    (Fintype.card (ιA × ιB) : ℝ) / 4 =
        (Fintype.card (ιA × ιB) : ℝ) * (1 / 4) := by ring
    _ ≤ (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 :=
      mul_le_mul_of_nonneg_left he hD
    _ ≤ K := h

/-- An explicit product-basis pure-resource witness. -/
theorem PureProtocol.identityPVM_footprint_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ)
      P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K :=
  P.pvm_footprint_floor 1 isIsometry_one hK hε hscore

/-- Product-basis pure-resource floor at error at most one half. -/
theorem PureProtocol.quarter_card_le_of_identityPVM_score
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hhalf : ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ)
      P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) / 4 ≤ K :=
  P.quarter_card_le_of_pvm_score 1 isIsometry_one hK hε hhalf hscore

end Pure

section Mixed

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

/-- PVM-B for a finite mixed resource.  The local support dimensions remain
unrestricted; only the componentwise Schmidt number and both message
dimensions enter the charged footprint. -/
theorem MixedResource.pvm_footprint_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.pvm_footprint_floor M hM hPK hε (hscore.trans hk)

/-- The finite-mixed `D / 4` consequence at error at most one half. -/
theorem MixedResource.quarter_card_le_of_pvm_score {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hhalf : ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) / 4 ≤ K := by
  have h := m.pvm_footprint_floor VA VB DA DB hVA hVB hDA hDB M hM
    hR hK hε hscore
  have hD : 0 ≤ (Fintype.card (ιA × ιB) : ℝ) := Nat.cast_nonneg _
  have he : (1 / 4 : ℝ) ≤ (1 - ε) ^ 2 := by
    nlinarith [sq_nonneg (ε - 1 / 2)]
  calc
    (Fintype.card (ιA × ιB) : ℝ) / 4 =
        (Fintype.card (ιA × ιB) : ℝ) * (1 / 4) := by ring
    _ ≤ (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 :=
      mul_le_mul_of_nonneg_left he hD
    _ ≤ K := h

/-- An explicit product-basis finite-mixed witness. -/
theorem MixedResource.identityPVM_footprint_floor {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ)
      (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K :=
  m.pvm_footprint_floor VA VB DA DB hVA hVB hDA hDB 1 isIsometry_one
    hR hK hε hscore

/-- Product-basis finite-mixed floor at error at most one half. -/
theorem MixedResource.quarter_card_le_of_identityPVM_score {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hhalf : ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ)
      (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) / 4 ≤ K :=
  m.quarter_card_le_of_pvm_score VA VB DA DB hVA hVB hDA hDB
    1 isIsometry_one hR hK hε hhalf hscore

end Mixed

end NLQCLean
