import NLQCLean.Approx.SharpFreezing
import NLQCLean.LinearAlgebra.SchmidtOverlap
import NLQCLean.Models.SwapChoi

/-!
# The unconditional SWAP resource floor

The SWAP Choi
coefficients have a flat Gram spectrum. Their top-K mass bounds the score
of every budget-K protocol, independently of the image-volume hypothesis.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem schmidtMass_swapUnitary_le (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℕ) :
    schmidtMass K (normalizedLabChoiMatrix (swapUnitary ι)) ≤
      (K : ℝ) / Fintype.card (ι × ι) := by
  have hgram := normalizedLabChoiMatrix_swapUnitary_gram ι
  have hcoord := schmidtMass_eq_topWeightMass_of_coordinates
    (normalizedLabChoiMatrix (swapUnitary ι)) (1 : Matrix (ι × ι) (ι × ι) ℂ)
    (fun _ : ι × ι => (Fintype.card (ι × ι) : ℝ)⁻¹)
    isIsometry_one (by simpa using (isIsometry_one (n := ι × ι) (𝕜 := ℂ)))
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simpa using hgram) K
  rw [hcoord, div_eq_mul_inv]
  exact topWeightMass_le_mul K _ (inv_nonneg.mpr (Nat.cast_nonneg _)) (fun _ => le_rfl)

section Protocol

variable {ι ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ι] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ι] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB] [Nonempty ι]

/-- SWAP footprint floor, pure-resource score bound, with arbitrary finite private registers. -/
theorem PureProtocol.scoreU_swap_le
    (P : PureProtocol ι ι ρA ρB κA κB μA μB ι ι εA εB)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    scoreU (swapUnitary ι) P.operationalChannel ≤ (K : ℝ) / Fintype.card (ι × ι) :=
  (P.scoreU_le_schmidtMass (swapUnitary ι) (isIsometry_swapUnitary ι) hK).trans
    (schmidtMass_swapUnitary_le ι K)

/-- SWAP footprint floor, the resource lower bound for any epsilon-accurate SWAP protocol. -/
theorem PureProtocol.swap_footprint_floor
    (P : PureProtocol ι ι ρA ρB κA κB μA μB ι ι εA εB)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ι) P.operationalChannel) :
    (Fintype.card (ι × ι) : ℝ) * (1 - ε) ≤ K := by
  have hd : 0 < (Fintype.card (ι × ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (le_div_iff₀ hd).mp (hscore.trans (P.scoreU_swap_le hK))
  simpa only [mul_comm] using h

theorem PureProtocol.half_dimension_le_of_swap_score
    (P : PureProtocol ι ι ρA ρB κA κB μA μB ι ι εA εB)
    {K : ℕ} {ε : ℝ} (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : ε ≤ 1 / 2) (hscore : 1 - ε ≤ scoreU (swapUnitary ι) P.operationalChannel) :
    (Fintype.card (ι × ι) : ℝ) / 2 ≤ K := by
  have h := P.swap_footprint_floor hK hscore
  have hd : 0 ≤ (Fintype.card (ι × ι) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- SWAP footprint floor for finite mixed resources. Only the Schmidt number of the
decomposition and the complete message dimensions are charged. -/
theorem MixedResource.scoreU_swap_le {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ι × ρA) ℂ) (VB : Matrix (κB × μB) (ι × ρB) ℂ)
    (DA : Matrix (ι × εA) (κA × μB) ℂ) (DB : Matrix (ι × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K) :
    scoreU (swapUnitary ι) (m.mixedChannel VA VB DA DB) ≤
      (K : ℝ) / Fintype.card (ι × ι) := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB (swapUnitary ι)
  let P : PureProtocol ι ι ρA ρB κA κB μA μB ι ι εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact hk.trans (P.scoreU_swap_le hPK)

theorem MixedResource.swap_footprint_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ι × ρA) ℂ) (VB : Matrix (κB × μB) (ι × ρB) ℂ)
    (DA : Matrix (ι × εA) (κA × μB) ℂ) (DB : Matrix (ι × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ι) (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ι × ι) : ℝ) * (1 - ε) ≤ K := by
  have hd : 0 < (Fintype.card (ι × ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (le_div_iff₀ hd).mp
    (hscore.trans (m.scoreU_swap_le VA VB DA DB hVA hVB hDA hDB hR hK))
  simpa only [mul_comm] using h

theorem MixedResource.half_dimension_le_of_swap_score {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ι × ρA) ℂ) (VB : Matrix (κB × μB) (ι × ρB) ℂ)
    (DA : Matrix (ι × εA) (κA × μB) ℂ) (DB : Matrix (ι × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K) (hε : ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ι) (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ι × ι) : ℝ) / 2 ≤ K := by
  have h := m.swap_footprint_floor VA VB DA DB hVA hVB hDA hDB hR hK hscore
  have hd : 0 ≤ (Fintype.card (ι × ι) : ℝ) := Nat.cast_nonneg _
  nlinarith

end Protocol

end NLQCLean
