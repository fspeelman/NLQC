import NLQCLean.Models.ChargedCompactProtocols
import NLQCLean.Models.ChargedCompactPVMProtocols
import NLQCLean.Bounds.QualitativeDiamond
import NLQCLean.Rigidity.FlaggedSupports

/-!
# Qualitative divergence for every exactly impossible target

Charged compactness gives positive budget-dependent gaps for any target with
no finite exact implementation. The same gap applies to common-map finite
mixtures, and score domination transfers it to the diamond or joint-TV
error. No rate and no attainment of an operational-error optimum is asserted.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

section PositiveFootprint

variable {ιA ιB ρA ρB κA κB μA μB oA oB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype oA] [Fintype oB] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq oA] [DecidableEq oB] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

/-- Nonempty input registers force positive resource and both message charges. -/
theorem PureProtocol.footprint_pos
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB oA oB εA εB) :
    0 < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  have hresource := P.resource_unit.card_pos
  simp only [Fintype.card_prod] at hresource
  have hρA : 0 < Fintype.card ρA := Nat.pos_of_mul_pos_right hresource
  have hρB : 0 < Fintype.card ρB := Nat.pos_of_mul_pos_left hresource
  have hencA := P.encA_isometry.card_le
  have hencB := P.encB_isometry.card_le
  simp only [Fintype.card_prod] at hencA hencB
  have hμA : 0 < Fintype.card μA :=
    Nat.pos_of_mul_pos_left ((Nat.mul_pos Fintype.card_pos hρA).trans_le hencA)
  have hμB : 0 < Fintype.card μB :=
    Nat.pos_of_mul_pos_left ((Nat.mul_pos Fintype.card_pos hρB).trans_le hencB)
  exact Nat.mul_pos (Nat.mul_pos P.resource_unit.schmidtRank_pos hμA) hμB

theorem PureProtocol.not_hasFootprint_zero
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB oA oB εA εB) :
    ¬ P.HasFootprint 0 := by
  intro hP
  have h := (hasFootprint_iff 0 P.resource).mp hP
  exact (Nat.not_le_of_gt P.footprint_pos) h

end PositiveFootprint

theorem pureReachable_zero_budget {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    pureReachable d 0 e = ∅ := by
  let : NeZero d := ⟨by omega⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro U ⟨s, P, hP, _⟩
  exact P.not_hasFootprint_zero hP

theorem purePVMReachable_zero_budget {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    purePVMReachable d 0 e = ∅ := by
  let : NeZero d := ⟨by omega⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro M ⟨s, P, hP, _⟩
  exact P.not_hasFootprint_zero hP

theorem mixedReachable_zero_budget {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    mixedReachable d 0 e = ∅ := by
  rw [mixedReachable_eq_pureReachable, pureReachable_zero_budget hd]

theorem mixedPVMReachable_zero_budget {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    mixedPVMReachable d 0 e = ∅ := by
  rw [mixedPVMReachable_eq_purePVMReachable, purePVMReachable_zero_budget hd]

/-- Finite compressed exact exclusion covers original registers in all universes. -/
theorem noFinitePureImplementation_of_no_shape_exact {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinProtocol d s, ¬ P.PerformsUnitary U) :
    NoFinitePureImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hexact
  let K := schmidtRank P.resource * Fintype.card μA * Fintype.card μB
  have hK : P.HasFootprint K := (hasFootprint_iff K P.resource).mpr le_rfl
  obtain ⟨s, _, Q, hchan⟩ := P.exists_support_charged_fin_representative hK
  apply hN s Q
  change Q.operationalChannel = adConj U
  rw [← hchan]
  exact hexact

/-- The PVM bridge uses score exactness, retaining the all-input task. -/
theorem noFinitePurePVMImplementation_of_no_shape_exact {d : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinPVMProtocol d s, ¬ P.PerformsPVM M) :
    NoFinitePurePVMImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M := by
  let : NeZero d := ⟨by omega⟩
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hexact
  let K := schmidtRank P.resource * Fintype.card μA * Fintype.card μB
  have hK : P.HasFootprint K := (hasFootprint_iff K P.resource).mpr le_rfl
  obtain ⟨s, _, Q, hchan⟩ := P.exists_support_charged_fin_pvm_representative hK
  apply hN s Q
  apply (Q.scorePVM_eq_one_iff_performsPVM hM).mp
  rw [← hchan]
  exact (P.scorePVM_eq_one_iff_performsPVM hM).mpr hexact

theorem unitaryScoreDeficit_pos_of_no_shape_exact {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : IsIsometry U)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinProtocol d s, ¬ P.PerformsUnitary U) :
    0 < unitaryScoreDeficit U K := by
  have hnonneg := (unitaryScoreDeficit_mem_Icc hd hK U hU).1
  apply lt_of_le_of_ne hnonneg
  intro hzero
  obtain ⟨s, P, _, hexact⟩ := (unitaryScoreDeficit_eq_zero_iff hd hK U hU).mp hzero.symm
  exact hN s P hexact

theorem pvmScoreDeficit_pos_of_no_shape_exact {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinPVMProtocol d s, ¬ P.PerformsPVM M) :
    0 < pvmScoreDeficit M K := by
  have hnonneg := (pvmScoreDeficit_mem_Icc hd hK M hM).1
  apply lt_of_le_of_ne hnonneg
  intro hzero
  obtain ⟨s, P, _, hexact⟩ := (pvmScoreDeficit_eq_zero_iff hd hK M hM).mp hzero.symm
  exact hN s P hexact

/-- Every finite budget has a positive common pure/mixed score and diamond gap. -/
theorem exists_general_target_unitary_gap {d : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : UnitaryTarget U)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinProtocol d s, ¬ P.PerformsUnitary U)
    (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e := by
  let : NeZero d := ⟨by omega⟩
  let L := max K 1
  have hL : 1 ≤ L := le_max_right _ _
  have he := unitaryScoreDeficit_pos_of_no_shape_exact hd hL U hU.1 hN
  have hp : PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
      U K (unitaryScoreDeficit U L) := by
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
    have hPL : P.HasFootprint L := HasFootprint.mono hP (le_max_left K 1)
    have hs := P.score_le_unitaryScoreMaximum hd hL hPL U
    simpa only [unitaryScoreDeficit, sub_sub_cancel] using hs
  exact ⟨_, he, hp, hp.mixed, hp.diamond hU, hp.mixed.diamond hU⟩

/-- The original no-finite-exact predicate implies the explicit compressed premise. -/
theorem exists_general_target_unitary_gap_of_no_finite_exact {d : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : UnitaryTarget U)
    (hN : NoFinitePureImplementation.{0, 0, 0, 0, 0, 0, 0, 0} U) (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e ∧
      MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e :=
  exists_general_target_unitary_gap hd U hU
    (fun s P => hN (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7)) P) K

/-- Every finite PVM budget has positive common score and joint-TV gaps. -/
theorem exists_general_target_pvm_gap {d : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hN : ∀ s : Fin 8 → ℕ, ∀ P : FinPVMProtocol d s, ¬ P.PerformsPVM M)
    (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  let : NeZero d := ⟨by omega⟩
  let L := max K 1
  have hL : 1 ≤ L := le_max_right _ _
  have he := pvmScoreDeficit_pos_of_no_shape_exact hd hL M hM hN
  have hp : PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
      M K (pvmScoreDeficit M L) := by
    intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
    have hPL : P.HasFootprint L := HasFootprint.mono hP (le_max_left K 1)
    have hs := P.scorePVM_le_pvmScoreMaximum hd hL hPL M
    simpa only [pvmScoreDeficit, sub_sub_cancel] using hs
  exact ⟨_, he, hp, hp.mixed, hp.tv hM, hp.mixed.tv hM⟩

theorem exists_general_target_pvm_gap_of_no_finite_exact {d : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hN : NoFinitePurePVMImplementation.{0, 0, 0, 0, 0, 0, 0, 0} M) (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e :=
  exists_general_target_pvm_gap hd M hM
    (fun s P => hN (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7)) P) K

section Divergence

variable {d : ℕ} {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
variable {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Error below a budget gap forces the rank/message footprint above it. -/
theorem PureScoreGap.footprint_gt_of_deficit_lt {K : ℕ} {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (he : 1 - scoreU U P.operationalChannel < e) :
    K < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  have hs := h ρA ρB κA κB μA μB εA εB P
    ((hasFootprint_iff K P.resource).mpr hK)
  linarith

theorem PureDiamondGap.footprint_gt_of_error_lt {K : ℕ} {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (he : diamondError P.operationalChannel (adConj U) < e) :
    K < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  exact (not_le_of_gt he) (h ρA ρB κA κB μA μB εA εB P
    ((hasFootprint_iff K P.resource).mpr hK))

theorem PurePVMScoreGap.footprint_gt_of_deficit_lt {K : ℕ} {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (he : 1 - scorePVM M P.operationalChannel < e) :
    K < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  have hs := h ρA ρB κA κB μA μB εA εB P
    ((hasFootprint_iff K P.resource).mpr hK)
  linarith

theorem PurePVMTVGap.footprint_gt_of_error_lt {K : ℕ} {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (he : pvmTVError M P.operationalChannel < e) :
    K < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  exact (not_le_of_gt he) (h ρA ρB κA κB μA μB εA εB P
    ((hasFootprint_iff K P.resource).mpr hK))

theorem MixedScoreGap.footprint_gt_of_deficit_lt {K : ℕ} {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (R : ℕ) (hR : m.schmidtNumberLE R)
    (he : 1 - scoreU U (m.mixedChannel VA VB DA DB) < e) :
    K < R * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  have hs := h ρA ρB κA κB μA μB εA εB n m VA VB DA DB
    hVA hVB hDA hDB R hR hK
  linarith

theorem MixedDiamondGap.footprint_gt_of_error_lt {K : ℕ} {e : ℝ}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} U K e)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (R : ℕ) (hR : m.schmidtNumberLE R)
    (he : diamondError (m.mixedChannel VA VB DA DB) (adConj U) < e) :
    K < R * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  exact (not_le_of_gt he) (h ρA ρB κA κB μA μB εA εB n m VA VB DA DB
    hVA hVB hDA hDB R hR hK)

theorem MixedPVMScoreGap.footprint_gt_of_deficit_lt {K : ℕ} {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (R : ℕ) (hR : m.schmidtNumberLE R)
    (he : 1 - scorePVM M (m.mixedChannel VA VB DA DB) < e) :
    K < R * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  have hs := h ρA ρB κA κB μA μB εA εB n m VA VB DA DB
    hVA hVB hDA hDB R hR hK
  linarith

theorem MixedPVMTVGap.footprint_gt_of_error_lt {K : ℕ} {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e)
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (R : ℕ) (hR : m.schmidtNumberLE R)
    (he : pvmTVError M (m.mixedChannel VA VB DA DB) < e) :
    K < R * Fintype.card μA * Fintype.card μB := by
  apply Nat.lt_of_not_ge
  intro hK
  exact (not_le_of_gt he) (h ρA ρB κA κB μA μB εA εB n m VA VB DA DB
    hVA hVB hDA hDB R hR hK)

end Divergence

end NLQCLean
