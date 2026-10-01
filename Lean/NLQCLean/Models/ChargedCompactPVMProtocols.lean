import NLQCLean.Bounds.PVMQualitativeGap
import NLQCLean.Models.PVMMixedReachability

/-!
# Compact charged families for ordered rank-one PVM scores

The finite family retains the support charge and both message dimensions.
Its maximum is attained by an actual protocol in the original two-sided
outcome model, rather than by an extra architecture in a bounding box.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

abbrev ChargedPVMShape (d K : ℕ) :=
  {s : BoundedPVMShape d K // (s 0).val * (s 4).val * (s 5).val ≤ K}

def chargedPVMShapeScores {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : Set ℝ :=
  ⋃ s : ChargedPVMShape d K, pvmShapeScores M (fun i => (s.val i).val)

theorem isCompact_chargedPVMShapeScores {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) :
    IsCompact (chargedPVMShapeScores M K) := by
  classical
  exact isCompact_iUnion fun s : ChargedPVMShape d K =>
    isCompact_pvmShapeScores M (fun i => (s.val i).val)

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

theorem PureProtocol.scorePVM_mem_chargedPVMShapeScores
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {K : ℕ} (hK : P.HasFootprint K) :
    scorePVM M P.operationalChannel ∈ chargedPVMShapeScores M K := by
  obtain ⟨s, hs, hcharge, Q, hchan⟩ :=
    P.exists_bounded_support_charged_fin_pvm_representative hd K hK
  rw [hchan]
  apply Set.mem_iUnion.mpr
  refine ⟨⟨fun i => ⟨s i, Nat.lt_succ_of_le (hs i)⟩, hcharge⟩, ?_⟩
  exact Q.score_mem_pvmShapeScores M

end ArbitraryRegisters

theorem mem_chargedPVMShapeScores_iff {d K : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (v : ℝ) :
    v ∈ chargedPVMShapeScores M K ↔
      ∃ s : Fin 8 → ℕ, ∃ P : FinPVMProtocol d s,
        P.HasFootprint K ∧ scorePVM M P.operationalChannel = v := by
  constructor
  · intro hv
    obtain ⟨s, x, hx, hscore⟩ := Set.mem_iUnion.mp hv
    exact ⟨_, PVMPhysicalBlocks.toProtocol x hx,
      (PVMPhysicalBlocks.toProtocol x hx).hasFootprint_of_support_charge s.property,
      hscore⟩
  · rintro ⟨s, P, hK, rfl⟩
    exact P.scorePVM_mem_chargedPVMShapeScores hd M hK

theorem purePVMReachable_eq_charged_iUnion {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    purePVMReachable d K e =
      ⋃ s : ChargedPVMShape d K, pvmPhysicalTargets d (fun i => (s.val i).val) e := by
  ext M
  constructor
  · rintro ⟨s, P, hK, he⟩
    obtain ⟨t, ht, hcharge, Q, hchan⟩ :=
      P.exists_bounded_support_charged_fin_pvm_representative hd K hK
    refine Set.mem_iUnion.mpr
      ⟨⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i)⟩, hcharge⟩,
        (Q.resource, Q.encA, Q.encB, Q.decA, Q.decB),
        ⟨Q.resource_unit, Q.encA_isometry, Q.encB_isometry,
          Q.decA_isometry, Q.decB_isometry⟩, ?_⟩
    change 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) Q.operationalChannel
    rw [← hchan]
    exact he
  · intro h
    obtain ⟨s, x, hx, he⟩ := Set.mem_iUnion.mp h
    exact ⟨_, PVMPhysicalBlocks.toProtocol x hx,
      (PVMPhysicalBlocks.toProtocol x hx).hasFootprint_of_support_charge s.property, he⟩

theorem isCompact_purePVMReachable {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    IsCompact (purePVMReachable d K e) := by
  classical
  rw [purePVMReachable_eq_charged_iUnion hd]
  exact isCompact_iUnion fun s : ChargedPVMShape d K =>
    isCompact_pvmPhysicalTargets d (fun i => (s.val i).val) e

theorem isCompact_mixedPVMReachable {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    IsCompact (mixedPVMReachable d K e) := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact isCompact_purePVMReachable hd e

def pvmPhysicalIncidence (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s) :=
  (Set.univ ×ˢ pvmPhysicalSet d s) ∩
    {z | 1 - e ≤ pvmPhysicalScore (z.1 : Matrix _ _ ℂ) z.2}

set_option maxHeartbeats 800000 in
theorem isCompact_pvmPhysicalIncidence (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    IsCompact (pvmPhysicalIncidence d s e) := by
  have hi : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PVMPhysicalBlocks d s =>
        ((z.1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hscore : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PVMPhysicalBlocks d s => pvmPhysicalScore (z.1 : Matrix _ _ ℂ) z.2) := by
    simpa only [Function.comp_def] using (continuous_pvmPhysicalScore_joint d s).comp hi
  exact (isCompact_univ.prod (isCompact_pvmPhysicalSet d s)).inter_right
    (isClosed_le continuous_const hscore)

def chargedPVMPhysicalIncidence (d K : ℕ) (s : ChargedPVMShape d K) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PVMPhysicalBlocks d (fun i => (s.val i).val)) :=
  pvmPhysicalIncidence d (fun i => (s.val i).val) e

theorem isCompact_chargedPVMPhysicalIncidence (d K : ℕ)
    (s : ChargedPVMShape d K) (e : ℝ) :
    IsCompact (chargedPVMPhysicalIncidence d K s e) :=
  isCompact_pvmPhysicalIncidence d (fun i => (s.val i).val) e

/-- An encoder-preserving isometry into the full joint-outcome alphabet. -/
def trivialPVMDecoder (d : ℕ) [NeZero d] :
    Matrix ((Fin d × Fin d) × Fin 1) (Fin d × Fin 1) ℂ :=
  fun p i => (if (p.1.1, p.2) = i then 1 else 0) *
    (Pi.single (0 : Fin d) (1 : ℂ) : Fin d → ℂ) p.1.2

theorem isIsometry_trivialPVMDecoder (d : ℕ) [NeZero d] :
    IsIsometry (trivialPVMDecoder d) := by
  let row : ((Fin d × Fin d) × Fin 1) ≃ (Fin d × Fin 1) × Fin d :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun p => ((p.1.1, p.2), p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine isIsometry_of_unit_columns row id Function.injective_id
    (fun _ => (Pi.single (0 : Fin d) (1 : ℂ) : Fin d → ℂ)) (fun _ => ?_)
    (fun _ _ => rfl)
  simp [IsUnitVector, Pi.single_apply, apply_ite Complex.normSq]

/-- A real budget-one PVM architecture; no success claim is needed for nonemptiness. -/
def trivialFinPVMProtocol (d : ℕ) [NeZero d] :
    FinPVMProtocol d ![1, 1, d, d, 1, 1, 1, 1] where
  resource := fun _ => 1
  resource_unit := by
    change IsUnitVector (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
    simp [IsUnitVector]
  encA := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  encB := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  encA_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))
  encB_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))
  decA := trivialPVMDecoder d
  decB := trivialPVMDecoder d
  decA_isometry := isIsometry_trivialPVMDecoder d
  decB_isometry := isIsometry_trivialPVMDecoder d

theorem trivialFinPVMProtocol_hasFootprint (d : ℕ) [NeZero d] {K : ℕ} (hK : 1 ≤ K) :
    (trivialFinPVMProtocol d).HasFootprint K := by
  apply FinPVMProtocol.hasFootprint_of_support_charge
  simpa using hK

theorem chargedPVMShapeScores_nonempty {d K : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hK : 1 ≤ K) :
    (chargedPVMShapeScores M K).Nonempty := by
  let : NeZero d := ⟨by omega⟩
  exact ⟨_, (trivialFinPVMProtocol d).scorePVM_mem_chargedPVMShapeScores hd M
    (trivialFinPVMProtocol_hasFootprint d hK)⟩

theorem exists_pvm_score_maximizer {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinPVMProtocol d s,
      P.HasFootprint K ∧
        IsGreatest (chargedPVMShapeScores M K) (scorePVM M P.operationalChannel) := by
  obtain ⟨v, hv⟩ := (isCompact_chargedPVMShapeScores M K).exists_isGreatest
    (chargedPVMShapeScores_nonempty hd M hK)
  obtain ⟨s, P, hP, hscore⟩ := (mem_chargedPVMShapeScores_iff hd M v).mp hv.1
  exact ⟨s, P, hP, hscore ▸ hv⟩

noncomputable def pvmScoreMaximum {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : ℝ :=
  sSup (chargedPVMShapeScores M K)

theorem pvmScoreMaximum_isGreatest {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    IsGreatest (chargedPVMShapeScores M K) (pvmScoreMaximum M K) := by
  obtain ⟨s, P, _, hv⟩ := exists_pvm_score_maximizer hd hK M
  change IsGreatest _ (sSup _)
  rw [hv.csSup_eq]
  exact hv

theorem exists_pvmScoreMaximum_protocol {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinPVMProtocol d s,
      P.HasFootprint K ∧ scorePVM M P.operationalChannel = pvmScoreMaximum M K :=
  (mem_chargedPVMShapeScores_iff hd M _).mp (pvmScoreMaximum_isGreatest hd hK M).1

theorem mem_purePVMReachable_iff_le_pvmScoreMaximum {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    M ∈ purePVMReachable d K e ↔
      1 - e ≤ pvmScoreMaximum (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K := by
  constructor
  · rintro ⟨s, P, hP, he⟩
    exact he.trans ((pvmScoreMaximum_isGreatest hd hK _).2
      (P.scorePVM_mem_chargedPVMShapeScores hd _ hP))
  · intro he
    obtain ⟨s, P, hP, hscore⟩ := exists_pvmScoreMaximum_protocol hd hK
      (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    exact ⟨s, P, hP, hscore ▸ he⟩

theorem mem_mixedPVMReachable_iff_le_pvmScoreMaximum {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    M ∈ mixedPVMReachable d K e ↔
      1 - e ≤ pvmScoreMaximum (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K := by
  rw [mixedPVMReachable_eq_purePVMReachable]
  exact mem_purePVMReachable_iff_le_pvmScoreMaximum hd hK M e

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

theorem PureProtocol.scorePVM_le_pvmScoreMaximum
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hd : 2 ≤ d) {K : ℕ} (hK : 1 ≤ K) (hP : P.HasFootprint K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scorePVM M P.operationalChannel ≤ pvmScoreMaximum M K :=
  (pvmScoreMaximum_isGreatest hd hK M).2 (P.scorePVM_mem_chargedPVMShapeScores hd M hP)

/-- The attained pure score also bounds the actual common-map finite mixture. -/
theorem MixedResource.scorePVM_le_pvmScoreMaximum {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 2 ≤ d) {R K : ℕ} (hK : 1 ≤ K) (hR : m.schmidtNumberLE R)
    (hcharge : R * Fintype.card μA * Fintype.card μB ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scorePVM M (m.mixedChannel VA VB DA DB) ≤ pvmScoreMaximum M K := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hP : P.HasFootprint K := (hasFootprint_iff K (m.component k)).mpr
    ((Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hcharge)
  exact hk.trans (P.scorePVM_le_pvmScoreMaximum hd hK hP M)

end ArbitraryRegisters

noncomputable def pvmScoreDeficit {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : ℝ :=
  1 - pvmScoreMaximum M K

theorem pvmScoreDeficit_mem_Icc {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M) :
    pvmScoreDeficit M K ∈ Set.Icc 0 1 := by
  obtain ⟨s, P, _, hscore⟩ := exists_pvmScoreMaximum_protocol hd hK M
  have hs := P.scorePVM_mem_Icc hM
  rw [hscore] at hs
  change 0 ≤ 1 - pvmScoreMaximum M K ∧ 1 - pvmScoreMaximum M K ≤ 1
  constructor <;> linarith [hs.1, hs.2]

theorem pvmScoreDeficit_eq_zero_iff {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M) :
    pvmScoreDeficit M K = 0 ↔
      ∃ s : Fin 8 → ℕ, ∃ P : FinPVMProtocol d s,
        P.HasFootprint K ∧ P.PerformsPVM M := by
  let : NeZero d := ⟨by omega⟩
  constructor
  · intro hzero
    obtain ⟨s, P, hP, hscore⟩ := exists_pvmScoreMaximum_protocol hd hK M
    refine ⟨s, P, hP, (P.scorePVM_eq_one_iff_performsPVM hM).mp ?_⟩
    unfold pvmScoreDeficit at hzero
    linarith
  · rintro ⟨s, P, hP, hexact⟩
    have hone := (P.scorePVM_eq_one_iff_performsPVM hM).mpr hexact
    have hle := P.scorePVM_le_pvmScoreMaximum hd hK hP M
    have hnonneg := (pvmScoreDeficit_mem_Icc hd hK M hM).1
    unfold pvmScoreDeficit at *
    linarith

end NLQCLean
