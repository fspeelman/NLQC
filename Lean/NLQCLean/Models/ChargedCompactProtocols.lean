import NLQCLean.Models.MixedReachability
import NLQCLean.Models.ProtocolMetrics
import NLQCLean.Models.UnitaryTask

/-!
# Compact parameter families with the rank/message budget

The finite box is restricted by its resource-support and two message charges.
Every physical point in this family is a protocol within the budget,
and exact compression puts every original pure channel in the family.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Bounded architectures whose resource support and both messages are charged. -/
abbrev ChargedShape (d K : ℕ) :=
  {s : BoundedShape d K // (s 0).val * (s 4).val * (s 5).val ≤ K}

/-- The score set of actual physical protocols in the finite charged family. -/
def chargedShapeScores {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : Set ℝ :=
  ⋃ s : ChargedShape d K, shapeScores U (fun i => (s.val i).val)

theorem isCompact_chargedShapeScores {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) :
    IsCompact (chargedShapeScores U K) := by
  classical
  exact isCompact_iUnion fun s : ChargedShape d K =>
    isCompact_shapeScores U (fun i => (s.val i).val)

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Exact channel compression retains the finite support-charge certificate. -/
theorem PureProtocol.score_mem_chargedShapeScores
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hd : 2 ≤ d) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {K : ℕ} (hK : P.HasFootprint K) :
    scoreU U P.operationalChannel ∈ chargedShapeScores U K := by
  obtain ⟨s, hs, hcharge, Q, _, hchan⟩ :=
    P.exists_bounded_support_charged_fin_representative hd K hK
  rw [hchan]
  apply Set.mem_iUnion.mpr
  refine ⟨⟨fun i => ⟨s i, Nat.lt_succ_of_le (hs i).2⟩, hcharge⟩, ?_⟩
  exact Q.score_mem_shapeScores U

end ArbitraryRegisters

/-- Both directions identify actual scores; no larger-budget points occur. -/
theorem mem_chargedShapeScores_iff {d K : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (v : ℝ) :
    v ∈ chargedShapeScores U K ↔
      ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
        P.HasFootprint K ∧ scoreU U P.operationalChannel = v := by
  constructor
  · intro hv
    obtain ⟨s, x, hx, hscore⟩ := Set.mem_iUnion.mp hv
    exact ⟨_, PhysicalBlocks.toProtocol x hx,
      (PhysicalBlocks.toProtocol x hx).hasFootprint_of_support_charge s.property,
      hscore⟩
  · rintro ⟨s, P, hK, rfl⟩
    exact P.score_mem_chargedShapeScores hd U hK

/-- Exact finite representation of the target score-threshold set. -/
theorem pureReachable_eq_charged_iUnion {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    pureReachable d K e =
      ⋃ s : ChargedShape d K, physicalTargets d (fun i => (s.val i).val) e := by
  ext U
  constructor
  · rintro ⟨s, P, hK, he⟩
    obtain ⟨t, ht, hcharge, Q, _, hchan⟩ :=
      P.exists_bounded_support_charged_fin_representative hd K hK
    refine Set.mem_iUnion.mpr
      ⟨⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i).2⟩, hcharge⟩,
        (Q.resource, Q.encA, Q.encB, Q.decA, Q.decB),
        ⟨Q.resource_unit, Q.encA_isometry, Q.encB_isometry,
          Q.decA_isometry, Q.decB_isometry⟩, ?_⟩
    change 1 - e ≤ scoreU (U : Matrix _ _ ℂ) Q.operationalChannel
    rw [← hchan]
    exact he
  · intro h
    obtain ⟨s, x, hx, he⟩ := Set.mem_iUnion.mp h
    exact ⟨_, PhysicalBlocks.toProtocol x hx,
      (PhysicalBlocks.toProtocol x hx).hasFootprint_of_support_charge s.property, he⟩

/-- Score-threshold reachability is compact for the original pure model. -/
theorem isCompact_pureReachable {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    IsCompact (pureReachable d K e) := by
  classical
  rw [pureReachable_eq_charged_iUnion hd]
  exact isCompact_iUnion fun s : ChargedShape d K =>
    isCompact_physicalTargets d (fun i => (s.val i).val) e

/-- Best-component selection gives the same compact set for common-map mixtures. -/
theorem isCompact_mixedReachable {d K : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    IsCompact (mixedReachable d K e) := by
  rw [mixedReachable_eq_pureReachable]
  exact isCompact_pureReachable hd e

/-- Closed target/protocol incidence for a fixed physical architecture. -/
def physicalIncidence (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ × PhysicalBlocks d s) :=
  (Set.univ ×ˢ physicalSet d s) ∩
    {z | 1 - e ≤ physicalScore (z.1 : Matrix _ _ ℂ) z.2}

set_option maxHeartbeats 800000 in
theorem isCompact_physicalIncidence (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    IsCompact (physicalIncidence d s e) := by
  have hi : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PhysicalBlocks d s =>
        ((z.1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hscore : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PhysicalBlocks d s => physicalScore (z.1 : Matrix _ _ ℂ) z.2) := by
    simpa only [Function.comp_def] using (continuous_physicalScore_joint d s).comp hi
  exact (isCompact_univ.prod (isCompact_physicalSet d s)).inter_right
    (isClosed_le continuous_const hscore)

/-- The closed target/protocol incidence set in each charged architecture. -/
def chargedPhysicalIncidence (d K : ℕ) (s : ChargedShape d K) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PhysicalBlocks d (fun i => (s.val i).val)) :=
  physicalIncidence d (fun i => (s.val i).val) e

theorem isCompact_chargedPhysicalIncidence (d K : ℕ) (s : ChargedShape d K) (e : ℝ) :
    IsCompact (chargedPhysicalIncidence d K s e) :=
  isCompact_physicalIncidence d (fun i => (s.val i).val) e

/-- A physical protocol with one-dimensional resource and messages. -/
def identityFinProtocol (d : ℕ) : FinProtocol d ![1, 1, d, d, 1, 1, 1, 1] where
  resource := fun _ => 1
  resource_unit := by
    change IsUnitVector (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
    simp [IsUnitVector]
  encA := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  encB := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  encA_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))
  encB_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))
  decA := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  decB := (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
  decA_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))
  decB_isometry := (isIsometry_one : IsIsometry (1 : Matrix (Fin d × Fin 1) _ ℂ))

theorem identityFinProtocol_hasFootprint (d : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    (identityFinProtocol d).HasFootprint K := by
  apply FinProtocol.hasFootprint_of_support_charge
  simpa using hK

/-- Nonemptiness is witnessed by a real budget-one protocol. -/
theorem chargedShapeScores_nonempty {d K : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hK : 1 ≤ K) :
    (chargedShapeScores U K).Nonempty :=
  ⟨_, (identityFinProtocol d).score_mem_chargedShapeScores hd U
    (identityFinProtocol_hasFootprint d hK)⟩

/-- The maximum is attained by an actual pure protocol with footprint at most K. -/
theorem exists_unitary_score_maximizer {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
      P.HasFootprint K ∧
        IsGreatest (chargedShapeScores U K) (scoreU U P.operationalChannel) := by
  obtain ⟨v, hv⟩ := (isCompact_chargedShapeScores U K).exists_isGreatest
    (chargedShapeScores_nonempty hd U hK)
  obtain ⟨s, P, hP, hscore⟩ := (mem_chargedShapeScores_iff hd U v).mp hv.1
  exact ⟨s, P, hP, hscore ▸ hv⟩

/-- The best normalized Choi score over the exact charged physical family. -/
noncomputable def unitaryScoreMaximum {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : ℝ :=
  sSup (chargedShapeScores U K)

theorem unitaryScoreMaximum_isGreatest {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    IsGreatest (chargedShapeScores U K) (unitaryScoreMaximum U K) := by
  obtain ⟨s, P, _, hv⟩ := exists_unitary_score_maximizer hd hK U
  change IsGreatest _ (sSup _)
  rw [hv.csSup_eq]
  exact hv

theorem exists_unitaryScoreMaximum_protocol {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
      P.HasFootprint K ∧ scoreU U P.operationalChannel = unitaryScoreMaximum U K :=
  (mem_chargedShapeScores_iff hd U _).mp (unitaryScoreMaximum_isGreatest hd hK U).1

theorem mem_pureReachable_iff_le_unitaryScoreMaximum {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    U ∈ pureReachable d K e ↔
      1 - e ≤ unitaryScoreMaximum (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K := by
  constructor
  · rintro ⟨s, P, hP, he⟩
    exact he.trans ((unitaryScoreMaximum_isGreatest hd hK _).2
      (P.score_mem_chargedShapeScores hd _ hP))
  · intro he
    obtain ⟨s, P, hP, hscore⟩ := exists_unitaryScoreMaximum_protocol hd hK
      (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    exact ⟨s, P, hP, hscore ▸ he⟩

theorem mem_mixedReachable_iff_le_unitaryScoreMaximum {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    U ∈ mixedReachable d K e ↔
      1 - e ≤ unitaryScoreMaximum (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K := by
  rw [mixedReachable_eq_pureReachable]
  exact mem_pureReachable_iff_le_unitaryScoreMaximum hd hK U e

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

theorem PureProtocol.score_le_unitaryScoreMaximum
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hd : 2 ≤ d) {K : ℕ} (hK : 1 ≤ K) (hP : P.HasFootprint K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scoreU U P.operationalChannel ≤ unitaryScoreMaximum U K :=
  (unitaryScoreMaximum_isGreatest hd hK U).2 (P.score_mem_chargedShapeScores hd U hP)

/-- Affinity bounds the actual mixed score by the attained pure optimum. -/
theorem MixedResource.score_le_unitaryScoreMaximum {n : ℕ}
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 2 ≤ d) {R K : ℕ} (hK : 1 ≤ K) (hR : m.schmidtNumberLE R)
    (hcharge : R * Fintype.card μA * Fintype.card μB ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scoreU U (m.mixedChannel VA VB DA DB) ≤ unitaryScoreMaximum U K := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB U
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hP : P.HasFootprint K := (hasFootprint_iff K (m.component k)).mpr
    ((Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hcharge)
  exact hk.trans (P.score_le_unitaryScoreMaximum hd hK hP U)

end ArbitraryRegisters

/-- The least normalized Choi deficit, using the witnessed score maximum. -/
noncomputable def unitaryScoreDeficit {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : ℝ :=
  1 - unitaryScoreMaximum U K

theorem unitaryScoreDeficit_mem_Icc {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : IsIsometry U) :
    unitaryScoreDeficit U K ∈ Set.Icc 0 1 := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨s, P, _, hscore⟩ := exists_unitaryScoreMaximum_protocol hd hK U
  have hF := P.isIsometry_globalIsometry.submatrix_equiv
    (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _)
  have hs := scoreU_mem_Icc hU hF
  change 0 ≤ 1 - unitaryScoreMaximum U K ∧ 1 - unitaryScoreMaximum U K ≤ 1
  change scoreU U P.operationalChannel ∈ Set.Icc 0 1 at hs
  rw [hscore] at hs
  constructor <;> linarith [hs.1, hs.2]

/-- Zero optimum deficit is equivalent to an exact implementation within budget. -/
theorem unitaryScoreDeficit_eq_zero_iff {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hU : IsIsometry U) :
    unitaryScoreDeficit U K = 0 ↔
      ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
        P.HasFootprint K ∧ P.PerformsUnitary U := by
  let : NeZero d := ⟨by omega⟩
  constructor
  · intro hzero
    obtain ⟨s, P, hP, hscore⟩ := exists_unitaryScoreMaximum_protocol hd hK U
    refine ⟨s, P, hP, ?_⟩
    have hone : scoreU U P.operationalChannel = 1 := by
      unfold unitaryScoreDeficit at hzero
      linarith
    exact (scoreU_eq_one_iff_channelOf_eq hU
      (P.isIsometry_globalIsometry.submatrix_equiv
        (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _))).mp hone
  · rintro ⟨s, P, hP, hexact⟩
    have hone : scoreU U P.operationalChannel = 1 := by
      change P.operationalChannel = adConj U at hexact
      rw [hexact]
      exact scoreU_adConj_self hU
    have hle := P.score_le_unitaryScoreMaximum hd hK hP U
    have hnonneg := (unitaryScoreDeficit_mem_Icc hd hK U hU).1
    unfold unitaryScoreDeficit at *
    linarith

end NLQCLean
