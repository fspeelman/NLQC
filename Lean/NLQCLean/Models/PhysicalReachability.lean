import NLQCLean.Models.CompactForward
import NLQCLean.Geometry.UnitaryNormalEmbedding

/-!
# Physical reachability is Borel

Exact support compression represents all original
rank-charged protocols by countably many compact physical families whose
resource support dimensions are charged. The bound is imposed only after
compression, never on the original private spaces or on mixed supports.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section JointScore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]
variable {N : WithTop ℕ∞}

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
theorem ContDiff.scoreVector_joint {U : E → Matrix κ ι ℂ}
    {F : E → Matrix (κ × ε) ι ℂ} (hU : ContDiff ℝ N U) (hF : ContDiff ℝ N F) (e : ε) :
    ContDiff ℝ N (fun x => NLQCLean.scoreVector (U x) (F x) e) := by
  have he : (fun x => NLQCLean.scoreVector (U x) (F x) e) = fun x =>
      (Fintype.card ι : ℂ)⁻¹ * ∑ p : κ × ι, star (U x p.1 p.2) * F x (p.1, e) p.2 := by
    funext x
    rw [NLQCLean.scoreVector, frobInner_eq_sum_prod]
    rfl
  rw [he]
  exact contDiff_const.mul (_root_.ContDiff.sum fun p _ =>
    (ContDiff.matrixEntry (ContDiff.matrixConjTranspose hU) p.2 p.1).mul
      (ContDiff.matrixEntry hF (p.1, e) p.2))

omit [DecidableEq κ] [DecidableEq ε] in
theorem ContDiff.scoreU_channelOf_joint {U : E → Matrix κ ι ℂ}
    {F : E → Matrix (κ × ε) ι ℂ} (hU : ContDiff ℝ N U) (hF : ContDiff ℝ N F) :
    ContDiff ℝ N (fun x => scoreU (U x) (channelOf (F x))) := by
  have he : (fun x => scoreU (U x) (channelOf (F x))) =
      fun x => ∑ e, Complex.normSq (NLQCLean.scoreVector (U x) (F x) e) := by
    funext x
    exact scoreU_eq_sum_normSq_scoreVector (U x) (F x)
  rw [he]
  exact _root_.ContDiff.sum fun e _ =>
    ContDiff.complexNormSq (ContDiff.scoreVector_joint hU hF e)

end JointScore

theorem continuous_physicalScore_joint (d : ℕ) (s : Fin 8 → ℕ) :
    Continuous (fun z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s =>
      physicalScore z.1 z.2) := by
  have hη : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s => z.2.1) := contDiff_fst.snd'
  have hVA : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s => z.2.2.1) := contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s => z.2.2.2.1) := contDiff_fst.snd'.snd'.snd'
  have hDA : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s => z.2.2.2.2.1) := contDiff_fst.snd'.snd'.snd'.snd'
  have hDB : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s => z.2.2.2.2.2) := contDiff_snd.snd'.snd'.snd'.snd'
  have hE := ContDiff.insertResource (ιA := Fin d) (ιB := Fin d) hη
  have hEx : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun _ :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PhysicalBlocks d s =>
        exchangeMatrix (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) := contDiff_const
  have hF := ContDiff.matrixMul (ContDiff.matrixKronecker hDA hDB)
    (ContDiff.matrixMul hEx (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) hE))
  exact (ContDiff.scoreU_channelOf_joint contDiff_fst (ContDiff.matrixSubmatrix hF
    (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id)).continuous

/-- The compact target projection of one physical architecture, at a closed score threshold. -/
def physicalTargets (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ x ∈ physicalSet d s, 1 - e ≤ physicalScore (U : Matrix _ _ ℂ) x}

set_option maxHeartbeats 800000 in
theorem isCompact_physicalTargets (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    IsCompact (physicalTargets d s e) := by
  have hscore : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × PhysicalBlocks d s =>
      physicalScore (z.1 : Matrix _ _ ℂ) z.2) := by
    have hi : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × PhysicalBlocks d s =>
        ((z.1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def] using (continuous_physicalScore_joint d s).comp hi
  have hc : IsCompact ((Set.univ ×ˢ physicalSet d s) ∩
      {z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × PhysicalBlocks d s |
        1 - e ≤ physicalScore (z.1 : Matrix _ _ ℂ) z.2}) :=
    (isCompact_univ.prod (isCompact_physicalSet d s)).inter_right
      (isClosed_le continuous_const hscore)
  have hi := hc.image continuous_fst
  convert hi using 1
  ext U
  simp [physicalTargets]

/-- A support-charged finite shape gives the original rank/message footprint. -/
theorem FinProtocol.hasFootprint_of_support_charge {d K : ℕ} {s : Fin 8 → ℕ}
    (P : FinProtocol d s) (hs : s 0 * s 4 * s 5 ≤ K) : P.HasFootprint K := by
  apply (hasFootprint_iff K P.resource).mpr
  have hr : schmidtRank P.resource ≤ s 0 := by
    simpa only [Fintype.card_fin] using schmidtRank_le_card_left P.resource
  simpa only [Fintype.card_fin] using
    (Nat.mul_le_mul_right (s 5) (Nat.mul_le_mul_right (s 4) hr)).trans hs

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Only the exactly compressed support dimension is charged in this representative. -/
theorem PureProtocol.exists_support_charged_fin_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB)
    {K : ℕ} (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, s 0 * s 4 * s 5 ≤ K ∧
      ∃ Q : FinProtocol d s, P.operationalChannel = Q.operationalChannel := by
  obtain ⟨r, kA, kB, eA, eB, hr, _, _, _, _, Q, hchan⟩ := P.exists_compressed_forward
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  let s : Fin 8 → ℕ := ![r, r, kA, kB, mA, mB, eA, eB]
  let R : FinProtocol d s := Q.reindex (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
    (Equiv.refl _) (Equiv.refl _)
  refine ⟨s, ?_, R, ?_⟩
  · change r * mA * mB ≤ K
    simpa only [hr] using (hasFootprint_iff K P.resource).mp hK
  · exact hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm

end ArbitraryRegisters

/-- Actual rank-based pure reachability, with arbitrary finite architectures enumerated by size. -/
def pureReachable (d K : ℕ) (e : ℝ) : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
    P.HasFootprint K ∧ 1 - e ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel}

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

theorem PureProtocol.mem_pureReachable
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB)
    {K : ℕ} {e : ℝ} {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (hK : P.HasFootprint K) (he : 1 - e ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel) :
    U ∈ pureReachable d K e := by
  obtain ⟨s, hs, Q, hchan⟩ := P.exists_support_charged_fin_representative hK
  exact ⟨s, Q, Q.hasFootprint_of_support_charge hs, hchan ▸ he⟩

end ArbitraryRegisters

/-- Exact equality, not an enlargement: every physical point has the charged rank footprint. -/
theorem pureReachable_eq_iUnion (d K : ℕ) (e : ℝ) :
    pureReachable d K e = ⋃ s : Fin 8 → ℕ, ⋃ (_ : s 0 * s 4 * s 5 ≤ K), physicalTargets d s e := by
  ext U
  constructor
  · rintro ⟨s, P, hP, he⟩
    obtain ⟨t, ht, Q, hchan⟩ := P.exists_support_charged_fin_representative hP
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, ?_⟩⟩
    refine ⟨(Q.resource, Q.encA, Q.encB, Q.decA, Q.decB),
      ⟨Q.resource_unit, Q.encA_isometry, Q.encB_isometry, Q.decA_isometry, Q.decB_isometry⟩, ?_⟩
    change 1 - e ≤ scoreU (U : Matrix _ _ ℂ) Q.operationalChannel
    rw [← hchan]
    exact he
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    obtain ⟨hcharge, x, hx, he⟩ := Set.mem_iUnion.mp hs
    let P := PhysicalBlocks.toProtocol x hx
    exact ⟨s, P, P.hasFootprint_of_support_charge hcharge, he⟩

/-- The original pure reachable set is a countable union of compact projections. -/
theorem measurableSet_pureReachable (d K : ℕ) (e : ℝ) : MeasurableSet (pureReachable d K e) := by
  rw [pureReachable_eq_iUnion]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    (isCompact_physicalTargets d s e).isClosed.measurableSet

end NLQCLean
