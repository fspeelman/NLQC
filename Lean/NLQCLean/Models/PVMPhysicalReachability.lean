import NLQCLean.Models.CompactForward
import NLQCLean.Models.PVMForwardCompression
import NLQCLean.Models.ProjectiveScoreSemantics
import NLQCLean.Models.Targets
import NLQCLean.Geometry.UnitaryNormalEmbedding

/-!
# Pure PVM reachability is Borel

Exact resource-support and encoder compression represents every
pure PVM protocol with arbitrary finite original registers by one of
countably many compact physical families.  The logical output on each side
is the full ordered-outcome type `Fin d × Fin d`; the rank/message footprint
charges only the resource Schmidt rank and the two message dimensions.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Finite-cardinality PVM architectures.  The shape coordinates are,
in order, the two resource registers, two retained encoder registers, two
message registers, and two discarded decoder environments. -/
abbrev FinPVMProtocol (d : ℕ) (s : Fin 8 → ℕ) :=
  PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin d × Fin d) (Fin d × Fin d)
    (Fin (s 6)) (Fin (s 7))

/-- The five physical blocks of a PVM protocol of fixed finite shape. -/
abbrev PVMPhysicalBlocks (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin (s 0) × Fin (s 1) → ℂ) ×
    Matrix (Fin (s 2) × Fin (s 4)) (Fin d × Fin (s 0)) ℂ ×
    Matrix (Fin (s 3) × Fin (s 5)) (Fin d × Fin (s 1)) ℂ ×
    Matrix ((Fin d × Fin d) × Fin (s 6)) (Fin (s 2) × Fin (s 5)) ℂ ×
    Matrix ((Fin d × Fin d) × Fin (s 7)) (Fin (s 3) × Fin (s 4)) ℂ

/-- Independent unit-sphere and Stiefel constraints for one PVM shape. -/
def pvmPhysicalSet (d : ℕ) (s : Fin 8 → ℕ) : Set (PVMPhysicalBlocks d s) :=
  {η | IsUnitVector η} ×ˢ
    ({VA | IsIsometry VA} ×ˢ ({VB | IsIsometry VB} ×ˢ
      ({DA | IsIsometry DA} ×ˢ {DB | IsIsometry DB})))

theorem isCompact_pvmPhysicalSet (d : ℕ) (s : Fin 8 → ℕ) :
    IsCompact (pvmPhysicalSet d s) :=
  (isCompact_unitVectors _).prod ((isCompact_isometries _ _).prod
    ((isCompact_isometries _ _).prod
      ((isCompact_isometries _ _).prod (isCompact_isometries _ _))))

/-- A constrained physical point gives a PVM protocol in the original model. -/
def PVMPhysicalBlocks.toProtocol {d : ℕ} {s : Fin 8 → ℕ}
    (x : PVMPhysicalBlocks d s) (hx : x ∈ pvmPhysicalSet d s) : FinPVMProtocol d s where
  resource := x.1
  resource_unit := hx.1
  encA := x.2.1
  encB := x.2.2.1
  encA_isometry := hx.2.1
  encB_isometry := hx.2.2.1
  decA := x.2.2.2.1
  decB := x.2.2.2.2
  decA_isometry := hx.2.2.2.1
  decB_isometry := hx.2.2.2.2

/-- The ordered rank-one PVM score on the whole five-block ambient space. -/
noncomputable def pvmPhysicalScore {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {s : Fin 8 → ℕ} (x : PVMPhysicalBlocks d s) : ℝ :=
  scorePVM M (operationalChannel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)

/-- Joint continuity in the basis lift and all five physical blocks. -/
theorem continuous_pvmPhysicalScore_joint (d : ℕ) (s : Fin 8 → ℕ) :
    Continuous (fun z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ ×
        PVMPhysicalBlocks d s => pvmPhysicalScore z.1 z.2) := by
  have hη : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s => z.2.1) :=
    contDiff_fst.snd'
  have hVA : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s => z.2.2.1) :=
    contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s => z.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'
  have hDA : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s =>
        z.2.2.2.2.1) := contDiff_fst.snd'.snd'.snd'.snd'
  have hDB : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s =>
        z.2.2.2.2.2) := contDiff_snd.snd'.snd'.snd'.snd'
  have hE := ContDiff.insertResource (ιA := Fin d) (ιB := Fin d) hη
  have hEx : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun _ :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s =>
        exchangeMatrix (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) :=
    contDiff_const
  have hF := ContDiff.matrixMul (ContDiff.matrixKronecker hDA hDB)
    (ContDiff.matrixMul hEx (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) hE))
  exact (ContDiff.scorePVM_channelOf_joint contDiff_fst hF).continuous

/-- The compact target projection of one physical architecture at a closed
PVM-score threshold. -/
def pvmPhysicalTargets (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ∃ x ∈ pvmPhysicalSet d s,
    1 - e ≤ pvmPhysicalScore (M : Matrix _ _ ℂ) x}

set_option maxHeartbeats 800000 in
theorem isCompact_pvmPhysicalTargets (d : ℕ) (s : Fin 8 → ℕ) (e : ℝ) :
    IsCompact (pvmPhysicalTargets d s e) := by
  have hscore : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
      PVMPhysicalBlocks d s => pvmPhysicalScore (z.1 : Matrix _ _ ℂ) z.2) := by
    have hi : Continuous (fun z : Matrix.unitaryGroup (Fin d × Fin d) ℂ ×
        PVMPhysicalBlocks d s =>
          ((z.1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def] using (continuous_pvmPhysicalScore_joint d s).comp hi
  have hc : IsCompact ((Set.univ ×ˢ pvmPhysicalSet d s) ∩
      {z : Matrix.unitaryGroup (Fin d × Fin d) ℂ × PVMPhysicalBlocks d s |
        1 - e ≤ pvmPhysicalScore (z.1 : Matrix _ _ ℂ) z.2}) :=
    (isCompact_univ.prod (isCompact_pvmPhysicalSet d s)).inter_right
      (isClosed_le continuous_const hscore)
  have hi := hc.image continuous_fst
  convert hi using 1
  ext M
  simp [pvmPhysicalTargets]

/-- A support-charged finite PVM shape has the advertised footprint. -/
theorem FinPVMProtocol.hasFootprint_of_support_charge {d K : ℕ} {s : Fin 8 → ℕ}
    (P : FinPVMProtocol d s) (hs : s 0 * s 4 * s 5 ≤ K) :
    HasFootprint K P.resource (Fin (s 4)) (Fin (s 5)) := by
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

/-- Exact resource-support compression and finite reindexing preserve the
channel while charging only the original rank/message footprint. -/
theorem PureProtocol.exists_support_charged_fin_pvm_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB)
    {K : ℕ} (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, s 0 * s 4 * s 5 ≤ K ∧
      ∃ Q : FinPVMProtocol d s, P.operationalChannel = Q.operationalChannel := by
  obtain ⟨r, kA, kB, hr, _, _, Q, _, hchan⟩ := P.exists_compressed_pvm_encoders
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  let ea := Fintype.card eA
  let eb := Fintype.card eB
  let s : Fin 8 → ℕ := ![r, r, kA, kB, mA, mB, ea, eb]
  let R : FinPVMProtocol d s := Q.reindex (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
    (Fintype.equivFin eA).symm (Fintype.equivFin eB).symm
  refine ⟨s, ?_, R, ?_⟩
  · change r * mA * mB ≤ K
    simpa only [hr] using (hasFootprint_iff K P.resource).mp hK
  · exact hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Fintype.equivFin eA).symm (Fintype.equivFin eB).symm).symm

end ArbitraryRegisters

/-- Actual rank-based pure PVM reachability, enumerated by finite register
cardinalities after exact compression. -/
def purePVMReachable (d K : ℕ) (e : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ∃ s : Fin 8 → ℕ, ∃ P : FinPVMProtocol d s,
    HasFootprint K P.resource (Fin (s 4)) (Fin (s 5)) ∧
      1 - e ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel}

section ArbitraryRegisters

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Every arbitrary-finite-register pure PVM protocol belongs to the finite
enumerated reachable set at the same footprint and score threshold. -/
theorem PureProtocol.mem_purePVMReachable
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB)
    {K : ℕ} {e : ℝ} {M : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (hK : P.HasFootprint K)
    (he : 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel) :
    M ∈ purePVMReachable d K e := by
  obtain ⟨s, hs, Q, hchan⟩ := P.exists_support_charged_fin_pvm_representative hK
  exact ⟨s, Q, Q.hasFootprint_of_support_charge hs, hchan ▸ he⟩

end ArbitraryRegisters

/-- Exact equality with a countable union of compact physical target
projections. -/
theorem purePVMReachable_eq_iUnion (d K : ℕ) (e : ℝ) :
    purePVMReachable d K e =
      ⋃ s : Fin 8 → ℕ, ⋃ (_ : s 0 * s 4 * s 5 ≤ K), pvmPhysicalTargets d s e := by
  ext M
  constructor
  · rintro ⟨s, P, hP, he⟩
    obtain ⟨t, ht, Q, hchan⟩ := P.exists_support_charged_fin_pvm_representative hP
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, ?_⟩⟩
    refine ⟨(Q.resource, Q.encA, Q.encB, Q.decA, Q.decB),
      ⟨Q.resource_unit, Q.encA_isometry, Q.encB_isometry,
        Q.decA_isometry, Q.decB_isometry⟩, ?_⟩
    change 1 - e ≤ scorePVM (M : Matrix _ _ ℂ) Q.operationalChannel
    rw [← hchan]
    exact he
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    obtain ⟨hcharge, x, hx, he⟩ := Set.mem_iUnion.mp hs
    let P := PVMPhysicalBlocks.toProtocol x hx
    exact ⟨s, P, P.hasFootprint_of_support_charge hcharge, he⟩

/-- Pure PVM reachability is Borel for every dimension, budget, and
real score tolerance. -/
theorem measurableSet_purePVMReachable (d K : ℕ) (e : ℝ) :
    MeasurableSet (purePVMReachable d K e) := by
  rw [purePVMReachable_eq_iUnion]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    (isCompact_pvmPhysicalTargets d s e).isClosed.measurableSet

/-- The matrix-level phase identity, packaged for unitary-group elements
without specializing the finite outcome type. -/
theorem scorePVM_unitary_mul_phase {δ : Type*} [Fintype δ] [DecidableEq δ]
    (M Δ : Matrix.unitaryGroup δ ℂ)
    (hΔ : (Δ : Matrix δ δ ℂ) ∈ phaseUnitaries δ)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    scorePVM ((M * Δ : Matrix.unitaryGroup δ ℂ) : Matrix δ δ ℂ) N =
      scorePVM (M : Matrix δ δ ℂ) N := by
  obtain ⟨z, hz, hΔeq⟩ := hΔ
  have hzsq : ∀ i, Complex.normSq (z i) = 1 := by
    intro i
    rw [Complex.normSq_eq_norm_sq, hz i]
    norm_num
  have hmul : ((M * Δ : Matrix.unitaryGroup δ ℂ) : Matrix δ δ ℂ) =
      (M : Matrix δ δ ℂ) * (Δ : Matrix δ δ ℂ) := rfl
  rw [hmul, hΔeq]
  exact scorePVM_mul_diagonal_phase (M : Matrix δ δ ℂ) z hzsq N

set_option maxHeartbeats 800000 in
/-- Reachability depends only on the ordered rank-one projectors, hence is
invariant under independent unit phases on the columns of a basis lift. -/
theorem mul_phase_mem_purePVMReachable_iff {d K : ℕ} {e : ℝ}
    (M Δ : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hΔ : (Δ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈
      phaseUnitaries (Fin d × Fin d)) :
    M * Δ ∈ purePVMReachable d K e ↔ M ∈ purePVMReachable d K e := by
  constructor <;> rintro ⟨s, P, hP, he⟩ <;> refine ⟨s, P, hP, ?_⟩
  · rwa [scorePVM_unitary_mul_phase M Δ hΔ] at he
  · rwa [scorePVM_unitary_mul_phase M Δ hΔ]

end NLQCLean
