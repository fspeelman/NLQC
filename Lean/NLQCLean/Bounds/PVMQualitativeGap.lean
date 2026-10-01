import NLQCLean.Exact.PVMHardTarget
import NLQCLean.Models.PVMPhysicalReachability
import NLQCLean.Models.ProjectiveTV

/-!
# Unconditional uniform fixed-target PVM gaps

Exact support compression, including the decoder environments
with the full ordered-outcome output type, places every protocol of footprint
at most `K` in a finite box of compact physical families with all dimensions at
most `d³K`. At the fixed exactly impossible target every physical point has score strictly below one,
so the compact maximum is below one. Score affinity transfers the same gap to
finite mixed resources, and `Δ ≥ 1 − q` transfers it to worst-case joint TV. The
target is chosen before every `K`; no external mathematical premise is used.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section Compression

variable {d : ℕ} {ρA ρB κA κB μA μB oA oB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype oA] [Fintype oB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq oA] [DecidableEq oB]
variable [DecidableEq εA] [DecidableEq εB]

/-- Exact compression of resource, encoders and decoder environments with an
arbitrary logical output type on each side. -/
theorem PureProtocol.exists_compressed_pvm_forward
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB oA oB εA εB) :
    ∃ r kA kB eA eB : ℕ, r = schmidtRank P.resource ∧
      kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      eA ≤ Fintype.card oA * (kA * Fintype.card μB) ∧
      eB ≤ Fintype.card oB * (kB * Fintype.card μA) ∧
      ∃ Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
        μA μB oA oB (Fin eA) (Fin eB),
        P.operationalChannel = Q.operationalChannel := by
  have hfac := exists_resource_support_factorization P.resource P.resource_unit
  generalize hr : schmidtRank P.resource = r at hfac
  obtain ⟨JA, JB, η, hJA, hJB, hη, hresource⟩ := hfac
  let VA0 := P.encA * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JA)
  let VB0 := P.encB * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JB)
  have hVA0 : IsIsometry VA0 := P.encA_isometry.mul (isIsometry_one.kronecker hJA)
  have hVB0 : IsIsometry VB0 := P.encB_isometry.mul (isIsometry_one.kronecker hJB)
  obtain ⟨kA, hkA, KA, VA, hKA, hA⟩ := exists_left_coefficient_factorization VA0
  obtain ⟨kB, hkB, KB, VB, hKB, hB⟩ := exists_left_coefficient_factorization VB0
  have hVA : IsIsometry VA :=
    ((hKA.kronecker isIsometry_one).mul_iff VA).mp (hA ▸ hVA0)
  have hVB : IsIsometry VB :=
    ((hKB.kronecker isIsometry_one).mul_iff VB).mp (hB ▸ hVB0)
  let DA0 := P.decA * (KA ⊗ₖ (1 : Matrix μB μB ℂ))
  let DB0 := P.decB * (KB ⊗ₖ (1 : Matrix μA μA ℂ))
  have hDA0 : IsIsometry DA0 := P.decA_isometry.mul (hKA.kronecker isIsometry_one)
  have hDB0 : IsIsometry DB0 := P.decB_isometry.mul (hKB.kronecker isIsometry_one)
  obtain ⟨eA, heA, EA, DA, hEA, hDA⟩ := exists_right_coefficient_factorization DA0
  obtain ⟨eB, heB, EB, DB, hEB, hDB⟩ := exists_right_coefficient_factorization DB0
  have hDA' : IsIsometry DA :=
    ((isIsometry_one.kronecker hEA).mul_iff DA).mp (hDA ▸ hDA0)
  have hDB' : IsIsometry DB :=
    ((isIsometry_one.kronecker hEB).mul_iff DB).mp (hDB ▸ hDB0)
  let Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
      μA μB oA oB (Fin eA) (Fin eB) :=
    ⟨η, hη, VA, VB, hVA, hVB, DA, DB, hDA', hDB'⟩
  refine ⟨r, kA, kB, eA, eB, rfl, ?_, ?_, ?_, ?_, Q, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkA
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkB
  · simpa only [Fintype.card_prod, Fintype.card_fin] using heA
  · simpa only [Fintype.card_prod, Fintype.card_fin] using heB
  · have hF : P.globalIsometry =
        (((1 : Matrix oA oA ℂ) ⊗ₖ EA) ⊗ₖ ((1 : Matrix oB oB ℂ) ⊗ₖ EB)) * Q.globalIsometry := by
      change NLQCLean.globalIsometry P.resource P.encA P.encB P.decA P.decB =
        _ * NLQCLean.globalIsometry η VA VB DA DB
      rw [hresource, globalIsometry_resource_inclusions]
      change NLQCLean.globalIsometry η VA0 VB0 P.decA P.decB = _
      rw [hA, hB, globalIsometry_private_inclusions]
      change NLQCLean.globalIsometry η VA VB DA0 DB0 = _
      rw [hDA, hDB]
      simp only [NLQCLean.globalIsometry, NLQCLean.decoder, Matrix.mul_kronecker_mul,
        Matrix.mul_assoc]
    have hFreg :
        P.globalIsometry.submatrix (outputRegroup oA oB εA εB) id =
          ((1 : Matrix (oA × oB) (oA × oB) ℂ) ⊗ₖ (EA ⊗ₖ EB)) *
            Q.globalIsometry.submatrix (outputRegroup oA oB (Fin eA) (Fin eB)) id :=
      (congrArg (fun F : Matrix ((oA × εA) × (oB × εB)) (Fin d × Fin d) ℂ =>
        F.submatrix (outputRegroup oA oB εA εB) id) hF).trans
          (regroup_environment_inclusions EA EB Q.globalIsometry)
    change channelOf (P.globalIsometry.submatrix (outputRegroup oA oB εA εB) id) =
      channelOf (Q.globalIsometry.submatrix (outputRegroup oA oB (Fin eA) (Fin eB)) id)
    rw [hFreg]
    exact channelOf_environment_inclusion (EA ⊗ₖ EB) (hEA.kronecker hEB) _

end Compression

section FiniteRepresentative

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Finite PVM representative: every protocol of footprint at most `K`, with
arbitrary finite original registers, has the same channel as a finite-cardinality
PVM architecture whose dimensions are all at most `d³K`. -/
theorem PureProtocol.exists_bounded_support_charged_fin_pvm_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hd : 2 ≤ d) (K : ℕ) (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, (∀ i, s i ≤ d ^ 3 * K) ∧
      s 0 * s 4 * s 5 ≤ K ∧
      ∃ Q : FinPVMProtocol d s, P.operationalChannel = Q.operationalChannel := by
  obtain ⟨r, kA, kB, eA, eB, hr, hkA, hkB, heA, heB, Q, hchan⟩ :=
    P.exists_compressed_pvm_forward
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  have hdpos : 0 < d := by omega
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : d * r ≤ kA * mA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : d * r ≤ kB * mB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hdpos hrpos).trans_le hencA)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hdpos hrpos).trans_le hencB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
  have hrm : r * mA ≤ K := (Nat.le_mul_of_pos_right _ hmb).trans hfoot
  have hrK : r ≤ K := (Nat.le_mul_of_pos_right _ hma).trans hrm
  have hmAK : mA ≤ K := (Nat.le_mul_of_pos_left _ hrpos).trans hrm
  have hmBK : mB ≤ K := (Nat.le_mul_of_pos_left _ (Nat.mul_pos hrpos hma)).trans hfoot
  have hqa : kA * mB ≤ d * K := by
    calc
      kA * mB ≤ (d * r * mA) * mB := Nat.mul_le_mul_right mB hkA
      _ ≤ d * K := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d hfoot
  have hqb : kB * mA ≤ d * K := by
    calc
      kB * mA ≤ (d * r * mB) * mA := Nat.mul_le_mul_right mA hkB
      _ ≤ d * K := by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left d hfoot
  have hd13 : d ≤ d ^ 3 := by
    calc d = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ 3 := Nat.pow_le_pow_right hdpos (by norm_num)
  have hKbox : K ≤ d ^ 3 * K := Nat.le_mul_of_pos_left K (pow_pos hdpos 3)
  have hdKbox : d * K ≤ d ^ 3 * K := Nat.mul_le_mul_right K hd13
  have hrbox : r ≤ d ^ 3 * K := hrK.trans hKbox
  have hmabox : mA ≤ d ^ 3 * K := hmAK.trans hKbox
  have hmbbox : mB ≤ d ^ 3 * K := hmBK.trans hKbox
  have hkabox : kA ≤ d ^ 3 * K := ((Nat.le_mul_of_pos_right kA hmb).trans hqa).trans hdKbox
  have hkbbox : kB ≤ d ^ 3 * K := ((Nat.le_mul_of_pos_right kB hma).trans hqb).trans hdKbox
  have heabox : eA ≤ d ^ 3 * K := by
    calc
      eA ≤ (d * d) * (kA * mB) := by
        simpa only [Fintype.card_prod, Fintype.card_fin] using heA
      _ ≤ (d * d) * (d * K) := Nat.mul_le_mul_left _ hqa
      _ = d ^ 3 * K := by ring
  have hebbox : eB ≤ d ^ 3 * K := by
    calc
      eB ≤ (d * d) * (kB * mA) := by
        simpa only [Fintype.card_prod, Fintype.card_fin] using heB
      _ ≤ (d * d) * (d * K) := Nat.mul_le_mul_left _ hqb
      _ = d ^ 3 * K := by ring
  let s : Fin 8 → ℕ := ![r, r, kA, kB, mA, mB, eA, eB]
  let R : FinPVMProtocol d s := Q.reindex (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
    (Equiv.refl _) (Equiv.refl _)
  refine ⟨s, ?_, ?_, R, ?_⟩
  · intro i
    fin_cases i <;> simp only [s] <;> assumption
  · exact hfoot
  · exact hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm

/-- The channel-preserving finite PVM representative, forgetting only the
additional architecture support-charge certificate. -/
theorem PureProtocol.exists_bounded_fin_pvm_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (hd : 2 ≤ d) (K : ℕ) (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, (∀ i, s i ≤ d ^ 3 * K) ∧
      ∃ Q : FinPVMProtocol d s, P.operationalChannel = Q.operationalChannel := by
  obtain ⟨s, hs, _, Q, hchan⟩ :=
    P.exists_bounded_support_charged_fin_pvm_representative hd K hK
  exact ⟨s, hs, Q, hchan⟩

end FiniteRepresentative

section CompactFamily

variable {d : ℕ}

theorem continuous_pvmPhysicalScore (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (s : Fin 8 → ℕ) : Continuous (pvmPhysicalScore M (s := s)) := by
  have hi : Continuous (fun x : PVMPhysicalBlocks d s => (M, x)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using (continuous_pvmPhysicalScore_joint d s).comp hi

/-- The PVM score image of one finite physical shape. -/
def pvmShapeScores (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (s : Fin 8 → ℕ) : Set ℝ :=
  pvmPhysicalScore M '' pvmPhysicalSet d s

theorem isCompact_pvmShapeScores (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (s : Fin 8 → ℕ) : IsCompact (pvmShapeScores M s) :=
  (isCompact_pvmPhysicalSet d s).image (continuous_pvmPhysicalScore M s)

theorem FinPVMProtocol.score_mem_pvmShapeScores {s : Fin 8 → ℕ} (P : FinPVMProtocol d s)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scorePVM M P.operationalChannel ∈ pvmShapeScores M s :=
  ⟨(P.resource, P.encA, P.encB, P.decA, P.decB),
    ⟨P.resource_unit, P.encA_isometry, P.encB_isometry, P.decA_isometry, P.decB_isometry⟩, rfl⟩

/-- The finite box of PVM shapes with all dimensions at most `d³K`. -/
abbrev BoundedPVMShape (d K : ℕ) := Fin 8 → Fin (d ^ 3 * K + 1)

/-- The finite union of compact PVM score images, with zero adjoined. Extra shapes
in the box are allowed; no footprint claim is made for all of its points. -/
def boundedPVMShapeScores (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : Set ℝ :=
  (⋃ s : BoundedPVMShape d K, pvmShapeScores M (fun i => (s i).val)) ∪ {0}

theorem isCompact_boundedPVMShapeScores (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (K : ℕ) : IsCompact (boundedPVMShapeScores M K) := by
  unfold boundedPVMShapeScores
  apply IsCompact.union
  · exact isCompact_iUnion (fun s : BoundedPVMShape d K =>
      isCompact_pvmShapeScores M (fun i => (s i).val))
  · exact isCompact_singleton

theorem boundedPVMShapeScores_nonempty (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (K : ℕ) : (boundedPVMShapeScores M K).Nonempty := ⟨0, Or.inr rfl⟩

/-- Every budget-K pure PVM score lies in the compact bounded union. -/
theorem PureProtocol.scorePVM_mem_boundedPVMShapeScores (hd : 2 ≤ d)
    {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (hK : P.HasFootprint K) :
    scorePVM M P.operationalChannel ∈ boundedPVMShapeScores M K := by
  obtain ⟨s, hs, Q, hchan⟩ := P.exists_bounded_fin_pvm_representative hd K hK
  rw [hchan]
  apply Or.inl
  apply Set.mem_iUnion.mpr
  refine ⟨fun i => ⟨s i, Nat.lt_succ_of_le (hs i)⟩, ?_⟩
  exact Q.score_mem_pvmShapeScores M

end CompactFamily

section Gaps

/-- A uniform PVM score gap for all pure protocols of footprint at most `K`, with every
finite original register type quantified after the gap. -/
def PurePVMScoreGap {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB),
    P.HasFootprint K → scorePVM M P.operationalChannel ≤ 1 - e

/-- The same score gap for finite mixed resources with common isometric local maps,
charging the common Schmidt number and both complete message dimensions. -/
def MixedPVMScoreGap {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
    ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
      scorePVM M (m.mixedChannel VA VB DA DB) ≤ 1 - e

/-- A uniform worst-case joint-TV gap for all pure protocols of footprint at most `K`. -/
def PurePVMTVGap {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB),
    P.HasFootprint K → e ≤ pvmTVError M P.operationalChannel

/-- The same worst-case joint-TV gap for the finite mixed channel. -/
def MixedPVMTVGap {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (e : ℝ) :
    Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
    ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
      e ≤ pvmTVError M (m.mixedChannel VA VB DA DB)

/-- Score affinity: the pure gap bounds the best component of a finite mixture. -/
theorem PurePVMScoreGap.mixed {d K : ℕ} {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h : PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e) :
    MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : P.HasFootprint K :=
    (hasFootprint_iff K (m.component k)).mpr
      ((Nat.mul_le_mul_right (Fintype.card μB)
        (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hK)
  exact hk.trans (h ρA ρB κA κB μA μB εA εB P hPK)

/-- The joint-TV inequality `Δ ≥ 1 − q` transfers a pure score gap to TV. -/
theorem PurePVMScoreGap.tv {d K : ℕ} [NeZero d] {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (h : PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e) :
    PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  have h1 := h ρA ρB κA κB μA μB εA εB P hP
  have h2 := P.one_sub_scorePVM_le_pvmTVError hM
  linarith

/-- The inequality `Δ ≥ 1 − q` on the mixed channel transfers the mixed gap. -/
theorem MixedPVMScoreGap.tv {d K : ℕ} [NeZero d] {e : ℝ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (h : MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e) :
    MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n m VA VB DA DB hVA hVB hDA hDB R hR hK
  have h1 := h ρA ρB κA κB μA μB εA εB n m VA VB DA DB hVA hVB hDA hDB R hR hK
  have h2 := m.one_sub_scorePVM_le_pvmTVError hVA hVB hDA hDB hM
  linarith

end Gaps

section Assembly

theorem boundedPVMShapeScores_lt_one {d : ℕ} [NeZero d]
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d)
    (K : ℕ) {v : ℝ} (hv : v ∈ boundedPVMShapeScores M K) : v < 1 := by
  rcases hv with hv | hv
  · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hv
    obtain ⟨x, hx, rfl⟩ := hs
    exact (PVMPhysicalBlocks.toProtocol x hx).scorePVM_lt_one_of_pvmMeanPurity_not_mem hM hN
  · have : v = 0 := hv
    simp [this]

theorem purePVMScoreGap_of_upperBound {d K : ℕ} (hd : 2 ≤ d)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {B : ℝ}
    (hB : B ∈ upperBounds (boundedPVMShapeScores M K)) : PurePVMScoreGap M K (1 - B) := by
  intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hP
  have hle := hB (P.scorePVM_mem_boundedPVMShapeScores hd M K hP)
  linarith

/-- Compactness turns strict exclusion at one fixed target into a positive
score and joint-TV gap for pure and finite mixed resources, at each budget `K`. -/
theorem exists_pvm_gap_of_pvmMeanPurity_not_mem {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (hN : pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∉ exactPVMPurityValues d) (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
      MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  obtain ⟨B, hB⟩ := (isCompact_boundedPVMShapeScores M K).exists_isGreatest
    (boundedPVMShapeScores_nonempty M K)
  have hlt : B < 1 := boundedPVMShapeScores_lt_one hM hN K hB.1
  exact ⟨1 - B, sub_pos.mpr hlt, purePVMScoreGap_of_upperBound hd hB.2,
    (purePVMScoreGap_of_upperBound hd hB.2).mixed,
    (purePVMScoreGap_of_upperBound hd hB.2).tv hM,
    (purePVMScoreGap_of_upperBound hd hB.2).mixed.tv hM⟩

/-- **QLPVM-G (unconditional).** For every `d ≥ 2` there is one ordered rank-one PVM,
chosen before every finite footprint, that is not exactly implementable by any
finite architecture. For every `K` it has a positive gap `e`, uniform over all
finite original registers and finite mixed decompositions. The gap holds for the
average basis score (`q ≤ 1 − e`) and for worst-case joint TV (`Δ ≥ e`). -/
theorem exists_pvm_qualitative_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
      NoFinitePurePVMImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M ∧
      NoFiniteMixedPVMImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧
        PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨s, hs0, hs1, hN⟩ := exists_pvmRotation_purity_not_mem hd
  have hs1' : s ≤ 1 := by linarith
  have hM := isIsometry_pvmRotationBasis hd hs0 hs1'
  refine ⟨pvmRotationBasis hd s, pvmRotationBasis_mem_unitaryGroup hd hs0 hs1', ?_, ?_,
    fun K => exists_pvm_gap_of_pvmMeanPurity_not_mem hd hM hN K⟩
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    exact P.not_performsPVM_of_pvmMeanPurity_not_mem hM hN
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n m VA VB DA DB hVA hVB hDA hDB
    exact m.not_performsPVM_of_pvmMeanPurity_not_mem hVA hVB hDA hDB hM hN

end Assembly

end NLQCLean
