import NLQCLean.Models.ClassicalCommunication.ResourceSupport
import NLQCLean.Models.ClassicalCommunication.ProtocolCompression
import NLQCLean.Models.ClassicalCommunication.TargetScores
import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Rigidity.FlaggedSupports
import NLQCLean.Models.PhysicalReachability
import NLQCLean.Models.PVMPhysicalReachability
import NLQCLean.Models.ProtocolMetrics
import NLQCLean.Models.ProjectiveTV

/-!
# Finite classical compression into an actual charged protocol

Rank-sized resource supports are established before selecting outcomes.
Alice and then Bob select at most `(d r)²` outcomes each without decreasing the actual
prescribed real-linear channel score, giving the charged footprint `d⁴ K⁵`.
The coherent conversion alone preserves the compressed channel. No equality
with the original channel, diamond error or joint-TV error is inferred from
score compression.
-/

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

open Matrix

variable {d K : ℕ} {ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype ιA'] [Fintype ιB']
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ηA] [DecidableEq ηB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq εA] [DecidableEq εB]

/-- Actual finite outcome compression and coherent conversion with the sharp
fifth-power charged footprint. All originally unused resource dimensions are
removed by a proved channel-preserving factorization before compression. -/
theorem exists_bounded_outcomes_charged_linearScore
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (hd : 0 < d) (hK : P.HasQuantumFootprint K) :
    ∃ nA : ℕ, nA ≤ (d * schmidtRank P.resource) ^ 2 ∧
      ∃ nB : ℕ, nB ≤ (d * schmidtRank P.resource) ^ 2 ∧
        ∃ Q : FiniteClassicalProtocol (Fin d) (Fin d)
          (Fin (schmidtRank P.resource)) (Fin (schmidtRank P.resource))
          κA κB μA μB (Fin nA) (Fin nB) ηA ηB ιA' ιB' εA εB,
          schmidtRank Q.resource ≤ schmidtRank P.resource ∧
          S P.operationalChannel ≤ S Q.operationalChannel ∧
          Q.coherentProtocol.HasFootprint (d ^ 4 * K ^ 5) ∧
          S P.operationalChannel ≤ S Q.coherentProtocol.operationalChannel := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hρ := P.resource_unit.card_pos
  simp only [Fintype.card_prod] at hρ
  have hρA : 0 < Fintype.card ρA := Nat.pos_of_mul_pos_right hρ
  have hρB : 0 < Fintype.card ρB := Nat.pos_of_mul_pos_left hρ
  have hencA : d * Fintype.card ρA ≤
      (Fintype.card κA * Fintype.card μA) * (Fintype.card σA * Fintype.card ηA) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using P.instrumentA.dilation_isometry.card_le
  have hencB : d * Fintype.card ρB ≤
      (Fintype.card κB * Fintype.card μB) * (Fintype.card σB * Fintype.card ηB) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using P.instrumentB.dilation_isometry.card_le
  have hmA : 1 ≤ Fintype.card μA :=
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right ((Nat.mul_pos hd hρA).trans_le hencA))
  have hmB : 1 ≤ Fintype.card μB :=
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right ((Nat.mul_pos hd hρB).trans_le hencB))
  obtain ⟨R, hchannel, hrankR, hfootR⟩ := P.exists_resource_support_protocol
  obtain ⟨nA, hnA, nB, hnB, Q, hresource, _, hscore⟩ :=
    R.exists_finiteOutcome_compression_nondecreasing_linearScore S
  have ha : nA ≤ (d * schmidtRank P.resource) ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hnA
  have hb : nB ≤ (d * schmidtRank P.resource) ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hnB
  have hrank : schmidtRank Q.resource ≤ schmidtRank P.resource := by
    rw [hresource]
    exact hrankR
  have hscoreP : S P.operationalChannel ≤ S Q.operationalChannel := by
    rw [hchannel]
    exact hscore
  have hcharged : Q.coherentProtocol.HasFootprint (d ^ 4 * K ^ 5) := by
    rw [Q.coherentProtocol_hasFootprint_iff]
    simp only [Fintype.card_fin]
    apply (Nat.mul_le_mul_right (Fintype.card μB * nB)
      (Nat.mul_le_mul_right (Fintype.card μA * nA) hrank)).trans
    exact charged_message_footprint_le d _ _ _ _ _ K hmA hmB
      ((hasFootprint_iff K P.resource).mp hK)
      (ha.trans_eq (mul_pow _ _ _)) (hb.trans_eq (mul_pow _ _ _))
  refine ⟨nA, ha, nB, hb, Q, hrank, hscoreP, hcharged, ?_⟩
  rw [Q.coherentProtocol_operationalChannel]
  exact hscoreP

/-- The finite-alphabet unitary score class enters the charged reachable set
through score-preserving compression. -/
theorem mem_pureReachable_of_quantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  obtain ⟨nA, _, nB, _, Q, _, _, hfoot, hsame⟩ :=
    P.exists_bounded_outcomes_charged_linearScore (unitaryScoreRealLinear
      (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) hd hK
  apply Q.coherentProtocol.mem_pureReachable hfoot
  change scoreU (U : Matrix _ _ ℂ) P.operationalChannel ≤
    scoreU (U : Matrix _ _ ℂ) Q.coherentProtocol.operationalChannel at hsame
  exact hscore.trans hsame

/-- The PVM bridge preserves the existing two-sided correct-label score. -/
theorem mem_purePVMReachable_of_quantumFootprint
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  obtain ⟨nA, _, nB, _, Q, _, _, hfoot, hsame⟩ :=
    P.exists_bounded_outcomes_charged_linearScore (pvmScoreRealLinear
      (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) hd hK
  apply Q.coherentProtocol.mem_purePVMReachable hfoot
  change scorePVM (M : Matrix _ _ ℂ) P.operationalChannel ≤
    scorePVM (M : Matrix _ _ ℂ) Q.coherentProtocol.operationalChannel at hsame
  exact hscore.trans hsame

/-- Diamond accuracy is used only to obtain the original target score.
The compressed protocol is not asserted to preserve the diamond error. -/
theorem mem_pureReachable_of_quantumFootprint_diamondError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d) (Fin d) εA εB)
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (herror : diamondError P.operationalChannel (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs := P.coherentProtocol.scoreU_ge_of_diamondError_le
    (e := ε) (Matrix.mem_unitaryGroup_iff'.mp U.property)
    (by simpa only [P.coherentProtocol_operationalChannel] using herror)
  rw [P.coherentProtocol_operationalChannel] at hs
  exact P.mem_pureReachable_of_quantumFootprint U hd hK hs

/-- Joint-TV accuracy similarly transfers through score, without asserting
joint-TV preservation by selecting classical outcomes. -/
theorem mem_purePVMReachable_of_quantumFootprint_pvmTVError
    (P : FiniteClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB ηA ηB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel ≤ ε) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs := P.coherentProtocol.one_sub_scorePVM_le_pvmTVError
    (Matrix.mem_unitaryGroup_iff'.mp M.property)
  rw [P.coherentProtocol_operationalChannel] at hs
  apply P.mem_purePVMReachable_of_quantumFootprint M hd hK
  linarith

end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol
