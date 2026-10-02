import NLQCLean.Models.ClassicalCommunication.BorelFiniteCompression
import NLQCLean.Models.ClassicalCommunication.BorelChannelNormalization
import NLQCLean.Models.ClassicalCommunication.FiniteCompression

/-!
# Rank-sized score compression for pure standard-Borel protocols

First select an actual finite protocol with the original resource and score,
then remove unused resource support and recompress its finite outcomes.
Both charged messages include the resulting finite labels. The final budget
depends only on the logical dimension and original quantum footprint.
-/

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open Matrix
open scoped ComplexOrder

attribute [local implicit_reducible] Matrix

local instance naturalProductDecidableEq {α β : Type*} [DecidableEq α] [DecidableEq β] :
    DecidableEq (α × β) := instDecidableEqProd

local instance unitDecidableEq : DecidableEq Unit := fun a b => by
  cases a
  cases b
  exact isTrue rfl

variable {d K : ℕ} {ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [NeZero d]
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]

/-- Pure Borel score compression gives actual rank-sized finite alphabets
and a charged coherent protocol with footprint at most `d ^ 4 * K ^ 5`.
The resource rank in both alphabet caps is that of the original protocol. -/
theorem exists_bounded_outcomes_charged_linearScore
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB ιA' ιB')
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (hd : 0 < d) (hK : P.HasQuantumFootprint K) :
    ∃ nA : ℕ, nA ≤ (d * schmidtRank P.resource) ^ 2 ∧
      ∃ nB : ℕ, nB ≤ (d * schmidtRank P.resource) ^ 2 ∧
        ∃ Q : FiniteClassicalProtocol (Fin d) (Fin d)
          (Fin (schmidtRank P.resource)) (Fin (schmidtRank P.resource))
          κA κB μA μB (Fin nA) (Fin nB)
          ((κA × μA) × (Fin d × ρA)) ((κB × μB) × (Fin d × ρB))
          ιA' ιB' (Unit × (ιA' × (κA × μB))) (Unit × (ιB' × (κB × μA))),
          schmidtRank Q.resource ≤ schmidtRank P.resource ∧
          S P.operationalChannel.toLinearMap ≤ S Q.operationalChannel ∧
          Q.coherentProtocol.HasFootprint (d ^ 4 * K ^ 5) ∧
          S P.operationalChannel.toLinearMap ≤ S Q.coherentProtocol.operationalChannel := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨_, _, _, _, F, hresource, hfoot, hscore⟩ :=
    P.exists_finite_protocol_preserving_linearScore S
  have hcompressed := F.exists_bounded_outcomes_charged_linearScore S hd ((hfoot K).mpr hK)
  rw [hresource] at hcompressed
  obtain ⟨nA, hnA, nB, hnB, Q, hrank, hscoreQ, hcharged, hcoherent⟩ := hcompressed
  exact ⟨nA, hnA, nB, hnB, Q, hrank, hscore.symm.trans_le hscoreQ,
    hcharged, hscore.symm.trans_le hcoherent⟩

/-- The actual Borel unitary score enters charged pure reachability after
both finite selection and rank-sized recompression. -/
theorem mem_pureReachable_of_quantumFootprint
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel.toLinearMap) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  obtain ⟨_, _, _, _, Q, _, _, hfoot, hsame⟩ :=
    P.exists_bounded_outcomes_charged_linearScore
      (unitaryScoreRealLinear (U : Matrix _ _ ℂ)) hd hK
  apply Q.coherentProtocol.mem_pureReachable hfoot
  change scoreU (U : Matrix _ _ ℂ) P.operationalChannel.toLinearMap ≤
    scoreU (U : Matrix _ _ ℂ) Q.coherentProtocol.operationalChannel at hsame
  exact hscore.trans hsame

/-- The PVM specialization retains both parties' correct output labels. -/
theorem mem_purePVMReachable_of_quantumFootprint
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel.toLinearMap) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  obtain ⟨_, _, _, _, Q, _, _, hfoot, hsame⟩ :=
    P.exists_bounded_outcomes_charged_linearScore
      (pvmScoreRealLinear (M : Matrix _ _ ℂ)) hd hK
  apply Q.coherentProtocol.mem_purePVMReachable hfoot
  change scorePVM (M : Matrix _ _ ℂ) P.operationalChannel.toLinearMap ≤
    scorePVM (M : Matrix _ _ ℂ) Q.coherentProtocol.operationalChannel at hsame
  exact hscore.trans hsame

/-- The original operational Borel channel has normalized Choi trace one,
as follows from its proved CP/TP properties and a finite Stinespring dilation. -/
theorem trace_choiMatrix_operationalChannel_eq_one
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB ιA' ιB') (hd : 0 < d) :
    (choiMatrix P.operationalChannel.toLinearMap).trace = 1 := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have h := trace_choiMatrix_channelOf_eq_one
    (operationStinespring_isometry P.operationalChannel
      P.operationalChannel_completelyPositive P.operationalChannel_tracePreserving)
  rwa [channelOf_operationStinespring] at h

/-- Normalized diamond error of the original Borel channel dominates its
unitary Choi infidelity. -/
theorem one_sub_scoreU_le_diamondError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (hd : 0 < d) :
    1 - scoreU (U : Matrix _ _ ℂ) P.operationalChannel.toLinearMap ≤
      diamondError P.operationalChannel.toLinearMap (adConj (U : Matrix _ _ ℂ)) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact NLQCLean.one_sub_scoreU_le_diamondError
    (Matrix.mem_unitaryGroup_iff'.mp U.property) P.operationalChannel.toLinearMap
    (P.trace_choiMatrix_operationalChannel_eq_one hd)

/-- Original diamond accuracy transfers through the original unitary score. -/
theorem mem_pureReachable_of_quantumFootprint_diamondError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (herror : diamondError P.operationalChannel.toLinearMap
      (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs := P.one_sub_scoreU_le_diamondError U hd
  apply P.mem_pureReachable_of_quantumFootprint U hd hK
  linarith

/-- The original Borel CP/TP channel gives a physical joint output
probability distribution for every density-matrix input. -/
theorem isPVMOutcomeChannel
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d)) (hd : 0 < d) :
    IsPVMOutcomeChannel P.operationalChannel.toLinearMap := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  constructor
  · intro ρ hρ ab
    have hp : (P.operationalChannel ρ).PosSemidef := by
      obtain ⟨A, hA⟩ := exists_kraus_of_completelyPositive
        P.operationalChannel.toLinearMap P.operationalChannel_completelyPositive
      change (P.operationalChannel.toLinearMap ρ).PosSemidef
      rw [hA, krausMap_apply]
      exact Matrix.posSemidef_sum _ (fun e _ => hρ.1.mul_mul_conjTranspose_same (A e))
    exact (Complex.nonneg_iff.mp (hp.diag_nonneg (i := ab))).1
  · intro ρ hρ
    change ∑ ab, (P.operationalChannel ρ ab ab).re = 1
    rw [← Complex.re_sum]
    change (P.operationalChannel ρ).trace.re = 1
    rw [P.operationalChannel_tracePreserving, hρ.2]
    rfl

/-- Worst-case joint TV of the original Borel channel dominates its
average two-sided correct-label infidelity. -/
theorem one_sub_scorePVM_le_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (hd : 0 < d) :
    1 - scorePVM (M : Matrix _ _ ℂ) P.operationalChannel.toLinearMap ≤
      pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel.toLinearMap := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  exact NLQCLean.one_sub_scorePVM_le_pvmTVError
    (Matrix.mem_unitaryGroup_iff'.mp M.property) (P.isPVMOutcomeChannel hd)

/-- Original joint-TV accuracy transfers through the original PVM score. -/
theorem mem_purePVMReachable_of_quantumFootprint_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasQuantumFootprint K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel.toLinearMap ≤ ε) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  have hs := P.one_sub_scorePVM_le_pvmTVError M hd
  apply P.mem_purePVMReachable_of_quantumFootprint M hd hK
  linarith

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol
