import NLQCLean.Models.ClassicalCommunication.BorelMixed

/-!
# Charged compression of common-map mixed Borel scores

Select an actual rank-capped pure component with score at least the mixed
channel, then apply the proved pure Borel compression. Diamond and joint-TV
hypotheses concern the original averaged channel and enter through its score.
-/

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open Matrix

attribute [local implicit_reducible] Matrix

local instance mixedNaturalProductDecidableEq {α β : Type*} [DecidableEq α] [DecidableEq β] :
    DecidableEq (α × β) := instDecidableEqProd

local instance mixedUnitDecidableEq : DecidableEq Unit := fun a b => by
  cases a
  cases b
  exact isTrue rfl

variable {d K n : ℕ} [NeZero d] {ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]

/-- Mixed Borel score selection gives an actual charged protocol with
rank-sized finite alphabets and the same fifth-power quantum budget. -/
theorem exists_component_bounded_outcomes_charged_linearScore
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB ιA' ιB')
    (m : MixedResource ρA ρB n)
    (S : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K) :
    ∃ k : Fin n,
      ∃ nA : ℕ, nA ≤ (d * schmidtRank (m.component k)) ^ 2 ∧
        ∃ nB : ℕ, nB ≤ (d * schmidtRank (m.component k)) ^ 2 ∧
          ∃ Q : FiniteClassicalProtocol (Fin d) (Fin d)
            (Fin (schmidtRank (m.component k))) (Fin (schmidtRank (m.component k)))
            κA κB μA μB (Fin nA) (Fin nB)
            ((κA × μA) × (Fin d × ρA)) ((κB × μB) × (Fin d × ρB))
            ιA' ιB' (Unit × (ιA' × (κA × μB))) (Unit × (ιB' × (κB × μA))),
            schmidtRank Q.resource ≤ schmidtRank (m.component k) ∧
            Q.coherentProtocol.HasFootprint (d ^ 4 * K ^ 5) ∧
            S (P.mixedOperationalChannel m) ≤ S Q.coherentProtocol.operationalChannel := by
  obtain ⟨k, hscore, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint S m hK
  have hcompressed := (P.componentProtocol m k).exists_bounded_outcomes_charged_linearScore S hd hfoot
  simp only [componentProtocol_resource] at hcompressed
  obtain ⟨nA, hnA, nB, hnB, Q, hrank, _, hcharged, hsame⟩ := hcompressed
  refine ⟨k, nA, hnA, nB, hnB, Q, hrank, hcharged, ?_⟩
  exact hscore.trans hsame

/-- The honest common-map mixed unitary score transfers to charged pure
reachability through an actual component and pure Borel compression. -/
theorem mem_pureReachable_of_mixedQuantumFootprint
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (m : MixedResource ρA ρB n) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  obtain ⟨k, hcomponent, hfoot⟩ :=
    P.exists_component_linearScore_ge_hasQuantumFootprint
      (unitaryScoreRealLinear (U : Matrix _ _ ℂ)) m hK
  apply (P.componentProtocol m k).mem_pureReachable_of_quantumFootprint U hd hfoot
  exact hscore.trans hcomponent

/-- Mixed PVM score transfer preserves the actual joint correct-label task. -/
theorem mem_purePVMReachable_of_mixedQuantumFootprint
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (m : MixedResource ρA ρB n) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  obtain ⟨k, hcomponent, hfoot⟩ :=
    P.exists_component_linearScore_ge_hasQuantumFootprint
      (pvmScoreRealLinear (M : Matrix _ _ ℂ)) m hK
  apply (P.componentProtocol m k).mem_purePVMReachable_of_quantumFootprint M hd hfoot
  exact hscore.trans hcomponent

/-- The original mixed Borel channel has normalized Choi trace one. -/
theorem trace_choiMatrix_mixedOperationalChannel_eq_one
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB ιA' ιB')
    (m : MixedResource ρA ρB n) (hd : 0 < d) :
    (choiMatrix (P.mixedOperationalChannel m)).trace = 1 := by
  rw [mixedOperationalChannel, trace_choiMatrix_sum_smul]
  have htrace (k : Fin n) := (P.componentProtocol m k).trace_choiMatrix_operationalChannel_eq_one hd
  simp only [htrace, mul_one]
  exact_mod_cast m.weight_sum

/-- Original averaged-channel diamond error controls its unitary score. -/
theorem one_sub_scoreU_mixedOperationalChannel_le_diamondError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (m : MixedResource ρA ρB n) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (hd : 0 < d) :
    1 - scoreU (U : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤
      diamondError (P.mixedOperationalChannel m) (adConj (U : Matrix _ _ ℂ)) :=
  NLQCLean.one_sub_scoreU_le_diamondError (Matrix.mem_unitaryGroup_iff'.mp U.property)
    _ (P.trace_choiMatrix_mixedOperationalChannel_eq_one m hd)

/-- Original mixed diamond accuracy is converted before component selection. -/
theorem mem_pureReachable_of_mixedQuantumFootprint_diamondError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d) (Fin d))
    (m : MixedResource ρA ρB n) (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj (U : Matrix _ _ ℂ)) ≤ ε) :
    U ∈ pureReachable d (d ^ 4 * K ^ 5) ε := by
  have hs := P.one_sub_scoreU_mixedOperationalChannel_le_diamondError m U hd
  apply P.mem_pureReachable_of_mixedQuantumFootprint m U hd hK
  linarith

/-- The original mixed Borel channel gives physical joint PVM distributions. -/
theorem isPVMOutcomeChannel_mixedOperationalChannel
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (m : MixedResource ρA ρB n) (hd : 0 < d) :
    IsPVMOutcomeChannel (P.mixedOperationalChannel m) :=
  IsPVMOutcomeChannel.sum_smul m.weight
    (fun k => (P.componentProtocol m k).operationalChannel.toLinearMap)
    (fun k => (P.componentProtocol m k).isPVMOutcomeChannel hd)
    m.weight_nonneg m.weight_sum

/-- Original averaged-channel joint TV controls its two-sided PVM score. -/
theorem one_sub_scorePVM_mixedOperationalChannel_le_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (m : MixedResource ρA ρB n) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (hd : 0 < d) :
    1 - scorePVM (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤
      pvmTVError (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m) :=
  NLQCLean.one_sub_scorePVM_le_pvmTVError (Matrix.mem_unitaryGroup_iff'.mp M.property)
    (P.isPVMOutcomeChannel_mixedOperationalChannel m hd)

/-- Original mixed joint-TV accuracy is converted before component selection. -/
theorem mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d)
      ρA ρB κA κB μA μB σA σB (Fin d × Fin d) (Fin d × Fin d))
    (m : MixedResource ρA ρB n) (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ}
    (hd : 0 < d) (hK : P.HasMixedQuantumFootprint m K)
    (herror : pvmTVError (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤ ε) :
    M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  have hs := P.one_sub_scorePVM_mixedOperationalChannel_le_pvmTVError m M hd
  apply P.mem_purePVMReachable_of_mixedQuantumFootprint m M hd hK
  linarith

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol
