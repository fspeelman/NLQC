import NLQCLean.Approx.FiniteClassicalSpectralFloors
import NLQCLean.Models.ClassicalCommunication.BorelSharedRandomness

/-!
# Quantum-footprint spectral floors for standard-Borel protocols

Same-resource finite score realization transfers the top-K Choi and
maximum-column PVM bounds while retaining the original quantum footprint.
Common-map mixed resources and actual averaged randomness are selected by
score with their branchwise caps. Classical labels remain uncharged.
-/

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius MeasureTheory

attribute [local implicit_reducible] Matrix

variable {ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable [Nonempty ιA] [Nonempty ιB]

/-- The actual Borel unitary score satisfies the original quantum top-K mass bound. -/
theorem scoreU_le_schmidtMass
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} (hK : P.HasQuantumFootprint K) :
    scoreU U P.operationalChannel.toLinearMap ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  classical
  obtain ⟨_, _, _, _, F, _, hfoot, hsame⟩ :=
    P.exists_finite_protocol_preserving_linearScore (unitaryScoreRealLinear U)
  change scoreU U F.operationalChannel = scoreU U P.operationalChannel.toLinearMap at hsame
  exact hsame ▸ F.scoreU_le_schmidtMass U ((hfoot K).mpr hK)

/-- A common target-column top-K mass bound controls both correct PVM labels. -/
theorem scorePVM_le_of_column_schmidtMass_le
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {t : ℝ}
    (hK : P.HasQuantumFootprint K) (ht : 0 ≤ t)
    (hmass : ∀ i, schmidtMass K (pvmConjugateColumnMatrix M i) ≤ t) :
    scorePVM M P.operationalChannel.toLinearMap ≤ t := by
  classical
  obtain ⟨_, _, _, _, F, _, hfoot, hsame⟩ :=
    P.exists_finite_protocol_preserving_linearScore (pvmScoreRealLinear M)
  change scorePVM M F.operationalChannel = scorePVM M P.operationalChannel.toLinearMap at hsame
  exact hsame ▸ F.scorePVM_le_of_column_schmidtMass_le M ((hfoot K).mpr hK) ht hmass

/-- The literal maximum-column PVM bound uses the quantum budget only. -/
theorem scorePVM_le_max_column_schmidtMass
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} (hK : P.HasQuantumFootprint K) :
    scorePVM M P.operationalChannel.toLinearMap ≤ pvmMaxColumnSchmidtMass K M :=
  P.scorePVM_le_of_column_schmidtMass_le M hK (pvmMaxColumnSchmidtMass_nonneg K M)
    (column_schmidtMass_le_pvmMaxColumnSchmidtMass K M)

/-- Actual common-map component selection retains the quantum-only Choi mass. -/
theorem mixed_scoreU_le_schmidtMass
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} (hK : P.HasMixedQuantumFootprint m K) :
    scoreU U (P.mixedOperationalChannel m) ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (unitaryScoreRealLinear U) m hK
  exact hs.trans ((P.componentProtocol m k).scoreU_le_schmidtMass U hfoot)

/-- Actual common-map mixing retains the maximum-column quantum bound. -/
theorem mixed_scorePVM_le_max_column_schmidtMass
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} (hK : P.HasMixedQuantumFootprint m K) :
    scorePVM M (P.mixedOperationalChannel m) ≤ pvmMaxColumnSchmidtMass K M := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact hs.trans ((P.componentProtocol m k).scorePVM_le_max_column_schmidtMass M hfoot)

/-- Original diamond accuracy gives the original Borel score before selection. -/
theorem scoreU_ge_of_diamondError_le
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {ε : ℝ}
    (herror : diamondError P.operationalChannel.toLinearMap (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U P.operationalChannel.toLinearMap := by
  have htrace := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    P.operationalChannel P.operationalChannel_completelyPositive P.operationalChannel_tracePreserving
  have hs := NLQCLean.one_sub_scoreU_le_diamondError hU P.operationalChannel.toLinearMap htrace
  linarith

/-- Original joint TV gives the original two-sided PVM score before selection. -/
theorem scorePVM_ge_of_pvmTVError_le
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {ε : ℝ}
    (herror : pvmTVError M P.operationalChannel.toLinearMap ≤ ε) :
    1 - ε ≤ scorePVM M P.operationalChannel.toLinearMap := by
  have hout := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    P.operationalChannel P.operationalChannel_completelyPositive P.operationalChannel_tracePreserving
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError hM hout
  linarith

/-- Original common-map mixed diamond accuracy is converted before component selection. -/
theorem mixed_scoreU_ge_of_diamondError_le
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {ε : ℝ}
    (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U (P.mixedOperationalChannel m) := by
  have htrace := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (P.mixedOperationalChannel m).toContinuousLinearMap
    (P.mixedOperationalChannel_completelyPositive m) (P.mixedOperationalChannel_tracePreserving m)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError hU (P.mixedOperationalChannel m) htrace
  linarith

/-- Original common-map mixed joint TV is converted before component selection. -/
theorem mixed_scorePVM_ge_of_pvmTVError_le
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {ε : ℝ}
    (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) :
    1 - ε ≤ scorePVM M (P.mixedOperationalChannel m) := by
  have hout := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (P.mixedOperationalChannel m).toContinuousLinearMap
    (P.mixedOperationalChannel_completelyPositive m) (P.mixedOperationalChannel_tracePreserving m)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError hM hout
  change 1 - scorePVM M (P.mixedOperationalChannel m) ≤
    pvmTVError M (P.mixedOperationalChannel m) at hs
  linarith


/-- Original score accuracy forces the target's quantum top-K Choi mass. -/
theorem unitary_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU U (P.operationalChannel.toLinearMap)) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (P.scoreU_le_schmidtMass U hK)

/-- Exact implementation covers the target operator-Schmidt rank. -/
theorem unitary_exact_schmidt_rank_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K) (hscore : 1 ≤ scoreU U (P.operationalChannel.toLinearMap)) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (P.scoreU_le_schmidtMass U hK))

/-- A target-only smallest-weight threshold forces full quantum Choi size. -/
theorem unitary_full_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (hscore : 1 - ε ≤ scoreU U (P.operationalChannel.toLinearMap)) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    ht hε (hscore.trans (P.scoreU_le_schmidtMass U hK))

/-- Joint correct-label accuracy forces the maximum-column quantum mass. -/
theorem pvm_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scorePVM M (P.operationalChannel.toLinearMap)) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  hscore.trans (P.scorePVM_le_max_column_schmidtMass M hK)

/-- A uniform target-column smallest-weight threshold forces full quantum column size. -/
theorem pvm_full_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasQuantumFootprint K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M (P.operationalChannel.toLinearMap)) :
    Fintype.card ιA ≤ K := by
  classical
  obtain ⟨_, _, _, _, F, _, hfoot, hsame⟩ :=
    P.exists_finite_protocol_preserving_linearScore (pvmScoreRealLinear M)
  exact F.pvm_full_spectral_floor M hM ((hfoot K).mpr hK) ht hε
    (by change scorePVM M F.operationalChannel = scorePVM M P.operationalChannel.toLinearMap at hsame
        exact hsame.symm ▸ hscore)

/-- The flat SWAP spectrum forces d² times the original score accuracy in quantum footprint. -/
theorem swap_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol ιA ιA ρA ρB κA κB μA μB σA σB ιA ιA) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) (P.operationalChannel.toLinearMap)) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K := by
  classical
  obtain ⟨_, _, _, _, F, _, hfoot, hsame⟩ :=
    P.exists_finite_protocol_preserving_linearScore (unitaryScoreRealLinear (swapUnitary ιA))
  exact F.swap_quantumFootprint_floor ((hfoot K).mpr hK)
    (by change scoreU (swapUnitary ιA) F.operationalChannel =
          scoreU (swapUnitary ιA) P.operationalChannel.toLinearMap at hsame
        exact hsame.symm ▸ hscore)

/-- Maximally entangled PVM columns force d times the original joint-score accuracy in quantum footprint. -/
theorem maximallyEntangledPVM_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA => ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scorePVM M (P.operationalChannel.toLinearMap)) :
    (Fintype.card ιA : ℝ) * (1 - ε) ≤ K := by
  classical
  obtain ⟨_, _, _, _, F, _, hfoot, hsame⟩ :=
    P.exists_finite_protocol_preserving_linearScore (pvmScoreRealLinear M)
  exact F.maximallyEntangledPVM_quantumFootprint_floor M hflat ((hfoot K).mpr hK)
    (by change scorePVM M F.operationalChannel = scorePVM M P.operationalChannel.toLinearMap at hsame
        exact hsame.symm ▸ hscore)

/-- The quantum spectral floor from the actual original diamond error. -/
theorem unitary_spectral_floor_of_diamondError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (herror : diamondError (P.operationalChannel.toLinearMap) (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  P.unitary_spectral_floor U hK
    (P.scoreU_ge_of_diamondError_le U hU herror)

/-- The quantum spectral floor from the actual original joint-TV error. -/
theorem pvm_spectral_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {K : ℕ} {ε : ℝ}
    (hK : P.HasQuantumFootprint K) (herror : pvmTVError M (P.operationalChannel.toLinearMap) ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  P.pvm_spectral_floor M hK
    (P.scorePVM_ge_of_pvmTVError_le M hM herror)

/-- Original mixed score accuracy forces the target's quantum top-K Choi mass. -/
theorem mixed_unitary_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scoreU U (P.mixedOperationalChannel m)) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (P.mixed_scoreU_le_schmidtMass m U hK)

/-- Exact mixed implementation covers the target operator-Schmidt rank. -/
theorem mixed_unitary_exact_schmidt_rank_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hU : IsIsometry U) (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 ≤ scoreU U (P.mixedOperationalChannel m)) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (P.mixed_scoreU_le_schmidtMass m U hK))

/-- A target-only smallest-weight threshold forces full quantum Choi size. -/
theorem mixed_unitary_full_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hU : IsIsometry U) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i)
    (hε : ε < t) (hscore : 1 - ε ≤ scoreU U (P.mixedOperationalChannel m)) :
    Fintype.card (ιA' × ιA) ≤ K :=
  card_le_of_spectral_threshold _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    ht hε (hscore.trans (P.mixed_scoreU_le_schmidtMass m U hK))

/-- Joint correct-label accuracy forces the maximum-column quantum mass. -/
theorem mixed_pvm_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scorePVM M (P.mixedOperationalChannel m)) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  hscore.trans (P.mixed_scorePVM_le_max_column_schmidtMass m M hK)

/-- A uniform target-column smallest-weight threshold forces full quantum column size. -/
theorem mixed_pvm_full_spectral_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) {K : ℕ} {ε t : ℝ}
    (hM : IsIsometry M) (hK : P.HasMixedQuantumFootprint m K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M (P.mixedOperationalChannel m)) :
    Fintype.card ιA ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact (P.componentProtocol m k).pvm_full_spectral_floor M hM hfoot ht hε (hscore.trans hs)

/-- The flat SWAP spectrum forces d² times the original score accuracy in quantum footprint. -/
theorem mixed_swap_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol ιA ιA ρA ρB κA κB μA μB σA σB ιA ιA)
    {n : ℕ} (m : MixedResource ρA ρB n) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) (P.mixedOperationalChannel m)) :
    (Fintype.card ιA : ℝ) ^ 2 * (1 - ε) ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (unitaryScoreRealLinear (swapUnitary ιA)) m hK
  exact (P.componentProtocol m k).swap_quantumFootprint_floor hfoot (hscore.trans hs)

/-- Maximally entangled PVM columns force d times the original joint-score accuracy in quantum footprint. -/
theorem mixed_maximallyEntangledPVM_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (hflat : ∀ i, pvmConjugateColumnMatrix M i * (pvmConjugateColumnMatrix M i)ᴴ =
      Matrix.diagonal (fun _ : ιA => ((Fintype.card ιA : ℝ)⁻¹ : ℂ)))
    {K : ℕ} {ε : ℝ} (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scorePVM M (P.mixedOperationalChannel m)) :
    (Fintype.card ιA : ℝ) * (1 - ε) ≤ K := by
  obtain ⟨k, hs, hfoot⟩ := P.exists_component_linearScore_ge_hasQuantumFootprint
    (pvmScoreRealLinear M) m hK
  exact (P.componentProtocol m k).maximallyEntangledPVM_quantumFootprint_floor
    M hflat hfoot (hscore.trans hs)

/-- The quantum spectral floor from the actual original diamond error. -/
theorem mixed_unitary_spectral_floor_of_diamondError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  P.mixed_unitary_spectral_floor m U hK
    (P.mixed_scoreU_ge_of_diamondError_le m U hU herror)

/-- The quantum spectral floor from the actual original joint-TV error. -/
theorem mixed_pvm_spectral_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB
      (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {K : ℕ} {ε : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  P.mixed_pvm_spectral_floor m M hK
    (P.mixed_scorePVM_ge_of_pvmTVError_le m M hM herror)

/-- A target-only threshold applies to the error of the original channel. -/
theorem unitary_full_spectral_floor_of_diamondError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {K : ℕ} {ε t : ℝ}
    (hK : P.HasQuantumFootprint K) (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t)
    (herror : diamondError (P.operationalChannel.toLinearMap) (adConj U) ≤ ε) : Fintype.card (ιA' × ιA) ≤ K :=
  P.unitary_full_spectral_floor U hU hK ht hε
    (P.scoreU_ge_of_diamondError_le U hU herror)

/-- A target-only threshold applies to the error of the original channel. -/
theorem pvm_full_spectral_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB (ιA × ιB) (ιA × ιB))
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {K : ℕ} {ε t : ℝ}
    (hK : P.HasQuantumFootprint K) (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t)
    (herror : pvmTVError M (P.operationalChannel.toLinearMap) ≤ ε) : Fintype.card ιA ≤ K :=
  P.pvm_full_spectral_floor M hM hK ht hε
    (P.scorePVM_ge_of_pvmTVError_le M hM herror)

/-- A target-only threshold applies to the error of the original channel. -/
theorem mixed_unitary_full_spectral_floor_of_diamondError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')
    {n : ℕ} (m : MixedResource ρA ρB n)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) (hU : IsIsometry U) {K : ℕ} {ε t : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t)
    (herror : diamondError (P.mixedOperationalChannel m) (adConj U) ≤ ε) : Fintype.card (ιA' × ιA) ≤ K :=
  P.mixed_unitary_full_spectral_floor m U hU hK ht hε
    (P.mixed_scoreU_ge_of_diamondError_le m U hU herror)

/-- A target-only threshold applies to the error of the original channel. -/
theorem mixed_pvm_full_spectral_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB (ιA × ιB) (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M) {K : ℕ} {ε t : ℝ}
    (hK : P.HasMixedQuantumFootprint m K) (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t)
    (herror : pvmTVError M (P.mixedOperationalChannel m) ≤ ε) : Fintype.card ιA ≤ K :=
  P.mixed_pvm_full_spectral_floor m M hM hK ht hε
    (P.mixed_scorePVM_ge_of_pvmTVError_le m M hM herror)

variable {d : ℕ} [NeZero d]

/-- The complete generalized Bell basis has the literal linear quantum floor. -/
theorem generalizedBellPVM_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB (Fin d × Fin d) (Fin d × Fin d))
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (P.operationalChannel.toLinearMap)) :
    (d : ℝ) * (1 - ε) ≤ K := by
  simpa only [Fintype.card_fin] using P.maximallyEntangledPVM_quantumFootprint_floor
    (generalizedBellFinMatrix d) (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d)
    hK hscore

/-- The concrete Bell floor uses the original joint-TV error of both labels. -/
theorem generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB (Fin d × Fin d) (Fin d × Fin d))
    {K : ℕ} {ε : ℝ} (hK : P.HasQuantumFootprint K)
    (herror : pvmTVError (generalizedBellFinMatrix d) (P.operationalChannel.toLinearMap) ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  P.generalizedBellPVM_quantumFootprint_floor hK
    (P.scorePVM_ge_of_pvmTVError_le _ (isIsometry_generalizedBellFinMatrix d) herror)

/-- The complete generalized Bell basis has the literal linear quantum floor. -/
theorem mixed_generalizedBellPVM_quantumFootprint_floor
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB (Fin d × Fin d) (Fin d × Fin d))
    {n : ℕ} (m : MixedResource ρA ρB n)
    {K : ℕ} {ε : ℝ} (hK : P.HasMixedQuantumFootprint m K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (P.mixedOperationalChannel m)) :
    (d : ℝ) * (1 - ε) ≤ K := by
  simpa only [Fintype.card_fin] using P.mixed_maximallyEntangledPVM_quantumFootprint_floor
    m (generalizedBellFinMatrix d) (pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d)
    hK hscore

/-- The concrete Bell floor uses the original joint-TV error of both labels. -/
theorem mixed_generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : StandardBorelClassicalProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      σA σB (Fin d × Fin d) (Fin d × Fin d))
    {n : ℕ} (m : MixedResource ρA ρB n)
    {K : ℕ} {ε : ℝ} (hK : P.HasMixedQuantumFootprint m K)
    (herror : pvmTVError (generalizedBellFinMatrix d) (P.mixedOperationalChannel m) ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  P.mixed_generalizedBellPVM_quantumFootprint_floor m hK
    (P.mixed_scorePVM_ge_of_pvmTVError_le m _ (isIsometry_generalizedBellFinMatrix d) herror)

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open Matrix MeasureTheory
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance floorMatrixNormedAddCommGroup {ν : Type*} [Fintype ν] :
    NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance floorMatrixTopologicalSpace {ν : Type*} [Fintype ν] :
    TopologicalSpace (Matrix ν ν ℂ) :=
  (floorMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance floorMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance floorMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance floorOperationNormedAddCommGroup {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance floorOperationRealNormedSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {d K : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB σA σB : α → Type*}
variable [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
variable [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
variable [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
variable [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
variable [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
variable [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
variable [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
variable [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]

/-- The actual averaged score retains the original branchwise quantum mass bound. -/
theorem sharedRandom_scoreU_le_schmidtMass
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) : scoreU U (sharedRandomOperationalChannel μ P).toLinearMap ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (unitaryScoreRealLinear U) hK
  exact hs.trans ((P a).scoreU_le_schmidtMass U hfoot)

/-- Original average-channel accuracy forces the same quantum spectral mass. -/
theorem sharedRandom_unitary_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU U (sharedRandomOperationalChannel μ P).toLinearMap) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (sharedRandom_scoreU_le_schmidtMass μ P hP U hK)

/-- Accuracy is converted on the unchanged actual averaged channel before selection. -/
theorem sharedRandom_scoreU_ge_of_diamondError_le
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε : ℝ} (herror : diamondError (sharedRandomOperationalChannel μ P).toLinearMap (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U (sharedRandomOperationalChannel μ P).toLinearMap := by
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (sharedRandomOperationalChannel μ P)
    (sharedRandomOperationalChannel_completelyPositive μ P hP)
    (sharedRandomOperationalChannel_tracePreserving μ P hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError hU (sharedRandomOperationalChannel μ P).toLinearMap hphysical
  linarith

/-- The quantum spectral floor uses the error of the original actual probability average. -/
theorem sharedRandom_unitary_spectral_floor_of_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) (herror : diamondError (sharedRandomOperationalChannel μ P).toLinearMap (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  sharedRandom_unitary_spectral_floor μ P hP U hK
    (sharedRandom_scoreU_ge_of_diamondError_le μ P hP U hU herror)

/-- A target-only threshold applies to every original randomness branch architecture. -/
theorem sharedRandom_unitary_full_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t) (hscore : 1 - ε ≤ scoreU U (sharedRandomOperationalChannel μ P).toLinearMap) :
    d ^ 2 ≤ K := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (unitaryScoreRealLinear U) hK
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    (P a).unitary_full_spectral_floor U hU hfoot ht hε (hscore.trans hs)

/-- A target-only threshold also applies to original average-channel error accuracy. -/
theorem sharedRandom_unitary_full_spectral_floor_of_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t) (herror : diamondError (sharedRandomOperationalChannel μ P).toLinearMap (adConj U) ≤ ε) : d ^ 2 ≤ K :=
  sharedRandom_unitary_full_spectral_floor μ P hP U hU hK ht hε
    (sharedRandom_scoreU_ge_of_diamondError_le μ P hP U hU herror)

/-- Exact actual averaged implementation covers the target operator-Schmidt rank. -/
theorem sharedRandom_unitary_exact_schmidt_rank_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) (hscore : 1 ≤ scoreU U (sharedRandomOperationalChannel μ P).toLinearMap) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (sharedRandom_scoreU_le_schmidtMass μ P hP U hK))

/-- The concrete flat target retains its quantum floor under actual shared randomness. -/
theorem sharedRandom_swap_quantumFootprint_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary (Fin d)) (sharedRandomOperationalChannel μ P).toLinearMap) :
    (d : ℝ) ^ 2 * (1 - ε) ≤ K := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (unitaryScoreRealLinear (swapUnitary (Fin d))) hK
  simpa only [Fintype.card_fin] using (P a).swap_quantumFootprint_floor hfoot (hscore.trans hs)

/-- The actual averaged score retains the original branchwise quantum mass bound. -/
theorem sharedRandom_scorePVM_le_max_column_schmidtMass
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) : scorePVM M (sharedRandomOperationalChannel μ P).toLinearMap ≤ pvmMaxColumnSchmidtMass K M := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (pvmScoreRealLinear M) hK
  exact hs.trans ((P a).scorePVM_le_max_column_schmidtMass M hfoot)

/-- Original average-channel accuracy forces the same quantum spectral mass. -/
theorem sharedRandom_pvm_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) (hscore : 1 - ε ≤ scorePVM M (sharedRandomOperationalChannel μ P).toLinearMap) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  hscore.trans (sharedRandom_scorePVM_le_max_column_schmidtMass μ P hP M hK)

/-- Accuracy is converted on the unchanged actual averaged channel before selection. -/
theorem sharedRandom_scorePVM_ge_of_pvmTVError_le
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε : ℝ} (herror : pvmTVError M (sharedRandomOperationalChannel μ P).toLinearMap ≤ ε) :
    1 - ε ≤ scorePVM M (sharedRandomOperationalChannel μ P).toLinearMap := by
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (sharedRandomOperationalChannel μ P)
    (sharedRandomOperationalChannel_completelyPositive μ P hP)
    (sharedRandomOperationalChannel_tracePreserving μ P hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError hM hphysical
  linarith

/-- The quantum spectral floor uses the error of the original actual probability average. -/
theorem sharedRandom_pvm_spectral_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K) (herror : pvmTVError M (sharedRandomOperationalChannel μ P).toLinearMap ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  sharedRandom_pvm_spectral_floor μ P hP M hK
    (sharedRandom_scorePVM_ge_of_pvmTVError_le μ P hP M hM herror)

/-- A target-only threshold applies to every original randomness branch architecture. -/
theorem sharedRandom_pvm_full_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M (sharedRandomOperationalChannel μ P).toLinearMap) :
    d ≤ K := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (pvmScoreRealLinear M) hK
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    (P a).pvm_full_spectral_floor M hM hfoot ht hε (hscore.trans hs)

/-- A target-only threshold also applies to original average-channel error accuracy. -/
theorem sharedRandom_pvm_full_spectral_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t) (herror : pvmTVError M (sharedRandomOperationalChannel μ P).toLinearMap ≤ ε) : d ≤ K :=
  sharedRandom_pvm_full_spectral_floor μ P hP M hM hK ht hε
    (sharedRandom_scorePVM_ge_of_pvmTVError_le μ P hP M hM herror)

/-- The concrete flat target retains its quantum floor under actual shared randomness. -/
theorem sharedRandom_generalizedBellPVM_quantumFootprint_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (sharedRandomOperationalChannel μ P).toLinearMap) :
    (d : ℝ) * (1 - ε) ≤ K := by
  obtain ⟨a, hfoot, hs⟩ := exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint
    μ P hP (pvmScoreRealLinear (generalizedBellFinMatrix d)) hK
  simpa only [Fintype.card_fin] using (P a).generalizedBellPVM_quantumFootprint_floor hfoot (hscore.trans hs)

/-- The concrete Bell floor uses the TV error of the actual average channel. -/
theorem sharedRandom_generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint K)
    (herror : pvmTVError (generalizedBellFinMatrix d) (sharedRandomOperationalChannel μ P).toLinearMap ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  sharedRandom_generalizedBellPVM_quantumFootprint_floor μ P hP hK
    (sharedRandom_scorePVM_ge_of_pvmTVError_le μ P hP _
      (isIsometry_generalizedBellFinMatrix d) herror)

/-- The actual averaged score retains the original branchwise quantum mass bound. -/
theorem mixedSharedRandom_scoreU_le_schmidtMass
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) : scoreU U (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ schmidtMass K (normalizedLabChoiMatrix U) := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (unitaryScoreRealLinear U) hK
  exact hs.trans (((P a).componentProtocol (m a) k).scoreU_le_schmidtMass U hfoot)

/-- Original average-channel accuracy forces the same quantum spectral mass. -/
theorem mixedSharedRandom_unitary_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) (hscore : 1 - ε ≤ scoreU U (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  hscore.trans (mixedSharedRandom_scoreU_le_schmidtMass μ P m hP U hK)

/-- Accuracy is converted on the unchanged actual averaged channel before selection. -/
theorem mixedSharedRandom_scoreU_ge_of_diamondError_le
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε : ℝ} (herror : diamondError (mixedSharedRandomOperationalChannel μ P m).toLinearMap (adConj U) ≤ ε) :
    1 - ε ≤ scoreU U (mixedSharedRandomOperationalChannel μ P m).toLinearMap := by
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (mixedSharedRandomOperationalChannel μ P m)
    (mixedSharedRandomOperationalChannel_completelyPositive μ P m hP)
    (mixedSharedRandomOperationalChannel_tracePreserving μ P m hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError hU (mixedSharedRandomOperationalChannel μ P m).toLinearMap hphysical
  linarith

/-- The quantum spectral floor uses the error of the original actual probability average. -/
theorem mixedSharedRandom_unitary_spectral_floor_of_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) (herror : diamondError (mixedSharedRandomOperationalChannel μ P m).toLinearMap (adConj U) ≤ ε) :
    1 - ε ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  mixedSharedRandom_unitary_spectral_floor μ P m hP U hK
    (mixedSharedRandom_scoreU_ge_of_diamondError_le μ P m hP U hU herror)

/-- A target-only threshold applies to every original randomness branch architecture. -/
theorem mixedSharedRandom_unitary_full_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t) (hscore : 1 - ε ≤ scoreU U (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    d ^ 2 ≤ K := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (unitaryScoreRealLinear U) hK
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    ((P a).componentProtocol (m a) k).unitary_full_spectral_floor U hU hfoot ht hε (hscore.trans hs)

/-- A target-only threshold also applies to original average-channel error accuracy. -/
theorem mixedSharedRandom_unitary_full_spectral_floor_of_diamondError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix U) i) (hε : ε < t) (herror : diamondError (mixedSharedRandomOperationalChannel μ P m).toLinearMap (adConj U) ≤ ε) : d ^ 2 ≤ K :=
  mixedSharedRandom_unitary_full_spectral_floor μ P m hP U hU hK ht hε
    (mixedSharedRandom_scoreU_ge_of_diamondError_le μ P m hP U hU herror)

/-- Exact actual averaged implementation covers the target operator-Schmidt rank. -/
theorem mixedSharedRandom_unitary_exact_schmidt_rank_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) (hscore : 1 ≤ scoreU U (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    (normalizedLabChoiMatrix U).rank ≤ K :=
  rank_le_of_one_le_schmidtMass _ (norm_normalizedLabChoiMatrix_of_isometry hU)
    (hscore.trans (mixedSharedRandom_scoreU_le_schmidtMass μ P m hP U hK))

/-- The concrete flat target retains its quantum floor under actual shared randomness. -/
theorem mixedSharedRandom_swap_quantumFootprint_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d) (Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary (Fin d)) (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    (d : ℝ) ^ 2 * (1 - ε) ≤ K := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (unitaryScoreRealLinear (swapUnitary (Fin d))) hK
  simpa only [Fintype.card_fin] using ((P a).componentProtocol (m a) k).swap_quantumFootprint_floor hfoot (hscore.trans hs)

/-- The actual averaged score retains the original branchwise quantum mass bound. -/
theorem mixedSharedRandom_scorePVM_le_max_column_schmidtMass
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) : scorePVM M (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ pvmMaxColumnSchmidtMass K M := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (pvmScoreRealLinear M) hK
  exact hs.trans (((P a).componentProtocol (m a) k).scorePVM_le_max_column_schmidtMass M hfoot)

/-- Original average-channel accuracy forces the same quantum spectral mass. -/
theorem mixedSharedRandom_pvm_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) (hscore : 1 - ε ≤ scorePVM M (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  hscore.trans (mixedSharedRandom_scorePVM_le_max_column_schmidtMass μ P m hP M hK)

/-- Accuracy is converted on the unchanged actual averaged channel before selection. -/
theorem mixedSharedRandom_scorePVM_ge_of_pvmTVError_le
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε : ℝ} (herror : pvmTVError M (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ ε) :
    1 - ε ≤ scorePVM M (mixedSharedRandomOperationalChannel μ P m).toLinearMap := by
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (mixedSharedRandomOperationalChannel μ P m)
    (mixedSharedRandomOperationalChannel_completelyPositive μ P m hP)
    (mixedSharedRandomOperationalChannel_tracePreserving μ P m hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError hM hphysical
  linarith

/-- The quantum spectral floor uses the error of the original actual probability average. -/
theorem mixedSharedRandom_pvm_spectral_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K) (herror : pvmTVError M (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ ε) :
    1 - ε ≤ pvmMaxColumnSchmidtMass K M :=
  mixedSharedRandom_pvm_spectral_floor μ P m hP M hK
    (mixedSharedRandom_scorePVM_ge_of_pvmTVError_le μ P m hP M hM herror)

/-- A target-only threshold applies to every original randomness branch architecture. -/
theorem mixedSharedRandom_pvm_full_spectral_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t) (hscore : 1 - ε ≤ scorePVM M (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    d ≤ K := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (pvmScoreRealLinear M) hK
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    ((P a).componentProtocol (m a) k).pvm_full_spectral_floor M hM hfoot ht hε (hscore.trans hs)

/-- A target-only threshold also applies to original average-channel error accuracy. -/
theorem mixedSharedRandom_pvm_full_spectral_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) {ε t : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j) (hε : ε < t) (herror : pvmTVError M (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ ε) : d ≤ K :=
  mixedSharedRandom_pvm_full_spectral_floor μ P m hP M hM hK ht hε
    (mixedSharedRandom_scorePVM_ge_of_pvmTVError_le μ P m hP M hM herror)

/-- The concrete flat target retains its quantum floor under actual shared randomness. -/
theorem mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (hscore : 1 - ε ≤ scorePVM (generalizedBellFinMatrix d) (mixedSharedRandomOperationalChannel μ P m).toLinearMap) :
    (d : ℝ) * (1 - ε) ≤ K := by
  obtain ⟨a, k, hfoot, hs⟩ := exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint
    μ P m hP (pvmScoreRealLinear (generalizedBellFinMatrix d)) hK
  simpa only [Fintype.card_fin] using ((P a).componentProtocol (m a) k).generalizedBellPVM_quantumFootprint_floor hfoot (hscore.trans hs)

/-- The concrete Bell floor uses the TV error of the actual average channel. -/
theorem mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor_of_pvmTVError
    (P : ∀ a, StandardBorelClassicalProtocol (Fin d) (Fin d)
      (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin d × Fin d) (Fin d × Fin d))
    {n : α → ℕ} (m : ∀ a, MixedResource (ρA a) (ρB a) (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) μ) {ε : ℝ} (hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) K)
    (herror : pvmTVError (generalizedBellFinMatrix d) (mixedSharedRandomOperationalChannel μ P m).toLinearMap ≤ ε) :
    (d : ℝ) * (1 - ε) ≤ K :=
  mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor μ P m hP hK
    (mixedSharedRandom_scorePVM_ge_of_pvmTVError_le μ P m hP _
      (isIsometry_generalizedBellFinMatrix d) herror)

end

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory
open scoped MeasureTheory Matrix.Norms.Elementwise

set_option linter.checkUnivs false in
/-- Original quantum systems and outcome spaces, with their intrinsic model instances. -/

structure BorelSystems where
  ρA : Type u₁
  ρB : Type u₂
  κA : Type u₃
  κB : Type u₄
  μA : Type u₅
  μB : Type u₆
  σA : Type u₇
  σB : Type u₈
  fintypeρA : Fintype ρA
  fintypeρB : Fintype ρB
  fintypeκA : Fintype κA
  fintypeκB : Fintype κB
  fintypeμA : Fintype μA
  fintypeμB : Fintype μB
  decidableEqρA : DecidableEq ρA
  decidableEqρB : DecidableEq ρB
  decidableEqκA : DecidableEq κA
  decidableEqκB : DecidableEq κB
  decidableEqμA : DecidableEq μA
  decidableEqμB : DecidableEq μB
  measurableσA : MeasurableSpace σA
  measurableσB : MeasurableSpace σB
  standardBorelσA : @StandardBorelSpace σA measurableσA
  standardBorelσB : @StandardBorelSpace σB measurableσB

attribute [instance] BorelSystems.fintypeρA BorelSystems.fintypeρB
  BorelSystems.fintypeκA BorelSystems.fintypeκB BorelSystems.fintypeμA BorelSystems.fintypeμB
  BorelSystems.decidableEqρA BorelSystems.decidableEqρB BorelSystems.decidableEqκA
  BorelSystems.decidableEqκB BorelSystems.decidableEqμA BorelSystems.decidableEqμB
  BorelSystems.measurableσA BorelSystems.measurableσB
  BorelSystems.standardBorelσA BorelSystems.standardBorelσB

abbrev BorelSystems.Protocol (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (d : ℕ) (ιA' ιB' : Type*)
    [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA'] [DecidableEq ιB'] :=
  StandardBorelClassicalProtocol (Fin d) (Fin d) s.ρA s.ρB s.κA s.κB s.μA s.μB
    s.σA s.σB ιA' ιB'

set_option linter.checkUnivs false in
/-- A probability space with arbitrary branch-dependent original systems. -/

structure BorelRandomSystems where
  α : Type u₉
  measurableα : MeasurableSpace α
  μ : @Measure α measurableα
  probability : @IsProbabilityMeasure α measurableα μ
  systems : α → BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}

attribute [instance] BorelRandomSystems.measurableα BorelRandomSystems.probability

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).ρA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).ρA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).ρB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).ρB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).κA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).κA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).κB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).κB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).μA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).μA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, Fintype (s.systems a).μB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, DecidableEq (s.systems a).μB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, MeasurableSpace (s.systems a).σA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, StandardBorelSpace (s.systems a).σA :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, MeasurableSpace (s.systems a).σB :=
  fun _a => inferInstance

instance (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) : ∀ a, StandardBorelSpace (s.systems a).σB :=
  fun _a => inferInstance

abbrev BorelRandomSystems.Protocol (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (d : ℕ) (ιA' ιB' : Type*)
    [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA'] [DecidableEq ιB'] :=
  ∀ a, (s.systems a).Protocol d ιA' ιB'

noncomputable section

noncomputable local instance targetMatrixNormedAddCommGroup {ν : Type*} [Fintype ν] :
    NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance targetMatrixTopologicalSpace {ν : Type*} [Fintype ν] :
    TopologicalSpace (Matrix ν ν ℂ) :=
  (targetMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance targetMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance targetMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance targetOperationNormedAddCommGroup {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance targetOperationRealNormedSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

open StandardBorelClassicalProtocol

/-- Actual pure or common-map mixed protocols with the original quantum cap.
The zero-dimensional class is empty; no outcome-class measurability is asserted. -/
def borelScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  if hd : 0 < d then
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    {T | ∃ s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}, ∃ P : s.Protocol d (Fin d) (Fin d),
      (P.HasQuantumFootprint K ∧ 1 - ε ≤ scoreU (T : Matrix _ _ ℂ) P.operationalChannel.toLinearMap) ∨
      ∃ n : ℕ, ∃ m : MixedResource s.ρA s.ρB n, P.HasMixedQuantumFootprint m K ∧
        1 - ε ≤ scoreU (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m)}
  else ∅

/-- Actual target membership embeds by score into the derived charged class. -/
theorem borelScoreReachable_subset_pureReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε ⊆ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro T hT
  rw [borelScoreReachable, dite_eq_left hd] at hT
  rcases hT with ⟨s, P, hacc⟩
  rcases hacc with ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩
  · exact P.mem_pureReachable_of_quantumFootprint T hd hK hs
  · exact P.mem_pureReachable_of_mixedQuantumFootprint m T hd hK hs

/-- Actual pure or common-map mixed protocols with the original quantum cap.
The zero-dimensional class is empty; no outcome-class measurability is asserted. -/
def borelPVMScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  if hd : 0 < d then
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    {T | ∃ s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}, ∃ P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d),
      (P.HasQuantumFootprint K ∧ 1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) P.operationalChannel.toLinearMap) ∨
      ∃ n : ℕ, ∃ m : MixedResource s.ρA s.ρB n, P.HasMixedQuantumFootprint m K ∧
        1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m)}
  else ∅

/-- Actual target membership embeds by score into the derived charged class. -/
theorem borelPVMScoreReachable_subset_purePVMReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε ⊆ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro T hT
  rw [borelPVMScoreReachable, dite_eq_left hd] at hT
  rcases hT with ⟨s, P, hacc⟩
  rcases hacc with ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩
  · exact P.mem_purePVMReachable_of_quantumFootprint T hd hK hs
  · exact P.mem_purePVMReachable_of_mixedQuantumFootprint m T hd hK hs

/-- Actual probability-averaged pure or common-map mixed protocols with the original quantum cap.
The zero-dimensional class is empty; no outcome-class measurability is asserted. -/
def borelSharedRandomScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  if hd : 0 < d then
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    {T | ∃ s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}, ∃ P : s.Protocol d (Fin d) (Fin d),
      (AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ ∧
        (∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) ∧
        1 - ε ≤ scoreU (T : Matrix _ _ ℂ) (sharedRandomOperationalChannel s.μ P).toLinearMap) ∨
      ∃ n : s.α → ℕ, ∃ m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a),
        AEStronglyMeasurable (mixedBranchOperation P m) s.μ ∧
        (∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) ∧
        1 - ε ≤ scoreU (T : Matrix _ _ ℂ) (mixedSharedRandomOperationalChannel s.μ P m).toLinearMap}
  else ∅

/-- Actual target membership embeds by score into the derived charged class. -/
theorem borelSharedRandomScoreReachable_subset_pureReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε ⊆ pureReachable d (4 * d ^ 4 * K ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro T hT
  rw [borelSharedRandomScoreReachable, dite_eq_left hd] at hT
  rcases hT with ⟨s, P, hacc⟩
  rcases hacc with ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩
  · exact mem_pureReachable_of_sharedRandom_quantumFootprint s.μ P hP T hd hK hs
  · exact mem_pureReachable_of_mixedSharedRandom_quantumFootprint s.μ P m hP T hd hK hs

/-- Actual probability-averaged pure or common-map mixed protocols with the original quantum cap.
The zero-dimensional class is empty; no outcome-class measurability is asserted. -/
def borelSharedRandomPVMScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  if hd : 0 < d then
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    {T | ∃ s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}, ∃ P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d),
      (AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ ∧
        (∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) ∧
        1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) (sharedRandomOperationalChannel s.μ P).toLinearMap) ∨
      ∃ n : s.α → ℕ, ∃ m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a),
        AEStronglyMeasurable (mixedBranchOperation P m) s.μ ∧
        (∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) ∧
        1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) (mixedSharedRandomOperationalChannel s.μ P m).toLinearMap}
  else ∅

/-- Actual target membership embeds by score into the derived charged class. -/
theorem borelSharedRandomPVMScoreReachable_subset_purePVMReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε ⊆ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro T hT
  rw [borelSharedRandomPVMScoreReachable, dite_eq_left hd] at hT
  rcases hT with ⟨s, P, hacc⟩
  rcases hacc with ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩
  · exact mem_purePVMReachable_of_sharedRandom_quantumFootprint s.μ P hP T hd hK hs
  · exact mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint s.μ P m hP T hd hK hs

/-- The union includes original pure/mixed protocols and their honest averaged counterparts. -/
def borelAllScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε ∪ borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε

theorem borelAllScoreReachable_subset_pureReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε ⊆ pureReachable d (4 * d ^ 4 * K ^ 5) ε :=
  Set.union_subset (borelScoreReachable_subset_pureReachable hd ε) (borelSharedRandomScoreReachable_subset_pureReachable hd ε)

/-- The union includes original pure/mixed protocols and their honest averaged counterparts. -/
def borelAllPVMScoreReachable (d K : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε ∪ borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε

theorem borelAllPVMScoreReachable_subset_purePVMReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε ⊆ purePVMReachable d (4 * d ^ 4 * K ^ 5) ε :=
  Set.union_subset (borelPVMScoreReachable_subset_purePVMReachable hd ε) (borelSharedRandomPVMScoreReachable_subset_purePVMReachable hd ε)

set_option maxHeartbeats 600000 in
/-- Almost every fixed target has one positive spectral threshold for every
original Borel architecture and actual pure/mixed probability-average channel.
This is the quantum footprint floor, with the original d² and d conclusions. -/

theorem ae_borel_classical_full_spectral_threshold (d : ℕ) [NeZero d] :
    ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (K : ℕ) (ε : ℝ), ε < η →
        (T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε → d ^ 2 ≤ K) ∧
        (T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε → d ≤ K) := by
  filter_upwards [ae_unitary_pos_schmidtWeight_lower_bound d,
    ae_pvm_pos_uniform_schmidtWeight_lower_bound d] with T hU hM
  obtain ⟨tU, htU, hwU⟩ := hU
  obtain ⟨tM, htM, hwM⟩ := hM
  let η := min 1 (min tU tM)
  refine ⟨η, lt_min (by norm_num) (lt_min htU htM), min_le_left _ _, ?_⟩
  intro K ε hε
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hεU : ε < tU := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε < tM := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hT : IsIsometry (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp T.property
  constructor
  · intro hreach
    rcases hreach with hreach | hreach
    · rw [borelScoreReachable, dite_eq_left hd] at hreach
      rcases hreach with ⟨s, P, hacc⟩
      rcases hacc with ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩
      · simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
          P.unitary_full_spectral_floor (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
      · simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
          P.mixed_unitary_full_spectral_floor m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
    · rw [borelSharedRandomScoreReachable, dite_eq_left hd] at hreach
      rcases hreach with ⟨s, P, hacc⟩
      rcases hacc with ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩
      · exact sharedRandom_unitary_full_spectral_floor s.μ P hP (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
      · exact mixedSharedRandom_unitary_full_spectral_floor s.μ P m hP (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwU hεU hs
  · intro hreach
    rcases hreach with hreach | hreach
    · rw [borelPVMScoreReachable, dite_eq_left hd] at hreach
      rcases hreach with ⟨s, P, hacc⟩
      rcases hacc with ⟨hK, hs⟩ | ⟨n, m, hK, hs⟩
      · simpa only [Fintype.card_fin] using
          P.pvm_full_spectral_floor (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs
      · simpa only [Fintype.card_fin] using
          P.mixed_pvm_full_spectral_floor m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs
    · rw [borelSharedRandomPVMScoreReachable, dite_eq_left hd] at hreach
      rcases hreach with ⟨s, P, hacc⟩
      rcases hacc with ⟨hP, hK, hs⟩ | ⟨n, m, hP, hK, hs⟩
      · exact sharedRandom_pvm_full_spectral_floor s.μ P hP (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs
      · exact mixedSharedRandom_pvm_full_spectral_floor s.μ P m hP (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hT hK hwM hεM hs

end

end NLQCLean.ClassicalCommunication
