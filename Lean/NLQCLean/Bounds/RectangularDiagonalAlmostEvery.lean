import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Geometry.DiagonalPhaseMeasure
import NLQCLean.Bounds.FiniteControlledPhaseQubits
import NLQCLean.Bounds.ResourceArithmetic
import NLQCLean.Bounds.FiniteClassicalQubits
import NLQCLean.Models.ClassicalCommunication.FiniteOutputRestriction

/-!
# Almost-every rectangular diagonal resource rates

Uniform independent phases are pulled back through the alternating four-entry
phase. The actual finite protocol restriction preserves the resource and both
messages and contracts normalized diamond error, including every finite ancilla.
Controlled-phase rates then give charged coefficient `1/2`, finite quantum-footprint
coefficient `1/10`, and finite LOSCC initial-resource-qubit coefficient `1/5`.
All constants are universal and each fixed target has a threshold before every
budget and original finite architecture. The finite/common-map mixed model is
explicit; these results do not supply the standard-Borel or shared-randomness scope.

The source is `thm:diagonal` and its rectangular restriction paragraph in the
revised robust companion, `fixed-dimension.tex`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory ClassicalCommunication

/-- Rectangular finite-classical logarithm rate on original channels. The
same target-only threshold serves pure and common-map mixed protocols. -/
theorem exists_ae_finiteRectangularDiagonal_log_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) := by
  obtain ⟨C, hC, hae⟩ :=
    exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉, u₁₀, u₁₁, u₁₂} hGeom
  refine ⟨C, hC, fun dA dB hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro Kq ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  let Q := P.restrictRectangularDiagonal hA hB θ
  have hbound := hphase Kq ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB
    (Fin dA × εA) (Fin dB × εB) Q
  have hgate := controlledPhase_rectangularAlternatingAngleMod hA hB θ
  refine ⟨?_, ?_⟩
  · intro hK he
    apply (hbound.1 ((P.restrictRectangularDiagonal_hasQuantumFootprint_iff hA hB θ Kq).mpr hK)).2
    rw [hgate]
    exact (P.restrictRectangularDiagonal_diamondError_le hA hB θ).trans he
  · intro n m hK he
    apply (hbound.2 n m
      ((P.restrictRectangularDiagonal_hasMixedQuantumFootprint_iff hA hB θ m Kq).mpr hK)).2
    rw [hgate]
    exact (P.restrictRectangularDiagonal_mixedDiamondError_le hA hB θ m).trans he

/-- The original rectangular diamond predicate yields coefficient `1/10`
on the double logarithm of error versus quantum footprint. -/
theorem exists_ae_finiteRectangularDiagonal_qubit_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) := by
  obtain ⟨C, hC, hae⟩ := exists_ae_finiteRectangularDiagonal_log_bound_of_imageVolumeBound hGeom
  refine ⟨max 0 (Real.logb 2 C / 10), le_max_left _ _, fun dA dB hA hB => ?_⟩
  filter_upwards [hae dA dB hA hB] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro Kq ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have harithmetic (hlog : Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) :
      (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
        max 0 (Real.logb 2 C / 10) ≤ Real.logb 2 (Kq : ℝ) := by
    have hK : 0 < Kq := by
      by_contra hn
      have hz : Kq = 0 := Nat.eq_zero_of_not_pos hn
      rw [hz] at hlog
      rw [Nat.cast_zero, zero_pow (by decide : (10 : ℕ) ≠ 0), mul_zero] at hlog
      linarith
    simpa using quantumFootprint_log_of_tenth_power_bound (a := 0) (n := 0)
      hC hL hK (by simpa using hlog)
  have hbound := hphase Kq ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB εA εB P
  exact ⟨fun hK he => harithmetic (hbound.1 hK he),
    fun n m hK he => harithmetic (hbound.2 n m hK he)⟩

/-- In finite LOSCC, the original resource dimensions have product at most
`2^q` and both quantum messages have dimension one. The original rectangular
diamond predicate then gives coefficient `1/5`. -/
theorem exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
          Fintype.card μA = 1 → Fintype.card μB = 1 →
          (diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n),
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨B, hB, hae⟩ :=
    exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉, u₁₀, u₁₁, u₁₂} hGeom
  refine ⟨B, hB, fun dA dB hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro q ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hq hμA hμB
  let Q := P.restrictRectangularDiagonal hA hB θ
  have hbound := hphase q ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB
    (Fin dA × εA) (Fin dB × εB) Q hq hμA hμB
  have hgate := controlledPhase_rectangularAlternatingAngleMod hA hB θ
  refine ⟨?_, ?_⟩
  · intro he
    apply hbound.1.2
    rw [hgate]
    exact (P.restrictRectangularDiagonal_diamondError_le hA hB θ).trans he
  · intro n m he
    apply (hbound.2 n m).2
    rw [hgate]
    exact (P.restrictRectangularDiagonal_mixedDiamondError_le hA hB θ m).trans he

/-- Charging both coherent outcome flags gives coefficient `1/2`. The mixed
channel is converted to score before any component selection; its common
Schmidt-number cap charges both original quantum messages and both flags. -/
theorem exists_ae_paidRectangularDiagonal_qubit_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (schmidtRank P.resource * (Fintype.card μA * Fintype.card σA) *
              (Fintype.card μB * Fintype.card σB) ≤ K →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n) (R : ℕ), m.schmidtNumberLE R →
            R * (Fintype.card μA * Fintype.card σA) *
              (Fintype.card μB * Fintype.card σB) ≤ K →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, fun dA dB hA hB => ?_⟩
  filter_upwards [ae_rectangularAlternatingAngleMod_of_ae hA hB hae] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro K ε hε hee ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  let Q := P.restrictRectangularDiagonal hA hB θ
  let φ := rectangularAlternatingAngleMod hA hB θ
  have hU := Matrix.mem_unitaryGroup_iff'.mp (controlledPhaseTarget φ).property
  have hgate := controlledPhase_rectangularAlternatingAngleMod hA hB θ
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have harithmetic (h : c * Real.sqrt (Real.log (1 / ε)) ≤ (K : ℝ)) :
      (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
        max 0 (-Real.logb 2 c) ≤ Real.logb 2 (K : ℝ) := by
    simpa using qubit_lower_of_resource hc hL 0 (by simpa using h)
  refine ⟨?_, ?_⟩
  · intro hK he
    have heQ : diamondError Q.coherentProtocol.operationalChannel
        (adConj (controlledPhase φ)) ≤ ε := by
      rw [Q.coherentProtocol_operationalChannel, hgate]
      exact (P.restrictRectangularDiagonal_diamondError_le hA hB θ).trans he
    have hs := Q.coherentProtocol.scoreU_ge_of_diamondError_le hU heQ
    have hfoot : Q.coherentProtocol.HasFootprint K :=
      (Q.coherentProtocol_hasFootprint_iff K).mpr hK
    exact harithmetic ((hphase K ε hε hee).1
      (Q.coherentProtocol.mem_pureReachable (U := controlledPhaseTarget φ) hfoot hs))
  · intro n m R hR hK he
    have heQ : diamondError (Q.mixedOperationalChannel m)
        (adConj (controlledPhase φ)) ≤ ε := by
      rw [hgate]
      exact (P.restrictRectangularDiagonal_mixedDiamondError_le hA hB θ m).trans he
    have hs := m.scoreU_ge_of_diamondError_le
      Q.coherentProtocol.encA_isometry Q.coherentProtocol.encB_isometry
      Q.coherentProtocol.decA_isometry Q.coherentProtocol.decB_isometry hU
      (by simpa only [controlledPhaseTarget,
        Q.mixedOperationalChannel_eq_coherentMixedChannel] using heQ)
    have hpaid : R * Fintype.card (μA × σA) * Fintype.card (μB × σB) ≤ K := by
      simpa only [Fintype.card_prod] using hK
    exact harithmetic ((hphase K ε hε hee).2
      (m.mem_mixedReachable Q.coherentProtocol.encA Q.coherentProtocol.encB
        Q.coherentProtocol.decA Q.coherentProtocol.decB
        Q.coherentProtocol.encA_isometry Q.coherentProtocol.encB_isometry
        Q.coherentProtocol.decA_isometry Q.coherentProtocol.decB_isometry hR hpaid
        (U := controlledPhaseTarget φ) hs))

/-- The one-outcome specialization preserves the entire common-map mixed
channel, before any conversion of diamond error to score. -/
theorem ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol
    {dA dB : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (Q : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB (Fin dA) (Fin dB) εA εB)
    {n : ℕ} (m : MixedResource ρA ρB n) :
    (FiniteClassicalProtocol.ofPureProtocol Q).mixedOperationalChannel m =
      m.mixedChannel Q.encA Q.encB Q.decA Q.decB := by
  rw [FiniteClassicalProtocol.mixedOperationalChannel, MixedResource.mixedChannel]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun N => (m.weight k : ℂ) • N)
  let Qk : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
      (Fin dA) (Fin dB) εA εB :=
    { Q with resource := m.component k, resource_unit := m.component_unit k }
  change (FiniteClassicalProtocol.ofPureProtocol Qk).operationalChannel = Qk.operationalChannel
  exact FiniteClassicalProtocol.operationalChannel_ofPureProtocol Qk

/-- Original eight-register charged protocols are the one-outcome
specialization of the paid-flag theorem. The mixed branch uses the original
common encoder/decoder maps and a Schmidt-number cap, with both messages. -/
theorem exists_ae_chargedRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            (Fin dA) (Fin dB) εA εB,
          (P.HasFootprint K →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n) (R : ℕ), m.schmidtNumberLE R →
            R * Fintype.card μA * Fintype.card μB ≤ K →
            diamondError (m.mixedChannel P.encA P.encB P.decA P.decB)
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨B, hB, hae⟩ :=
    exists_ae_paidRectangularDiagonal_qubit_bound_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, 0, 0, 0, 0, u₇, u₈} hGeom
  refine ⟨B, hB, fun dA dB hA hB => ?_⟩
  filter_upwards [hae dA dB hA hB] with θ hθ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro K ε hε hee ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  let Q := FiniteClassicalProtocol.ofPureProtocol P
  have hbound := hphase K ε hε hee ρA ρB κA κB μA μB Unit Unit Unit Unit εA εB Q
  refine ⟨?_, ?_⟩
  · intro hK he
    have hpaid : schmidtRank Q.resource * (Fintype.card μA * Fintype.card Unit) *
        (Fintype.card μB * Fintype.card Unit) ≤ K := by
      simpa only [Q, FiniteClassicalProtocol.ofPureProtocol, Fintype.card_unique, mul_one] using
        (hasFootprint_iff K P.resource).mp hK
    apply hbound.1 hpaid
    simpa only [Q, FiniteClassicalProtocol.operationalChannel_ofPureProtocol] using he
  · intro n m R hR hK he
    apply hbound.2 n m R hR
    · simpa only [Fintype.card_unique, mul_one] using hK
    · simpa only [Q, FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol] using he

/-- With the original rectangular error predicate and a threshold before every budget and register. -/
theorem exists_ae_finiteRectangularDiagonal_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) :=
  exists_ae_finiteRectangularDiagonal_log_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- With the original rectangular error predicate and a threshold before every budget and register. -/
theorem exists_ae_finiteRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (P.HasQuantumFootprint Kq →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 10 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (Kq : ℝ)) :=
  exists_ae_finiteRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- With the original rectangular error predicate and a threshold before every budget and register. -/
theorem exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
          Fintype.card μA = 1 → Fintype.card μB = 1 →
          (diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n),
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) :=
  exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- With the original rectangular error predicate and a threshold before every budget and register. -/
theorem exists_ae_paidRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
            (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
            [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
            [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : FiniteClassicalProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            σA σB ηA ηB (Fin dA) (Fin dB) εA εB,
          (schmidtRank P.resource * (Fintype.card μA * Fintype.card σA) *
              (Fintype.card μB * Fintype.card σB) ≤ K →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n) (R : ℕ), m.schmidtNumberLE R →
            R * (Fintype.card μA * Fintype.card σA) *
              (Fintype.card μB * Fintype.card σB) ≤ K →
            diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_paidRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- With the original rectangular error predicate and a threshold before every budget and register. -/
theorem exists_ae_chargedRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ dA dB : ℕ, 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          ∀ P : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB
            (Fin dA) (Fin dB) εA εB,
          (P.HasFootprint K →
            diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n) (R : ℕ), m.schmidtNumberLE R →
            R * Fintype.card μA * Fintype.card μB ≤ K →
            diamondError (m.mixedChannel P.encA P.encB P.decA P.decB)
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ Real.logb 2 (K : ℝ)) :=
  exists_ae_chargedRectangularDiagonal_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean
