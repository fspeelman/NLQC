import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.FiniteControlledPhaseAlmostEvery
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Initial-resource qubits for finite LOSCC controlled-phase protocols

The qubit cap bounds the product of the two original resource dimensions,
not their Schmidt rank by assumption. matrix-rank bounds supply a
common Schmidt-number cap for every component of a finite mixed resource.
Both quantum message dimensions are one, as required for LOSCC. Classical
alphabets and fresh private workspace are not charged. No expected-budget,
shared-randomness or standard-Borel extension is asserted.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory ClassicalCommunication

/-- The Schmidt rank is bounded by both original resource dimensions. -/
theorem schmidtRank_sq_le_resource_card_product
    {ρA ρB : Type*} [Fintype ρA] [Fintype ρB] (η : ρA × ρB → ℂ) :
    schmidtRank η ^ 2 ≤ Fintype.card ρA * Fintype.card ρB := by
  simpa only [pow_two] using
    Nat.mul_le_mul (schmidtRank_le_card_left η) (schmidtRank_le_card_right η)

/-- An initial-resource dimension cap gives the pure-state rank bound. -/
theorem schmidtRank_le_sqrt_resource_qubit_cap
    {ρA ρB : Type*} [Fintype ρA] [Fintype ρB] (η : ρA × ρB → ℂ) (q : ℕ)
    (hq : Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q) :
    (schmidtRank η : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ q) := by
  have hs : (schmidtRank η : ℝ) ^ 2 ≤ (2 : ℝ) ^ q := by
    exact_mod_cast (schmidtRank_sq_le_resource_card_product η).trans hq
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ q by positivity),
    Real.sqrt_nonneg ((2 : ℝ) ^ q)]

/-- Every component obeys a common dimensional Schmidt-number cap;
this neither bounds the mixed-state support nor discards zero-weight components. -/
theorem MixedResource.schmidtNumberLE_min_resource_card
    {ρA ρB : Type*} [Fintype ρA] [Fintype ρB] {n : ℕ}
    (m : MixedResource ρA ρB n) :
    m.schmidtNumberLE (min (Fintype.card ρA) (Fintype.card ρB)) := by
  intro k
  exact le_min (schmidtRank_le_card_left (m.component k))
    (schmidtRank_le_card_right (m.component k))

/-- The common dimensional cap has the same squared resource-dimension bound. -/
theorem min_resource_card_sq_le_product {ρA ρB : Type*}
    [Fintype ρA] [Fintype ρB] :
    min (Fintype.card ρA) (Fintype.card ρB) ^ 2 ≤
      Fintype.card ρA * Fintype.card ρB := by
  simpa only [pow_two] using Nat.mul_le_mul
    (min_le_left (Fintype.card ρA) (Fintype.card ρB))
    (min_le_right (Fintype.card ρA) (Fintype.card ρB))

/-- The coefficient `1/5` follows from a tenth-power footprint estimate and
a pointwise squared footprint cap. The latter is not an expected qubit cap. -/
theorem qubit_lower_of_tenth_power_and_squared_footprint {C L : ℝ} {Kq q : ℕ}
    (hC : 0 < C) (hL : 0 < L) (hlog : L ≤ C * (Kq : ℝ) ^ 10)
    (hq : Kq ^ 2 ≤ 2 ^ q) :
    (1 / 5 : ℝ) * Real.logb 2 L - max 0 ((1 / 5 : ℝ) * Real.logb 2 C) ≤
      (q : ℝ) := by
  have hqR : (Kq : ℝ) ^ 2 ≤ (2 : ℝ) ^ q := by exact_mod_cast hq
  have hpower : (Kq : ℝ) ^ 10 ≤ (2 : ℝ) ^ (5 * q) := by
    calc
      (Kq : ℝ) ^ 10 = ((Kq : ℝ) ^ 2) ^ 5 := by ring
      _ ≤ ((2 : ℝ) ^ q) ^ 5 := pow_le_pow_left₀ (by positivity) hqR 5
      _ = (2 : ℝ) ^ (5 * q) := by rw [← pow_mul, Nat.mul_comm]
  have hbound := hlog.trans (mul_le_mul_of_nonneg_left hpower hC.le)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hL hbound
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  push_cast at hl
  linarith [le_max_right (0 : ℝ) ((1 / 5 : ℝ) * Real.logb 2 C)]

/-- For finite LOSCC, the original resource dimensions supply the quantum
footprint cap. One additive constant precedes the fixed phase, whose threshold
precedes all errors, qubit caps, original finite architectures and protocols. -/
theorem exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂),
        ∀ [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
          [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB],
        ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
          [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
        ∀ P : FiniteClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB ηA ηB (Fin 2) (Fin 2) εA εB,
        Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
        Fintype.card μA = 1 → Fintype.card μB = 1 →
        ((1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (diamondError P.operationalChannel (adConj (controlledPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ))) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n),
          (1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (diamondError (P.mixedOperationalChannel m) (adConj (controlledPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ))) := by
  obtain ⟨C, hC, hae⟩ := exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound hGeom
  refine ⟨max 0 ((1 / 5 : ℝ) * Real.logb 2 C), le_max_left _ _, ?_⟩
  filter_upwards [hae] with θ hθ
  obtain ⟨ε₀, hε₀pos, hε₀half, hphase⟩ := hθ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro q ε hε hε₀ ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hq hμA hμB
  let R := min (Fintype.card ρA) (Fintype.card ρB)
  have hR : R ^ 2 ≤ 2 ^ q :=
    (min_resource_card_sq_le_product (ρA := ρA) (ρB := ρB)).trans hq
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith))
  have hfoot : P.HasQuantumFootprint R := by
    apply (hasFootprint_iff R P.resource).mpr
    simpa only [hμA, hμB, mul_one] using
      le_min (schmidtRank_le_card_left P.resource) (schmidtRank_le_card_right P.resource)
  have hbound := hphase R ε hε hε₀ ρA ρB κA κB μA μB σA σB ηA ηB εA εB P
  have harithmetic : Real.log (1 / ε) ≤ C * (R : ℝ) ^ 10 →
      (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
        max 0 ((1 / 5 : ℝ) * Real.logb 2 C) ≤ (q : ℝ) :=
    fun h => qubit_lower_of_tenth_power_and_squared_footprint hC hL h hR
  refine ⟨⟨fun hs => harithmetic ((hbound.1 hfoot).1 hs),
    fun he => harithmetic ((hbound.1 hfoot).2 he)⟩, ?_⟩
  intro n m
  have hfootm : P.HasMixedQuantumFootprint m R := by
    apply (P.hasMixedQuantumFootprint_iff_rank_bound m R).mpr
    exact ⟨R, m.schmidtNumberLE_min_resource_card,
      by simpa only [hμA, hμB, mul_one] using (le_refl R)⟩
  exact ⟨fun hs => harithmetic ((hbound.2 n m hfootm).1 hs),
    fun he => harithmetic ((hbound.2 n m hfootm).2 he)⟩

/-- The finite LOSCC qubit corollary retains exactly the three unchanged
geometry arguments. Resource and message accounting are proved internally. -/
theorem exists_ae_finiteLOSCCControlledPhase_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          (ηA : Type u₉) (ηB : Type u₁₀) (εA : Type u₁₁) (εB : Type u₁₂),
        ∀ [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
          [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB],
        ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
          [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB],
        ∀ P : FiniteClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB ηA ηB (Fin 2) (Fin 2) εA εB,
        Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q →
        Fintype.card μA = 1 → Fintype.card μB = 1 →
        ((1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (diamondError P.operationalChannel (adConj (controlledPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ))) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n),
          (1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (diamondError (P.mixedOperationalChannel m) (adConj (controlledPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ))) :=
  exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean
