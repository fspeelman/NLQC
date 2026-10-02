import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.BorelSharedRandomRectangular
import NLQCLean.Bounds.FiniteControlledPhaseQubits
import NLQCLean.Bounds.AlmostEveryPhysical
import NLQCLean.Bounds.Quantitative

/-!
# Initial resource qubits in LOSCC with free shared randomness

The resource-qubit count `n_res` of `thm:diagonal` lets shared randomness and
local workspace be free and bounds the number of initial resource qubits in
every branch. With only classical messages (both quantum message dimensions
one), a branch whose resource dimensions have product at most `2^q` has quantum
footprint at most `⌊√(2^q)⌋`, whose square is at most `2^q`. The tenth-power
logarithm bounds then give `q ≥ (1/5) log₂ ln(1/ε) - B`:

* rectangular diagonal gates, pure and common-map mixed branches, normalized
  diamond error (`thm:diagonal` (ii));
* two-qubit diagonal gates with Choi infidelity (`thm:diagonal`, two qubits);
* Haar-almost every two-qubit unitary (`rem:two-qubit`).
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory ClassicalCommunication

noncomputable section

noncomputable local instance losccMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance losccMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (losccMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance losccMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance losccMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance losccOperationNormedAddCommGroup
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedAddCommGroup (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance losccOperationRealNormedSpace
    {ι κ : Type*} [Fintype ι] [Fintype κ] : NormedSpace ℝ (MatrixOperation ι κ) :=
  ContinuousLinearMap.toNormedSpace

section Footprint

variable {ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]

omit [Fintype ιA] [Fintype ιB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
  [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
  [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq ιA']
  [DecidableEq ιB'] [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA]
  [StandardBorelSpace σB] in
theorem min_card_le_sqrt_two_pow {q : ℕ} (hcard : Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q) :
    min (Fintype.card ρA) (Fintype.card ρB) ≤ Nat.sqrt (2 ^ q) :=
  Nat.le_sqrt.mpr (by simpa only [pow_two] using
    (min_resource_card_sq_le_product (ρA := ρA) (ρB := ρB)).trans hcard)

/-- In LOSCC, `q` resource qubits give quantum footprint at most `⌊√(2^q)⌋`. -/
theorem ClassicalCommunication.StandardBorelClassicalProtocol.hasQuantumFootprint_of_loscc
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB') {q : ℕ}
    (hcard : Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q)
    (hμA : Fintype.card μA = 1) (hμB : Fintype.card μB = 1) :
    P.HasQuantumFootprint (Nat.sqrt (2 ^ q)) := by
  apply (hasFootprint_iff _ P.resource).mpr
  rw [hμA, hμB, mul_one, mul_one]
  exact (le_min (schmidtRank_le_card_left P.resource)
    (schmidtRank_le_card_right P.resource)).trans (min_card_le_sqrt_two_pow hcard)

theorem ClassicalCommunication.StandardBorelClassicalProtocol.hasMixedQuantumFootprint_of_loscc
    (P : StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB') {q n : ℕ}
    (m : MixedResource ρA ρB n) (hcard : Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q)
    (hμA : Fintype.card μA = 1) (hμB : Fintype.card μB = 1) :
    P.HasMixedQuantumFootprint m (Nat.sqrt (2 ^ q)) :=
  (P.hasMixedQuantumFootprint_iff_rank_bound m _).mpr
    ⟨Nat.sqrt (2 ^ q), fun k => (m.schmidtNumberLE_min_resource_card k).trans
      (min_card_le_sqrt_two_pow hcard), by rw [hμA, hμB, mul_one, mul_one]⟩

theorem sqrt_two_pow_sq_le (q : ℕ) : Nat.sqrt (2 ^ q) ^ 2 ≤ 2 ^ q := by
  simpa only [pow_two] using Nat.sqrt_le (2 ^ q)

/-- From `L ≤ C ⌊√(2^q)⌋¹⁰` to `q ≥ (1/5) log₂ L - B`. -/
theorem loscc_qubit_lower {C L : ℝ} {q : ℕ} (hC : 0 < C) (hL : 0 < L)
    (hlog : L ≤ C * ((Nat.sqrt (2 ^ q) : ℕ) : ℝ) ^ 10) :
    (1 / 5 : ℝ) * Real.logb 2 L - max 0 ((1 / 5 : ℝ) * Real.logb 2 C) ≤ (q : ℝ) :=
  qubit_lower_of_tenth_power_and_squared_footprint hC hL hlog (sqrt_two_pow_sq_le q)

end Footprint

/-- **`thm:diagonal` (ii), `n_res` with free shared randomness.** For almost
every rectangular diagonal phase there is a threshold below which every LOSCC
protocol with free shared randomness, at most `q` initial resource qubits in
every branch and normalized diamond error `ε`, has `q ≥ (1/5) log₂ ln(1/ε) - B`,
for pure and for common-map mixed branch resources. -/
theorem exists_ae_sharedRandomLOSCCRectangularDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dA dB : ℕ) [NeZero dA] [NeZero dB], 2 ≤ dA → 2 ≤ dB →
      ∀ᵐ θ ∂rectangularPhaseMeasure dA dB,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin dA) (Fin dB)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin dA) (Fin dB)),
          (∀ᵐ a ∂μ, Fintype.card (ρA a) * Fintype.card (ρB a) ≤ 2 ^ q ∧
            Fintype.card (μA a) = 1 ∧ Fintype.card (μB a) = 1) →
          (AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
            diamondError (averageOperationalChannel μ (fun a => (P a).operationalChannel)).toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : α → ℕ) (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
            AEStronglyMeasurable
              (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap) μ →
            diamondError (averageOperationalChannel μ
                (fun a => ((P a).mixedOperationalChannel (m a)).toContinuousLinearMap)).toLinearMap
              (adConj (rectangularDiagonalPhase θ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨C₁, hC₁, hpure⟩ :=
    exists_ae_sharedRandomRectangularDiagonal_log_bound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  obtain ⟨C₂, hC₂, hmixed⟩ :=
    exists_ae_mixedSharedRandomRectangularDiagonal_log_bound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}
  refine ⟨max (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₁)) (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₂)),
    le_max_of_le_left (le_max_left _ _), fun dA dB _ _ hA hB => ?_⟩
  filter_upwards [hpure dA dB hA hB, hmixed dA dB hA hB] with θ h₁ h₂
  obtain ⟨ε₁, hε₁, hε₁half, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, hε₂half, h₂⟩ := h₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hε₁half, ?_⟩
  intro q ε hε hsmall α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hcap
  have hL : 0 < Real.log (1 / ε) :=
    Real.log_pos ((one_lt_div₀ hε).mpr (by linarith [hsmall.trans (min_le_left _ _)]))
  refine ⟨fun hP he => ?_, fun n m hP he => ?_⟩
  · have hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasQuantumFootprint_of_loscc ha.1 ha.2.1 ha.2.2
    have hlog := h₁ (Nat.sqrt (2 ^ q)) ε hε (hsmall.trans (min_le_left _ _)) α μ ρA ρB κA κB
      μA μB σA σB P hP hK he
    have := loscc_qubit_lower hC₁ hL hlog
    linarith [le_max_left (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₁))
      (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₂))]
  · have hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasMixedQuantumFootprint_of_loscc (m a) ha.1 ha.2.1 ha.2.2
    have hlog := h₂ (Nat.sqrt (2 ^ q)) ε hε (hsmall.trans (min_le_right _ _)) α μ ρA ρB κA κB
      μA μB σA σB P n m hP hK he
    have := loscc_qubit_lower hC₂ hL hlog
    linarith [le_max_right (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₁))
      (max 0 ((1 / 5 : ℝ) * Real.logb 2 C₂))]

/-- From a charged `c' √ln(1/ε) ≤ 16 Kq⁵` bound at `Kq = ⌊√(2^q)⌋` to the qubit count. -/
theorem loscc_qubit_lower_of_charged {c ε : ℝ} {q : ℕ} (hc : 0 < c) (hε : 0 < ε)
    (hε1 : ε < 1)
    (h : c * Real.sqrt (Real.log (1 / ε)) ≤ ((2 ^ 4 * Nat.sqrt (2 ^ q) ^ 5 : ℕ) : ℝ)) :
    (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) -
      max 0 ((1 / 5 : ℝ) * Real.logb 2 (256 / c ^ 2)) ≤ (q : ℝ) := by
  have hL : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div₀ hε).mpr hε1)
  apply loscc_qubit_lower (by positivity) hL
  apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL.le
  simpa only [show 2 ^ 4 = (16 : ℕ) by norm_num, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-- **`thm:diagonal`, two qubits, `n_res` with Choi infidelity and free shared
randomness.** For almost every diagonal two-qubit gate there is a threshold below
which every LOSCC protocol with free shared randomness, at most `q` initial
resource qubits in every branch and score deficit `ε` has
`q ≥ (1/5) log₂ ln(1/ε) - B`. -/
theorem exists_ae_sharedRandomLOSCCTwoQubitDiagonal_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ φ ∂rectangularPhaseMeasure 2 2,
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin 2) (Fin 2)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin 2) (Fin 2)),
          (∀ᵐ a ∂μ, Fintype.card (ρA a) * Fintype.card (ρB a) ≤ 2 ^ q ∧
            Fintype.card (μA a) = 1 ∧ Fintype.card (μB a) = 1) →
          (AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
            1 - ε ≤ scoreU (rectangularDiagonalPhase φ)
              (StandardBorelClassicalProtocol.sharedRandomOperationalChannel μ P).toLinearMap →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : α → ℕ) (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
            AEStronglyMeasurable (StandardBorelClassicalProtocol.mixedBranchOperation P m) μ →
            1 - ε ≤ scoreU (rectangularDiagonalPhase φ)
              (StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel μ P m).toLinearMap →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_twoQubitDiagonal_resource_constant
  refine ⟨max 0 ((1 / 5 : ℝ) * Real.logb 2 (256 / c ^ 2)), le_max_left _ _, ?_⟩
  filter_upwards [hae] with φ hφ
  obtain ⟨ε₀, hε₀, hε₀half, hcharged⟩ := hφ
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro q ε hε hsmall α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hcap
  have hε1 : ε < 1 := by linarith
  refine ⟨fun hP hs => ?_, fun n m hP hs => ?_⟩
  · have hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasQuantumFootprint_of_loscc ha.1 ha.2.1 ha.2.2
    exact loscc_qubit_lower_of_charged hc hε hε1 ((hcharged _ ε hε hsmall).1
      (StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint
        μ P hP (rectangularDiagonalPhaseUnitary φ) (by decide) hK hs))
  · have hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasMixedQuantumFootprint_of_loscc (m a) ha.1 ha.2.1 ha.2.2
    exact loscc_qubit_lower_of_charged hc hε hε1 ((hcharged _ ε hε hsmall).1
      (StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint
        μ P m hP (rectangularDiagonalPhaseUnitary φ) (by decide) hK hs))

/-- **`rem:two-qubit`, `n_res`.** For Haar-almost every two-qubit unitary there
is a threshold below which every LOSCC protocol with free shared randomness, at
most `q` initial resource qubits in every branch and normalized diamond error
`ε` has `q ≥ (1/5) log₂ ln(1/ε) - B`. -/
theorem exists_ae_sharedRandomLOSCCTwoQubit_qubit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ (T : unitaryGroup (Fin 2 × Fin 2) ℂ) ∂unitaryHaar (Fin 2 × Fin 2),
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (q : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ∀ (α : Type u₉) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
            (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
            (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
            [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)]
            [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
            [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
            [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
            [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
            [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
            [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
            [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)]
            (P : ∀ a, StandardBorelClassicalProtocol (Fin 2) (Fin 2)
              (ρA a) (ρB a) (κA a) (κB a) (μA a) (μB a) (σA a) (σB a) (Fin 2) (Fin 2)),
          (∀ᵐ a ∂μ, Fintype.card (ρA a) * Fintype.card (ρB a) ≤ 2 ^ q ∧
            Fintype.card (μA a) = 1 ∧ Fintype.card (μB a) = 1) →
          (AEStronglyMeasurable (fun a => (P a).operationalChannel) μ →
            diamondError (StandardBorelClassicalProtocol.sharedRandomOperationalChannel μ P).toLinearMap
              (adConj (T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) ∧
          (∀ (n : α → ℕ) (m : ∀ a, MixedResource (ρA a) (ρB a) (n a)),
            AEStronglyMeasurable (StandardBorelClassicalProtocol.mixedBranchOperation P m) μ →
            diamondError
                (StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel μ P m).toLinearMap
              (adConj (T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ ε →
            (1 / 5 : ℝ) * Real.logb 2 (Real.log (1 / ε)) - B ≤ (q : ℝ)) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0}
    (DirectVolume.polynomialImageVolumeBound)
  refine ⟨max 0 ((1 / 5 : ℝ) * Real.logb 2 (256 / (2 * c) ^ 2)), le_max_left _ _, ?_⟩
  filter_upwards [hae 2 le_rfl] with T hT
  obtain ⟨ε₀, hε₀, hε₀half, hcharged⟩ := hT
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro q ε hε hsmall α _ μ _ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P hcap
  have hε1 : ε < 1 := by linarith
  have hconv (h : c * ((2 : ℕ) : ℝ) * Real.sqrt (Real.log (1 / ε)) ≤
      ((2 ^ 4 * Nat.sqrt (2 ^ q) ^ 5 : ℕ) : ℝ)) :
      (2 * c) * Real.sqrt (Real.log (1 / ε)) ≤ ((2 ^ 4 * Nat.sqrt (2 ^ q) ^ 5 : ℕ) : ℝ) := by
    have : c * ((2 : ℕ) : ℝ) * Real.sqrt (Real.log (1 / ε)) =
        (2 * c) * Real.sqrt (Real.log (1 / ε)) := by push_cast; ring
    rw [← this]; exact h
  refine ⟨fun hP he => ?_, fun n m hP he => ?_⟩
  · have hK : ∀ᵐ a ∂μ, (P a).HasQuantumFootprint (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasQuantumFootprint_of_loscc ha.1 ha.2.1 ha.2.2
    exact loscc_qubit_lower_of_charged (by positivity) hε hε1 (hconv ((hcharged _ ε hε hsmall).1
      (StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError
        μ P hP T (by decide) hK he)))
  · have hK : ∀ᵐ a ∂μ, (P a).HasMixedQuantumFootprint (m a) (Nat.sqrt (2 ^ q)) :=
      hcap.mono fun a ha => (P a).hasMixedQuantumFootprint_of_loscc (m a) ha.1 ha.2.1 ha.2.2
    exact loscc_qubit_lower_of_charged (by positivity) hε hε1 (hconv ((hcharged _ ε hε hsmall).1
      (StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError
        μ P m hP T (by decide) hK he)))

end

end NLQCLean
