import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Models.ClassicalCommunication.BorelLocalization
import NLQCLean.Bounds.FiniteLocalization
import NLQCLean.Approx.BorelClassicalSpectralFloors

/-!
# Approximate localization with standard-Borel outcomes

Localizations by local POVMs with outcomes in standard Borel spaces and a
measurable reporting function (`cor:localization`). The broadcast protocol is
an actual standard-Borel protocol with one-dimensional quantum messages, so
its quantum footprint is the resource Schmidt rank, and its PVM score is the
Born success probability. The Haar outer-measure bound and the almost-every
rank bound `r ≥ max(d, c d^{-3/5} log(1/ε)^{1/10})` follow, for pure and
common-map mixed resources.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix MeasureTheory
open scoped ENNReal

universe u₁ u₂ u₃ u₄ u₅

/-- Every standard-Borel localization scheme has success strictly below
`1 - ε` at this resource rank cap. -/
def AllBorelLocalizationScoresBelow {d : ℕ} (T : unitaryGroup (Fin d × Fin d) ℂ)
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ [NeZero d], ∀ (ρA : Type u₁) (ρB : Type u₂) (σA : Type u₃) (σB : Type u₄) (ω : Type u₅),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype ω],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ω] [Unique ω],
  ∀ [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB],
  ∀ L : BorelLocalizationScheme (Fin d) (Fin d) ρA ρB σA σB (Fin d × Fin d) ω,
  (∀ (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ), schmidtRank γ ≤ r →
    L.successScore γ hγ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε) ∧
  (∀ (n : ℕ) (m : MixedResource ρA ρB n), m.schmidtNumberLE r →
    L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε)

/-- Targets with a standard-Borel localization of success at least `1 - ε`. -/
def borelLocalizationReachable (d r : ℕ) (ε : ℝ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  {T | ¬ AllBorelLocalizationScoresBelow.{u₁, u₂, u₃, u₄, u₅} T r ε}

/-- Standard-Borel localization enters the charged PVM score class through the
proved Borel classical compression. -/
theorem borelLocalizationReachable_subset_purePVMReachable
    {d : ℕ} (hd : 0 < d) (r : ℕ) (ε : ℝ) :
    borelLocalizationReachable.{u₁, u₂, u₃, u₄, u₅} d r ε ⊆
      purePVMReachable d (d ^ 4 * r ^ 5) ε := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro T hT
  by_contra hnot
  apply hT
  intro _ ρA ρB σA σB ω _ _ _ _ _ _ _ _ _ _ _ L
  refine ⟨fun γ hγ hr => ?_, fun n m hr => ?_⟩
  · by_contra hscore
    apply hnot
    apply (L.protocol γ hγ).mem_purePVMReachable_of_quantumFootprint T hd
      ((L.protocol_hasQuantumFootprint_iff γ hγ r).mpr hr)
    rw [L.protocol_scorePVM]
    exact le_of_not_gt hscore
  · by_contra hscore
    apply hnot
    let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
    let P := L.protocol (m.component k) (m.component_unit k)
    apply P.mem_purePVMReachable_of_mixedQuantumFootprint m T hd
      ((L.protocol_hasMixedQuantumFootprint_iff (m.component k) (m.component_unit k) m r).mpr hr)
    rw [L.protocol_mixedScorePVM]
    exact le_of_not_gt hscore

/-- `cor:localization`, outer-measure part, with standard-Borel outcomes. -/
theorem exists_borel_localization_haar_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d r : ℕ), 2 ≤ d → 1 ≤ r →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure
            (borelLocalizationReachable.{u₁, u₂, u₃, u₄, u₅} d r ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (r : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d r hd hr ε hε hεhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hr
  have h := (hbound d (d ^ 4 * r ^ 5) hd hone hquarter ε hε hεhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact (measure_mono (borelLocalizationReachable_subset_purePVMReachable
    (by omega : 0 < d) r ε)).trans h

/-- The standard-Borel localization rank bound for one fixed target. -/
def AllBorelLocalizationRankBounds {d : ℕ} (T : unitaryGroup (Fin d × Fin d) ℂ)
    (ε c : ℝ) : Prop :=
  ∀ [NeZero d], ∀ (ρA : Type u₁) (ρB : Type u₂) (σA : Type u₃) (σB : Type u₄) (ω : Type u₅),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype ω],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ω] [Unique ω],
  ∀ [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB],
  ∀ L : BorelLocalizationScheme (Fin d) (Fin d) ρA ρB σA σB (Fin d × Fin d) ω,
  (∀ (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) (r : ℕ), schmidtRank γ ≤ r →
    1 - ε ≤ L.successScore γ hγ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
    LocalizationRankLowerBound d r ε c) ∧
  (∀ (n : ℕ) (m : MixedResource ρA ρB n) (r : ℕ), m.schmidtNumberLE r →
    1 - ε ≤ L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
    LocalizationRankLowerBound d r ε c)

/-- **`cor:localization` with standard-Borel outcomes.** One universal constant;
for almost every PVM a threshold below which every standard-Borel localization
with failure probability `ε` uses Schmidt number
`r ≥ max(d, c d^{-3/5} log(1/ε)^{1/10})`. -/
theorem exists_ae_borel_localization_rank_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        AllBorelLocalizationRankBounds.{u₁, u₂, u₃, u₄, u₅} T ε c := by
  obtain ⟨c₀, hc₀, hrate⟩ := exists_ae_pvm_resource_constant_of_imageVolumeBound hGeom
  let C : ℝ := 1 / c₀ ^ 2
  have hC : 0 < C := by positivity
  refine ⟨C ^ (-(1 / 10 : ℝ)), by positivity, ?_⟩
  intro d hd
  let : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  filter_upwards [hrate d hd, ae_pvm_pos_uniform_schmidtWeight_lower_bound d]
    with T hRate hWeights
  obtain ⟨εRate, hRatepos, hRatehalf, hcharged⟩ := hRate
  obtain ⟨t, ht, hw⟩ := hWeights
  refine ⟨min εRate (t / 2), lt_min hRatepos (by positivity),
    (min_le_left _ _).trans hRatehalf, ?_⟩
  intro ε hε hsmall
  have hεRate := hsmall.trans (min_le_left εRate (t / 2))
  have hεt : ε < t := lt_of_le_of_lt (hsmall.trans (min_le_right _ _)) (by linarith)
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith [hεRate]))
  have hM : IsIsometry (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp T.property
  have hcombine (r : ℕ) (hfloor : d ≤ r)
      (hreach : T ∈ purePVMReachable d (d ^ 4 * r ^ 5) ε) :
      LocalizationRankLowerBound d r ε (C ^ (-(1 / 10 : ℝ))) := by
    apply max_le
    · exact_mod_cast hfloor
    · apply localization_rank_rate_of_log_bound hC hd0 hL
      apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc₀ hd0 hL
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (hcharged (d ^ 4 * r ^ 5) ε hε hεRate).1 hreach
  intro _ ρA ρB σA σB ω _ _ _ _ _ _ _ _ _ _ _ L
  refine ⟨fun γ hγ r hr hs => ?_, fun n m r hr hs => ?_⟩
  · let P := L.protocol γ hγ
    have hK := (L.protocol_hasQuantumFootprint_iff γ hγ r).mpr hr
    have hscore : 1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        P.operationalChannel.toLinearMap := by
      rwa [L.protocol_scorePVM]
    have hfloor : d ≤ r := by
      simpa only [Fintype.card_fin] using P.pvm_full_spectral_floor
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hM hK hw hεt hscore
    exact hcombine r hfloor (P.mem_purePVMReachable_of_quantumFootprint T hd0 hK hscore)
  · let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
    let P := L.protocol (m.component k) (m.component_unit k)
    have hK := (L.protocol_hasMixedQuantumFootprint_iff
      (m.component k) (m.component_unit k) m r).mpr hr
    have hscore : 1 - ε ≤ scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        (P.mixedOperationalChannel m) := by
      rwa [L.protocol_mixedScorePVM]
    have hfloor : d ≤ r := by
      simpa only [Fintype.card_fin] using P.mixed_pvm_full_spectral_floor m
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hM hK hw hεt hscore
    exact hcombine r hfloor (P.mem_purePVMReachable_of_mixedQuantumFootprint m T hd0 hK hscore)

/-- `cor:localization` with standard-Borel outcomes, outer-measure part. -/
theorem exists_borel_localization_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d r : ℕ), 2 ≤ d → 1 ≤ r →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure
            (borelLocalizationReachable.{u₁, u₂, u₃, u₄, u₅} d r ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (r : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) :=
  exists_borel_localization_haar_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- `cor:localization` with standard-Borel outcomes, rank part. -/
theorem exists_ae_borel_localization_rank_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        AllBorelLocalizationRankBounds.{u₁, u₂, u₃, u₄, u₅} T ε c :=
  exists_ae_borel_localization_rank_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication
