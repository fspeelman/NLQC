import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Models.ClassicalCommunication.FiniteLocalization
import NLQCLean.Bounds.AlmostEveryExact
import NLQCLean.Bounds.ArbitraryFiniteClassicalAlmostEvery
import NLQCLean.Approx.FiniteClassicalSpectralFloors

/-!
# Exact and robust finite localization

Actual finite local POVMs and their joint reporting function induce the
two-sided classical protocol constructed in the model leaf. Quantum messages
are one-dimensional, so its quantum budget is the resource Schmidt rank.
Exact Haar nullity and the quantitative conclusions are unconditional.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix MeasureTheory
open scoped ENNReal

universe u₁ u₂ u₃ u₄

/-- No actual finite POVMs and reporting function localize this target
exactly, for pure resources, common-map mixtures, or arbitrary density matrices. -/
def NoFiniteExactLocalization (T : unitaryGroup (Fin d × Fin d) ℂ) : Prop :=
  ∀ (ρA : Type u₁) (ρB : Type u₂) (σA : Type u₃) (σB : Type u₄),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype σA] [Fintype σB],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq σA] [DecidableEq σB],
  ∀ L : FiniteLocalizationScheme (Fin d) (Fin d) ρA ρB σA σB (Fin d × Fin d),
  (∀ γ : ρA × ρB → ℂ, IsUnitVector γ →
    ¬ L.IsExact γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ∧
  (∀ (n : ℕ) (m : MixedResource ρA ρB n),
    ¬ L.IsMixedExact m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ∧
  (∀ S : Matrix (ρA × ρB) (ρA × ρB) ℂ, IsState S →
    ¬ L.IsStateExact S (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))

/-- The finite-outcome exact localization corollary (`cor:localizable`)
is unconditional and covers every finite shared density matrix. -/
theorem ae_no_finite_exact_localization (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      NoFiniteExactLocalization.{u₁, u₂, u₃, u₄} T := by
  let : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  filter_upwards [ae_not_mem_reachable_zero d hd] with T hT
  have hM : IsIsometry (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp T.property
  intro ρA ρB σA σB _ _ _ _ _ _ _ _ L
  have hpure : ∀ γ : ρA × ρB → ℂ, IsUnitVector γ →
      ¬ L.IsExact γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    intro γ hγ hex
    let P := L.protocol γ hγ
    have hscore : scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        P.operationalChannel = 1 := scorePVM_eq_one_of_twoSidedExactChannel hM
      (L.protocol_twoSidedExactChannel_of_isExact γ hγ _ hex)
    have hreach := P.mem_purePVMReachable_of_quantumFootprint (ε := 0) T hd0
      ((L.protocol_hasQuantumFootprint_iff γ hγ (schmidtRank γ)).mpr le_rfl)
      (by simpa only [sub_zero, hscore] using (le_refl (1 : ℝ)))
    exact (hT _).2.2.1 hreach
  have hmixed : ∀ (n : ℕ) (m : MixedResource ρA ρB n),
      ¬ L.IsMixedExact m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    intro n m hex
    let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
    let γ := m.component k
    have hγ := m.component_unit k
    let P := L.protocol γ hγ
    have hr : m.schmidtNumberLE (Fintype.card ρA) :=
      fun j => schmidtRank_le_card_left (m.component j)
    have hscore : scorePVM (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        (P.mixedOperationalChannel m) = 1 := scorePVM_eq_one_of_twoSidedExactChannel hM
      (L.protocol_twoSidedExactChannel_of_isMixedExact γ hγ m _ hex)
    have hreach := P.mem_purePVMReachable_of_mixedQuantumFootprint (ε := 0) m T hd0
      ((L.protocol_hasMixedQuantumFootprint_iff γ hγ m (Fintype.card ρA)).mpr hr)
      (by simpa only [sub_zero, hscore] using (le_refl (1 : ℝ)))
    exact (hT _).2.2.1 hreach
  refine ⟨hpure, hmixed, ?_⟩
  intro S hS hex
  apply hmixed _ (MixedResource.ofState S hS)
  intro X hX i
  rw [← L.stateReportedProbability_densityMatrix, MixedResource.densityMatrix_ofState]
  exact hex X hX i

/-- Exact finite localization is Haar-null without a quantitative geometry premise. -/
theorem finite_exact_localization_haar_null (d : ℕ) (hd : 2 ≤ d) :
    (unitaryHaar (Fin d × Fin d)).toOuterMeasure
      {T | ¬ NoFiniteExactLocalization.{u₁, u₂, u₃, u₄} T} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  exact (ae_no_finite_exact_localization d hd).mono fun _ h => not_not_intro h

/-- Every original finite localization architecture has success strictly
below the stated accuracy level at this fixed resource rank cap. -/
def AllFiniteLocalizationScoresBelow (T : unitaryGroup (Fin d × Fin d) ℂ)
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ (ρA : Type u₁) (ρB : Type u₂) (σA : Type u₃) (σB : Type u₄),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype σA] [Fintype σB],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq σA] [DecidableEq σB],
  ∀ L : FiniteLocalizationScheme (Fin d) (Fin d) ρA ρB σA σB (Fin d × Fin d),
  (∀ γ : ρA × ρB → ℂ, IsUnitVector γ → schmidtRank γ ≤ r →
    L.successScore γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε) ∧
  (∀ (n : ℕ) (m : MixedResource ρA ρB n), m.schmidtNumberLE r →
    L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε) ∧
  (∀ S : Matrix (ρA × ρB) (ρA × ρB) ℂ, IsState S →
    MixedResource.HasSchmidtNumberLE S r →
    L.stateSuccessScore S (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε)

/-- A target belongs when some actual finite localization scheme attains
success at least `1-ε`. All original finite systems are quantified directly. -/
def finiteLocalizationReachable (d r : ℕ) (ε : ℝ) :
    Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  {T | ¬ AllFiniteLocalizationScoresBelow.{u₁, u₂, u₃, u₄} T r ε}

/-- Rank-only localization enters the charged PVM score class through the
proved finite classical compression, retaining all classical charges there. -/
theorem finiteLocalizationReachable_subset_purePVMReachable
    {d : ℕ} (hd : 0 < d) (r : ℕ) (ε : ℝ) :
    finiteLocalizationReachable.{u₁, u₂, u₃, u₄} d r ε ⊆
      purePVMReachable d (d ^ 4 * r ^ 5) ε := by
  intro T hT
  by_contra hnot
  apply hT
  intro ρA ρB σA σB _ _ _ _ _ _ _ _ L
  have hpure : ∀ γ : ρA × ρB → ℂ, IsUnitVector γ → schmidtRank γ ≤ r →
      L.successScore γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε := by
    intro γ hγ hr
    by_contra hscore
    apply hnot
    let P := L.protocol γ hγ
    apply P.mem_purePVMReachable_of_quantumFootprint T hd
      ((L.protocol_hasQuantumFootprint_iff γ hγ r).mpr hr)
    rw [L.protocol_scorePVM]
    exact le_of_not_gt hscore
  have hmixed : ∀ (n : ℕ) (m : MixedResource ρA ρB n), m.schmidtNumberLE r →
      L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) < 1 - ε := by
    intro n m hr
    by_contra hscore
    apply hnot
    let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
    let P := L.protocol (m.component k) (m.component_unit k)
    apply P.mem_purePVMReachable_of_mixedQuantumFootprint m T hd
      ((L.protocol_hasMixedQuantumFootprint_iff (m.component k) (m.component_unit k) m r).mpr hr)
    rw [L.protocol_mixedScorePVM]
    exact le_of_not_gt hscore
  refine ⟨hpure, hmixed, ?_⟩
  intro S _ hcap
  obtain ⟨n, m, hS, hr⟩ := hcap
  rw [← hS, L.stateSuccessScore_densityMatrix]
  exact hmixed n m hr

/-- The full-group outer-measure bound for finite localization. The class
need not be measurable; the PVM codimension and error normalization remain
those of the ordered joint-label score. -/
theorem exists_finite_localization_haar_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d r : ℕ), 2 ≤ d → 1 ≤ r →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure
            (finiteLocalizationReachable.{u₁, u₂, u₃, u₄} d r ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (r : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d r hd hr ε hε hεhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hr
  have h := (hbound d (d ^ 4 * r ^ 5) hd hone hquarter ε hε hεhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact (measure_mono (finiteLocalizationReachable_subset_purePVMReachable
    (by omega : 0 < d) r ε)).trans h

/-- The outer-measure localization theorem. -/
theorem exists_finite_localization_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d r : ℕ), 2 ≤ d → 1 ≤ r →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure
            (finiteLocalizationReachable.{u₁, u₂, u₃, u₄} d r ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (r : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) :=
  exists_finite_localization_haar_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- The literal tenth-root form of the finite classical logarithm rate. -/
theorem localization_rank_rate_of_log_bound {C L : ℝ} {d r : ℕ}
    (hC : 0 < C) (hd : 0 < d) (hL : 0 ≤ L)
    (hbound : L ≤ C * (d : ℝ) ^ 6 * (r : ℝ) ^ 10) :
    C ^ (-(1 / 10 : ℝ)) * (d : ℝ) ^ (-(3 / 5 : ℝ)) * L ^ (1 / 10 : ℝ) ≤ r := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot := Real.rpow_le_rpow hL hbound (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hD : ((d : ℝ) ^ 6) ^ (1 / 10 : ℝ) = (d : ℝ) ^ (3 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdR.le]
    norm_num
  have hr : ((r : ℝ) ^ 10) ^ (1 / 10 : ℝ) = r := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg r) (by decide : (10 : ℕ) ≠ 0)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hC.le (by positivity), hD, hr] at hroot
  have hCC : C ^ (-(1 / 10 : ℝ)) * C ^ (1 / 10 : ℝ) = 1 := by
    rw [← Real.rpow_add hC]
    norm_num
  have hDD : (d : ℝ) ^ (-(3 / 5 : ℝ)) * (d : ℝ) ^ (3 / 5 : ℝ) = 1 := by
    rw [← Real.rpow_add hdR]
    norm_num
  calc
    _ ≤ C ^ (-(1 / 10 : ℝ)) * (d : ℝ) ^ (-(3 / 5 : ℝ)) *
        (C ^ (1 / 10 : ℝ) * (d : ℝ) ^ (3 / 5 : ℝ) * r) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (C ^ (-(1 / 10 : ℝ)) * C ^ (1 / 10 : ℝ)) *
        ((d : ℝ) ^ (-(3 / 5 : ℝ)) * (d : ℝ) ^ (3 / 5 : ℝ)) * r := by ring
    _ = r := by rw [hCC, hDD]; ring

/-- The source localization lower bound, including its full dimension floor. -/
def LocalizationRankLowerBound (d r : ℕ) (ε c : ℝ) : Prop :=
  max (d : ℝ) (c * (d : ℝ) ^ (-(3 / 5 : ℝ)) *
    (Real.log (1 / ε)) ^ (1 / 10 : ℝ)) ≤ r

/-- A fixed target's rank bound for every actual finite architecture,
with pure resources, common-map mixtures, and density-matrix Schmidt number. -/
def AllFiniteLocalizationRankBounds (T : unitaryGroup (Fin d × Fin d) ℂ)
    (ε c : ℝ) : Prop :=
  ∀ (ρA : Type u₁) (ρB : Type u₂) (σA : Type u₃) (σB : Type u₄),
  ∀ [Fintype ρA] [Fintype ρB] [Fintype σA] [Fintype σB],
  ∀ [DecidableEq ρA] [DecidableEq ρB] [DecidableEq σA] [DecidableEq σB],
  ∀ L : FiniteLocalizationScheme (Fin d) (Fin d) ρA ρB σA σB (Fin d × Fin d),
  (∀ (γ : ρA × ρB → ℂ), IsUnitVector γ → ∀ r : ℕ, schmidtRank γ ≤ r →
    1 - ε ≤ L.successScore γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
    LocalizationRankLowerBound d r ε c) ∧
  (∀ (n : ℕ) (m : MixedResource ρA ρB n) (r : ℕ), m.schmidtNumberLE r →
    1 - ε ≤ L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
    LocalizationRankLowerBound d r ε c) ∧
  (∀ (S : Matrix (ρA × ρB) (ρA × ρB) ℂ), IsState S → ∀ r : ℕ,
    MixedResource.HasSchmidtNumberLE S r →
    1 - ε ≤ L.stateSuccessScore S (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
    LocalizationRankLowerBound d r ε c)

/-- The finite-outcome restriction of `cor:localization`, with one universal
constant and a fixed-target threshold preceding every resource rank and
original outcome/register architecture. -/
theorem exists_ae_finite_localization_rank_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        AllFiniteLocalizationRankBounds.{u₁, u₂, u₃, u₄} T ε c := by
  obtain ⟨C, hC, hrate⟩ :=
    exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound.{u₁, u₂, u₁, u₂, 0, 0, u₃, u₄, 0, 0, u₁, u₂}
      hGeom
  refine ⟨C ^ (-(1 / 10 : ℝ)), by positivity, ?_⟩
  intro d hd
  let : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  filter_upwards [hrate d hd, ae_pvm_pos_uniform_schmidtWeight_lower_bound d]
    with T hRate hWeights
  obtain ⟨εRate, hRatepos, hRatehalf, hlog⟩ := hRate
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
      (hprec : Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (r : ℝ) ^ 10) :
      LocalizationRankLowerBound d r ε (C ^ (-(1 / 10 : ℝ))) := by
    apply max_le
    · exact_mod_cast hfloor
    · exact localization_rank_rate_of_log_bound hC hd0 hL hprec
  intro ρA ρB σA σB _ _ _ _ _ _ _ _ L
  have hpure : ∀ γ : ρA × ρB → ℂ, IsUnitVector γ → ∀ r : ℕ, schmidtRank γ ≤ r →
      1 - ε ≤ L.successScore γ (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
      LocalizationRankLowerBound d r ε (C ^ (-(1 / 10 : ℝ))) := by
    intro γ hγ r hr hs
    let P := L.protocol γ hγ
    have hK := (L.protocol_hasQuantumFootprint_iff γ hγ r).mpr hr
    have hscore : 1 - ε ≤ scorePVM
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel := by
      change 1 - ε ≤ scorePVM
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (L.protocol γ hγ).operationalChannel
      rw [L.protocol_scorePVM]
      exact hs
    have hfloor : d ≤ r := by
      simpa only [Fintype.card_fin] using P.pvm_full_spectral_floor
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hM hK hw hεt hscore
    have hprecision := ((hlog r ε hε hεRate ρA ρB (Fin d × ρA) (Fin d × ρB)
      Unit Unit σA σB Unit Unit (Fin d × ρA) (Fin d × ρB)).2 P).1 hK (Or.inl hscore)
    exact hcombine r hfloor hprecision
  have hmixed : ∀ (n : ℕ) (m : MixedResource ρA ρB n) (r : ℕ), m.schmidtNumberLE r →
      1 - ε ≤ L.mixedSuccessScore m (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) →
      LocalizationRankLowerBound d r ε (C ^ (-(1 / 10 : ℝ))) := by
    intro n m r hr hs
    let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
    let P := L.protocol (m.component k) (m.component_unit k)
    have hK := (L.protocol_hasMixedQuantumFootprint_iff
      (m.component k) (m.component_unit k) m r).mpr hr
    have hscore : 1 - ε ≤ scorePVM
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (P.mixedOperationalChannel m) := by
      change 1 - ε ≤ scorePVM
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        ((L.protocol (m.component k) (m.component_unit k)).mixedOperationalChannel m)
      rw [L.protocol_mixedScorePVM]
      exact hs
    have hfloor : d ≤ r := by
      simpa only [Fintype.card_fin] using P.mixed_pvm_full_spectral_floor m
        (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hM hK hw hεt hscore
    have hprecision := ((hlog r ε hε hεRate ρA ρB (Fin d × ρA) (Fin d × ρB)
      Unit Unit σA σB Unit Unit (Fin d × ρA) (Fin d × ρB)).2 P).2 n m hK (Or.inl hscore)
    exact hcombine r hfloor hprecision
  refine ⟨hpure, hmixed, ?_⟩
  intro S _ r hcap hs
  obtain ⟨n, m, hS, hr⟩ := hcap
  apply hmixed n m r hr
  simpa only [← hS, L.stateSuccessScore_densityMatrix] using hs

/-- The finite localization maximum bound retains exactly the three
existing explicit external geometric arguments. -/
theorem exists_ae_finite_localization_rank_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        AllFiniteLocalizationRankBounds.{u₁, u₂, u₃, u₄} T ε c :=
  exists_ae_finite_localization_rank_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication
