import NLQCLean.Bounds.PVMAlmostEveryTargets
import NLQCLean.Bounds.DiamondConditional
import NLQCLean.Bounds.PVMTVHaarConditional
import NLQCLean.Models.ProjectiveProtocolScore
import NLQCLean.Models.ProjectiveMixedExactness

/-!
# Almost-every fixed-target resource bounds for all small errors

From the common conull set: one universal `c`, then for almost every target a
threshold `e₀ ∈ (0, 1/2]` depending on `d` and the target only, valid for every
budget `K ≥ 0` and every real `0 < e ≤ e₀`. Diamond and joint-TV statements use
the proved inclusions into the score sets; no measurability of those sets is
claimed. Physical statements quantify arbitrary finite original registers.
The single geometric property stays explicit.

The exact-implementation conclusions are derived from an almost-every
zero-reachability statement given as an argument
(`ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable` and
`ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable`). Here that
statement comes from the geometric property; `NLQCLean.Bounds.AlmostEveryExact`
supplies it without any geometric input.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory

/-- Resource rates and Unitary diamond resource rate/TV together: one constant and, for almost every fixed target,
one threshold serving all eight reachable sets. -/
theorem exists_ae_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨A, hA, hae⟩ := exists_ae_forbidden_error_constant hGeom
  have hA0 : 0 < A := by linarith
  refine ⟨1 / Real.sqrt A, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  filter_upwards [hae d hd] with T hT
  obtain ⟨K₀, -, hT⟩ := hT
  obtain ⟨K₁, hK₀₁, hK₁⟩ : ∃ K₁ : ℕ, K₀ ≤ K₁ ∧ d ^ 2 ≤ K₁ :=
    ⟨max K₀ (d ^ 2), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨he₀, he₀'⟩ := forbiddenError_threshold_mem hA (by omega : 1 ≤ d) hK₁
  refine ⟨_, he₀, he₀', fun K e _he hee => ?_⟩
  have hforb (K' : ℕ) (hK' : K₁ ≤ K') := hT K' (hK₀₁.trans hK')
  have key : ∀ {R : ℕ → ℝ → Set (unitaryGroup (Fin d × Fin d) ℂ)},
      (∀ {K K' : ℕ} {e e' : ℝ}, K ≤ K' → e ≤ e' → R K e ⊆ R K' e') →
      (∀ K' : ℕ, K₁ ≤ K' → T ∉ R K' (Real.exp (-(A * (K' : ℝ) ^ 2 / (d : ℝ) ^ 2)))) →
      T ∈ R K e → 1 / Real.sqrt A * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K :=
    fun hmono hf hx => resource_lower_of_forbiddenError hmono hA0 hd0 hf hee hx
  have hpU := key (R := pureReachable d) pureReachable_mono fun K' hK' => (hforb K' hK').1
  have hmU := key (R := mixedReachable d) mixedReachable_mono fun K' hK' => (hforb K' hK').2.1
  have hpP := key (R := purePVMReachable d) purePVMReachable_mono
    fun K' hK' => (hforb K' hK').2.2.1
  have hmP := key (R := mixedPVMReachable d) mixedPVMReachable_mono
    fun K' hK' => (hforb K' hK').2.2.2
  exact ⟨hpU, hmU, hpP, hmP,
    fun h => hpU (pureDiamondReachable_subset_pureReachable K e h),
    fun h => hmU (mixedDiamondReachable_subset_mixedReachable K e h),
    fun h => hpP (purePVMTVReachable_subset_purePVMReachable K e h),
    fun h => hmP (mixedPVMTVReachable_subset_mixedPVMReachable K e h)⟩

/-- Unitary score resource rate: almost every fixed unitary, pure and finite mixed score reachability. -/
theorem exists_ae_unitary_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_resource_constant.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K e he he' => ⟨(hT K e he he').1, (hT K e he he').2.1⟩⟩

/-- Unitary diamond resource rate: the same target and threshold for normalized diamond error. -/
theorem exists_ae_diamond_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K e he he' => ⟨(hT K e he he').2.2.2.2.1, (hT K e he he').2.2.2.2.2.1⟩⟩

/-- PVM score resource rate: almost every fixed basis lift, pure and finite mixed PVM score reachability. -/
theorem exists_ae_pvm_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMReachable d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_resource_constant.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K e he he' => ⟨(hT K e he he').2.2.1, (hT K e he he').2.2.2.1⟩⟩

/-- PVM joint-TV resource rate: the same basis lift and threshold for worst-case joint TV. -/
theorem exists_ae_pvm_tv_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
          c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K e he he' =>
    ⟨(hT K e he he').2.2.2.2.2.2.1, (hT K e he he').2.2.2.2.2.2.2⟩⟩

/-- Physical resource rates, unitary: every arbitrary-register pure protocol, and every finite mixed
resource with common local maps, of footprint at most `K` and score error or
normalized diamond error at most `e ≤ e₀`, obeys the bound. -/
theorem exists_ae_unitary_physical_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        ∀ (ρA ρB κA κB μA μB εA εB : Type*)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
            P.HasFootprint K →
            (1 - e ≤ scoreU (T : Matrix _ _ ℂ) P.operationalChannel ∨
              diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ)) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n)
            (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
            (DA : Matrix (Fin d × εA) (κA × μB) ℂ) (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
            IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
            ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
            (1 - e ≤ scoreU (T : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
              diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ)) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_unitary_resource_constant hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  have : NeZero d := ⟨by omega⟩
  have hU := Matrix.mem_unitaryGroup_iff'.mp T.2
  refine ⟨e₀, h0, h1, fun K e he he' ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_⟩⟩
  · intro P hP hs
    exact (hT K e he he').1
      (P.mem_pureReachable hP (hs.elim id (P.scoreU_ge_of_diamondError_le hU)))
  · intro n m VA VB DA DB hVA hVB hDA hDB R hR hK hs
    exact (hT K e he he').2 (m.mem_mixedReachable VA VB DA DB hVA hVB hDA hDB hR hK
      (hs.elim id (m.scoreU_ge_of_diamondError_le hVA hVB hDA hDB hU)))

/-- Physical resource rates, PVM: every arbitrary-register pure protocol, and every finite mixed resource
with common local maps, of footprint at most `K` and PVM score error or worst-case
joint-TV error at most `e ≤ e₀`, obeys the bound. -/
theorem exists_ae_pvm_physical_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ)
      ∂unitaryHaar (Fin d × Fin d),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
        ∀ (ρA ρB κA κB μA μB εA εB : Type*)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
          (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
              (Fin d × Fin d) (Fin d × Fin d) εA εB,
            P.HasFootprint K →
            (1 - e ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel ∨
              pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (∀ (n : ℕ) (m : MixedResource ρA ρB n)
            (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
            (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
            (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
            IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
            ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
            (1 - e ≤ scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
              pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ≤ e) →
            c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_pvm_resource_constant hGeom
  refine ⟨c, hc, fun d hd => ?_⟩
  have : NeZero d := ⟨by omega⟩
  refine (h d hd).mono fun M hM => ?_
  obtain ⟨e₀, h0, h1, hM⟩ := hM
  have hU := Matrix.mem_unitaryGroup_iff'.mp M.2
  refine ⟨e₀, h0, h1, fun K e he he' ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_⟩⟩
  · intro P hP hs
    have hb := P.one_sub_scorePVM_le_pvmTVError hU
    exact (hM K e he he').1 (P.mem_purePVMReachable hP (hs.elim id fun ht => by linarith))
  · intro n m VA VB DA DB hVA hVB hDA hDB R hR hK hs
    have hb := m.one_sub_scorePVM_le_pvmTVError hVA hVB hDA hDB hU
    exact (hM K e he he').1 (m.mem_purePVMReachable VA VB DA DB hVA hVB hDA hDB hR hK
      (hs.elim id fun ht => by linarith))

/-- AF4 core: on the AF1 good set no finite budget reaches score error zero. -/
theorem ae_not_mem_reachable_zero (hGeom : PolynomialImageVolumeBound) :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      T ∉ purePVMReachable d K 0 ∧ T ∉ mixedPVMReachable d K 0 := by
  obtain ⟨A, _hA, hae⟩ := exists_ae_forbidden_error_constant hGeom
  intro d hd
  filter_upwards [hae d hd] with T hT
  obtain ⟨K₀, -, hT⟩ := hT
  intro K
  have hJ := hT (max K K₀) (le_max_right _ _)
  have h0 := (Real.exp_pos (-(A * ((max K K₀ : ℕ) : ℝ) ^ 2 / (d : ℝ) ^ 2))).le
  exact ⟨fun h => hJ.1 (pureReachable_mono (le_max_left _ _) h0 h),
    fun h => hJ.2.1 (mixedReachable_mono (le_max_left _ _) h0 h),
    fun h => hJ.2.2.1 (purePVMReachable_mono (le_max_left _ _) h0 h),
    fun h => hJ.2.2.2 (mixedPVMReachable_mono (le_max_left _ _) h0 h)⟩

/-- Physical form of unitary zero-reachability. If for almost every fixed unitary no
finite budget reaches score error zero, then for almost every fixed unitary no finite
budget admits an exact pure or finite mixed implementation on any finite registers:
the channel differs from `Ad_T`, equivalently its normalized diamond error is
positive. -/
theorem ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable
    (hzero : ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
        T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0) :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
        (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
          P.HasFootprint K →
          P.operationalChannel ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ))) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix (Fin d × εA) (κA × μB) ℂ) (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          m.mixedChannel VA VB DA DB ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ))) := by
  intro d hd
  have : NeZero d := ⟨by omega⟩
  filter_upwards [hzero d hd] with T hT
  intro K
  have hU := Matrix.mem_unitaryGroup_iff'.mp T.2
  refine ⟨(hT K).1, (hT K).2, fun ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_⟩⟩
  · intro P hP
    have hpos : 0 < diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ)) := by
      by_contra hle
      exact (hT K).1 (P.mem_pureReachable hP (P.scoreU_ge_of_diamondError_le hU (not_lt.mp hle)))
    exact ⟨fun heq => hpos.ne' ((diamondError_eq_zero_iff _ _).mpr heq), hpos⟩
  · intro n m VA VB DA DB hVA hVB hDA hDB R hR hK
    have hpos : 0 < diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ)) := by
      by_contra hle
      exact (hT K).2 (m.mem_mixedReachable VA VB DA DB hVA hVB hDA hDB hR hK
        (m.scoreU_ge_of_diamondError_le hVA hVB hDA hDB hU (not_lt.mp hle)))
    exact ⟨fun heq => hpos.ne' ((diamondError_eq_zero_iff _ _).mpr heq), hpos⟩

/-- Physical form of PVM zero-reachability. If for almost every fixed basis lift no
finite budget reaches PVM score error zero, then for almost every fixed basis lift no
finite budget admits a pure or finite mixed protocol on any finite registers performing
the two-sided ordered PVM task exactly; equivalently its worst-case joint-TV error is
positive. -/
theorem ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable
    (hzero : ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
        M ∉ purePVMReachable d K 0 ∧ M ∉ mixedPVMReachable d K 0) :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      M ∉ purePVMReachable d K 0 ∧ M ∉ mixedPVMReachable d K 0 ∧
      ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
        (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
            (Fin d × Fin d) (Fin d × Fin d) εA εB,
          P.HasFootprint K →
          ¬ P.PerformsPVM (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
          (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          ¬ m.PerformsPVM VA VB DA DB (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) := by
  intro d hd
  have : NeZero d := ⟨by omega⟩
  filter_upwards [hzero d hd] with M hM
  intro K
  have hU := Matrix.mem_unitaryGroup_iff'.mp M.2
  refine ⟨(hM K).1, (hM K).2, fun ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_⟩⟩
  · intro P hP
    have hlt : scorePVM (M : Matrix _ _ ℂ) P.operationalChannel < 1 := by
      by_contra hle
      exact (hM K).1 (P.mem_purePVMReachable hP (by linarith))
    have hb := P.one_sub_scorePVM_le_pvmTVError hU
    exact ⟨fun hp => hlt.ne ((P.scorePVM_eq_one_iff_performsPVM hU).mpr hp), by linarith⟩
  · intro n m VA VB DA DB hVA hVB hDA hDB R hR hK
    have hlt : scorePVM (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) < 1 := by
      by_contra hle
      exact (hM K).1 (m.mem_purePVMReachable VA VB DA DB hVA hVB hDA hDB hR hK
        (by linarith))
    have hb := m.one_sub_scorePVM_le_pvmTVError hVA hVB hDA hDB hU
    exact ⟨fun hp => hlt.ne ((m.scorePVM_eq_one_iff_performsPVM hVA hVB hDA hDB hU).mpr hp),
      by linarith⟩

/-- Unitary exact impossibility: for almost every fixed unitary, no finite budget admits an exact pure or finite
mixed implementation on any finite registers: the channel differs from `Ad_T`,
equivalently its normalized diamond error is positive. -/
theorem ae_unitary_no_finite_exact_implementation (hGeom : PolynomialImageVolumeBound) :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      T ∉ pureReachable d K 0 ∧ T ∉ mixedReachable d K 0 ∧
      ∀ (ρA ρB κA κB μA μB εA εB : Type*)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
          P.HasFootprint K →
          P.operationalChannel ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ))) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix (Fin d × εA) (κA × μB) ℂ) (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          m.mixedChannel VA VB DA DB ≠ adConj (T : Matrix _ _ ℂ) ∧
            0 < diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ))) :=
  ae_unitary_no_finite_exact_implementation_of_ae_not_mem_reachable fun d hd =>
    (ae_not_mem_reachable_zero hGeom d hd).mono fun _ hT K => ⟨(hT K).1, (hT K).2.1⟩

/-- PVM exact impossibility: for almost every fixed basis lift, no finite budget admits a pure or finite mixed
protocol on any finite registers performing the two-sided ordered PVM task exactly;
equivalently its worst-case joint-TV error is positive. -/
theorem ae_pvm_no_finite_exact_implementation (hGeom : PolynomialImageVolumeBound) :
    ∀ d : ℕ, 2 ≤ d → ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d), ∀ K : ℕ,
      M ∉ purePVMReachable d K 0 ∧ M ∉ mixedPVMReachable d K 0 ∧
      ∀ (ρA ρB κA κB μA μB εA εB : Type*)
        [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
        [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
        [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
        [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
        (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
            (Fin d × Fin d) (Fin d × Fin d) εA εB,
          P.HasFootprint K →
          ¬ P.PerformsPVM (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) P.operationalChannel) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n)
          (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
          (DA : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)
          (DB : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ),
          IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
          ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
          ¬ m.PerformsPVM VA VB DA DB (M : Matrix _ _ ℂ) ∧
            0 < pvmTVError (M : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB)) :=
  ae_pvm_no_finite_exact_implementation_of_ae_not_mem_reachable fun d hd =>
    (ae_not_mem_reachable_zero hGeom d hd).mono fun _ hM K => ⟨(hM K).2.2.1, (hM K).2.2.2⟩

end NLQCLean
