import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Approx.BorelClassicalSpectralFloors
import NLQCLean.Bounds.FiniteClassicalStrongUniversal
import NLQCLean.Bounds.ArbitraryFiniteClassicalAlmostEvery

/-!
# Rates for actual standard-Borel classical protocols

Actual original pure/common-map mixed channels and honest measured averages
enter the charged score classes at `4 * d⁴ * K⁵`. Original diamond and joint-TV
errors imply score accuracy before any selection. Haar bounds use outer
measure; the stronger universal rate remains restricted to unitary targets.
-/

namespace NLQCLean.ClassicalCommunication

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

open Matrix MeasureTheory StandardBorelClassicalProtocol
open scoped MeasureTheory ENNReal Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

/-- Record unchanged original systems with their intrinsic model instances. -/
def BorelSystems.ofTypes
    (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
    (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [MeasurableSpace σA] [MeasurableSpace σB]
    [StandardBorelSpace σA] [StandardBorelSpace σB] : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} :=
  { ρA := ρA, ρB := ρB, κA := κA, κB := κB, μA := μA, μB := μB, σA := σA, σB := σB
    fintypeρA := inferInstance, fintypeρB := inferInstance, fintypeκA := inferInstance
    fintypeκB := inferInstance, fintypeμA := inferInstance, fintypeμB := inferInstance
    decidableEqρA := inferInstance, decidableEqρB := inferInstance
    decidableEqκA := inferInstance, decidableEqκB := inferInstance
    decidableEqμA := inferInstance, decidableEqμB := inferInstance
    measurableσA := inferInstance, measurableσB := inferInstance
    standardBorelσA := inferInstance, standardBorelσB := inferInstance }

/-- Record the actual probability measure and original branch-dependent systems. -/
def BorelRandomSystems.ofTypes {α : Type u₉} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ρA : α → Type u₁) (ρB : α → Type u₂) (κA : α → Type u₃) (κB : α → Type u₄)
    (μA : α → Type u₅) (μB : α → Type u₆) (σA : α → Type u₇) (σB : α → Type u₈)
    [∀ a, Fintype (ρA a)] [∀ a, Fintype (ρB a)] [∀ a, Fintype (κA a)] [∀ a, Fintype (κB a)]
    [∀ a, Fintype (μA a)] [∀ a, Fintype (μB a)]
    [∀ a, DecidableEq (ρA a)] [∀ a, DecidableEq (ρB a)]
    [∀ a, DecidableEq (κA a)] [∀ a, DecidableEq (κB a)]
    [∀ a, DecidableEq (μA a)] [∀ a, DecidableEq (μB a)]
    [∀ a, MeasurableSpace (σA a)] [∀ a, MeasurableSpace (σB a)]
    [∀ a, StandardBorelSpace (σA a)] [∀ a, StandardBorelSpace (σB a)] : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} :=
  { α := α, measurableα := inferInstance, μ := μ, probability := inferInstance
    systems := fun a => BorelSystems.ofTypes (ρA a) (ρB a) (κA a) (κB a)
      (μA a) (μB a) (σA a) (σB a) }

noncomputable section

noncomputable local instance rateMatrixNormedAddCommGroup {ν : Type*} [Fintype ν] :
    NormedAddCommGroup (Matrix ν ν ℂ) := Matrix.normedAddCommGroup
noncomputable local instance rateMatrixTopologicalSpace {ν : Type*} [Fintype ν] :
    TopologicalSpace (Matrix ν ν ℂ) :=
  (rateMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
noncomputable local instance rateMatrixComplexNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance rateMatrixRealNormedSpace {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace
noncomputable local instance rateOperationNormedAddCommGroup {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance rateOperationRealNormedSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

variable {d K : ℕ} [NeZero d]

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelScoreReachable_of_quantumFootprint
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d) (Fin d))
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU (T : Matrix _ _ ℂ) (P.operationalChannel.toLinearMap)) :
    T ∈ borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  rw [borelScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inl ⟨hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelScoreReachable_of_quantumFootprint_diamondError
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d) (Fin d))
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasQuantumFootprint K) (herror : diamondError (P.operationalChannel.toLinearMap) (adConj (T : Matrix _ _ ℂ)) ≤ ε) : T ∈ borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  apply mem_borelScoreReachable_of_quantumFootprint s P T hd hK
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (P.operationalChannel) (P.operationalChannel_completelyPositive) (P.operationalChannel_tracePreserving)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError (Matrix.mem_unitaryGroup_iff'.mp T.property) (P.operationalChannel).toLinearMap hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelScoreReachable_of_mixedQuantumFootprint
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d) (Fin d))
    {n : ℕ} (m : MixedResource s.ρA s.ρB n)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scoreU (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    T ∈ borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  rw [borelScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inr ⟨n, m, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelScoreReachable_of_mixedQuantumFootprint_diamondError
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d) (Fin d))
    {n : ℕ} (m : MixedResource s.ρA s.ρB n)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasMixedQuantumFootprint m K) (herror : diamondError (P.mixedOperationalChannel m) (adConj (T : Matrix _ _ ℂ)) ≤ ε) : T ∈ borelScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  apply mem_borelScoreReachable_of_mixedQuantumFootprint s P m T hd hK
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    ((P.mixedOperationalChannel m).toContinuousLinearMap) (P.mixedOperationalChannel_completelyPositive m) (P.mixedOperationalChannel_tracePreserving m)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError (Matrix.mem_unitaryGroup_iff'.mp T.property) (P.mixedOperationalChannel m) hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelPVMScoreReachable_of_quantumFootprint
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasQuantumFootprint K) (hscore : 1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) (P.operationalChannel.toLinearMap)) :
    T ∈ borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  rw [borelPVMScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inl ⟨hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelPVMScoreReachable_of_quantumFootprint_pvmTVError
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasQuantumFootprint K) (herror : pvmTVError (T : Matrix _ _ ℂ) (P.operationalChannel.toLinearMap) ≤ ε) : T ∈ borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  apply mem_borelPVMScoreReachable_of_quantumFootprint s P T hd hK
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (P.operationalChannel) (P.operationalChannel_completelyPositive) (P.operationalChannel_tracePreserving)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError (Matrix.mem_unitaryGroup_iff'.mp T.property) hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelPVMScoreReachable_of_mixedQuantumFootprint
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    {n : ℕ} (m : MixedResource s.ρA s.ρB n)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasMixedQuantumFootprint m K) (hscore : 1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m)) :
    T ∈ borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  rw [borelPVMScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inr ⟨n, m, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelPVMScoreReachable_of_mixedQuantumFootprint_pvmTVError
    (s : BorelSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    {n : ℕ} (m : MixedResource s.ρA s.ρB n)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : P.HasMixedQuantumFootprint m K) (herror : pvmTVError (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤ ε) : T ∈ borelPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε := by
  apply mem_borelPVMScoreReachable_of_mixedQuantumFootprint s P m T hd hK
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    ((P.mixedOperationalChannel m).toContinuousLinearMap) (P.mixedOperationalChannel_completelyPositive m) (P.mixedOperationalChannel_tracePreserving m)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError (Matrix.mem_unitaryGroup_iff'.mp T.property) hphysical
  change 1 - scorePVM (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m) ≤
    pvmTVError (T : Matrix _ _ ℂ) (P.mixedOperationalChannel m) at hs
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelSharedRandomScoreReachable_of_sharedRandom
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) (hscore : 1 - ε ≤ scoreU (T : Matrix _ _ ℂ) ((sharedRandomOperationalChannel s.μ P).toLinearMap)) :
    T ∈ borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  rw [borelSharedRandomScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inl ⟨hP, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelSharedRandomScoreReachable_of_sharedRandom_diamondError
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d) (Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) (herror : diamondError ((sharedRandomOperationalChannel s.μ P).toLinearMap) (adConj (T : Matrix _ _ ℂ)) ≤ ε) : T ∈ borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  apply mem_borelSharedRandomScoreReachable_of_sharedRandom s P hP T hd hK
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (sharedRandomOperationalChannel s.μ P) (sharedRandomOperationalChannel_completelyPositive s.μ P hP) (sharedRandomOperationalChannel_tracePreserving s.μ P hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError (Matrix.mem_unitaryGroup_iff'.mp T.property) (sharedRandomOperationalChannel s.μ P).toLinearMap hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelSharedRandomScoreReachable_of_mixedSharedRandom
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d) (Fin d))
    {n : s.α → ℕ} (m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) (hscore : 1 - ε ≤ scoreU (T : Matrix _ _ ℂ) ((mixedSharedRandomOperationalChannel s.μ P m).toLinearMap)) :
    T ∈ borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  rw [borelSharedRandomScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inr ⟨n, m, hP, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelSharedRandomScoreReachable_of_mixedSharedRandom_diamondError
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d) (Fin d))
    {n : s.α → ℕ} (m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) (herror : diamondError ((mixedSharedRandomOperationalChannel s.μ P m).toLinearMap) (adConj (T : Matrix _ _ ℂ)) ≤ ε) : T ∈ borelSharedRandomScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  apply mem_borelSharedRandomScoreReachable_of_mixedSharedRandom s P m hP T hd hK
  have hphysical := trace_choiMatrix_eq_one_of_completelyPositive_tracePreserving
    (mixedSharedRandomOperationalChannel s.μ P m) (mixedSharedRandomOperationalChannel_completelyPositive s.μ P m hP) (mixedSharedRandomOperationalChannel_tracePreserving s.μ P m hP)
  have hs := NLQCLean.one_sub_scoreU_le_diamondError (Matrix.mem_unitaryGroup_iff'.mp T.property) (mixedSharedRandomOperationalChannel s.μ P m).toLinearMap hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelSharedRandomPVMScoreReachable_of_sharedRandom
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) (hscore : 1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) ((sharedRandomOperationalChannel s.μ P).toLinearMap)) :
    T ∈ borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  rw [borelSharedRandomPVMScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inl ⟨hP, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelSharedRandomPVMScoreReachable_of_sharedRandom_pvmTVError
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    (hP : AEStronglyMeasurable (fun a => (P a).operationalChannel) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasQuantumFootprint K) (herror : pvmTVError (T : Matrix _ _ ℂ) ((sharedRandomOperationalChannel s.μ P).toLinearMap) ≤ ε) : T ∈ borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  apply mem_borelSharedRandomPVMScoreReachable_of_sharedRandom s P hP T hd hK
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (sharedRandomOperationalChannel s.μ P) (sharedRandomOperationalChannel_completelyPositive s.μ P hP) (sharedRandomOperationalChannel_tracePreserving s.μ P hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError (Matrix.mem_unitaryGroup_iff'.mp T.property) hphysical
  linarith

/-- The unchanged original channel and its intrinsic source data are literal witnesses. -/
theorem mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    {n : s.α → ℕ} (m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) (hscore : 1 - ε ≤ scorePVM (T : Matrix _ _ ℂ) ((mixedSharedRandomOperationalChannel s.μ P m).toLinearMap)) :
    T ∈ borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  rw [borelSharedRandomPVMScoreReachable, dite_eq_left hd]
  exact ⟨s, P, Or.inr ⟨n, m, hP, hK, hscore⟩⟩

/-- Original operational error gives score accuracy before branch, component or outcome selection. -/
theorem mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom_pvmTVError
    (s : BorelRandomSystems.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉}) (P : s.Protocol d (Fin d × Fin d) (Fin d × Fin d))
    {n : s.α → ℕ} (m : ∀ a, MixedResource (s.systems a).ρA (s.systems a).ρB (n a))
    (hP : AEStronglyMeasurable (mixedBranchOperation P m) s.μ)
    (T : unitaryGroup (Fin d × Fin d) ℂ) {ε : ℝ} (hd : 0 < d)
    (hK : ∀ᵐ a ∂s.μ, (P a).HasMixedQuantumFootprint (m a) K) (herror : pvmTVError (T : Matrix _ _ ℂ) ((mixedSharedRandomOperationalChannel s.μ P m).toLinearMap) ≤ ε) : T ∈ borelSharedRandomPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε := by
  apply mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom s P m hP T hd hK
  have hphysical := isPVMOutcomeChannel_of_completelyPositive_tracePreserving
    (mixedSharedRandomOperationalChannel s.μ P m) (mixedSharedRandomOperationalChannel_completelyPositive s.μ P m hP) (mixedSharedRandomOperationalChannel_tracePreserving s.μ P m hP)
  have hs := NLQCLean.one_sub_scorePVM_le_pvmTVError (Matrix.mem_unitaryGroup_iff'.mp T.property) hphysical
  linarith

end

/-- Full-group outer Haar bound for all actual Borel and averaged score witnesses. -/
theorem exists_borel_classical_unitary_haar_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨16 * C, by linarith, ?_⟩
  intro d K hd hK ε hε hhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hK
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd hone hquarter ε hε hhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact (measure_mono (borelAllScoreReachable_subset_pureReachable (by omega : 0 < d) ε)).trans h

/-- This applied outer-measure theorem. -/
theorem exists_borel_classical_unitary_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) :=
  exists_borel_classical_unitary_haar_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

/-- Full-group outer Haar bound for all actual Borel and averaged score witnesses. -/
theorem exists_borel_classical_pvm_haar_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨16 * C, by linarith, ?_⟩
  intro d K hd hK ε hε hhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hK
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd hone hquarter ε hε hhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact (measure_mono (borelAllPVMScoreReachable_subset_purePVMReachable (by omega : 0 < d) ε)).trans h

/-- This applied outer-measure theorem. -/
theorem exists_borel_classical_pvm_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) :=
  exists_borel_classical_pvm_haar_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

/-- Target-dependent actual protocols transfer to the existing charged universal bound. -/
theorem exists_borel_classical_unitary_universal_log_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
  obtain ⟨c, hc, hbound⟩ := exists_universal_resource_constant_of_imageVolumeBound hGeom
  refine ⟨16 / c ^ 2, by positivity, ?_⟩
  intro d K hd hK ε hε hhalf hreach
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd (finiteClassical_charged_budget_admissible hd hK).1 ε hε hhalf).1 (fun T => borelAllScoreReachable_subset_pureReachable hd0 ε (hreach T))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The universal conclusion. -/
theorem exists_borel_classical_unitary_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 :=
  exists_borel_classical_unitary_universal_log_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

/-- Target-dependent actual protocols transfer to the existing charged universal bound. -/
theorem exists_borel_classical_pvm_universal_log_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
  obtain ⟨c, hc, hbound⟩ := exists_pvm_universal_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨16 / c ^ 2, by positivity, ?_⟩
  intro d K hd _hK ε hε hhalf hreach
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd ε hε hhalf).1 (fun T => borelAllPVMScoreReachable_subset_purePVMReachable hd0 ε (hreach T))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The universal conclusion. -/
theorem exists_borel_classical_pvm_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 :=
  exists_borel_classical_pvm_universal_log_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

/-- Target-dependent actual protocols transfer to the existing charged universal bound. -/
theorem exists_borel_classical_strong_unitary_universal_log_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 := by
  obtain ⟨c, hc, hbound⟩ := exists_strongUniversalResourceBound_of_imageVolumeBound hGeom
  refine ⟨16 / c ^ 2, by positivity, ?_⟩
  intro d K hd _hK ε hε hhalf hreach
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  apply log_le_fourth_tenth_power_of_finite_strong_charged_lower_bound hc hd0 hL
  have h := (hbound d (4 * d ^ 4 * K ^ 5) hd ε hε hhalf).1 (fun T => borelAllScoreReachable_subset_pureReachable hd0 ε (hreach T))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The universal conclusion. -/
theorem exists_borel_classical_strong_unitary_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∀ T, T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε) →
        Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 :=
  exists_borel_classical_strong_unitary_universal_log_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

/-- One fixed-target threshold precedes budget, error, all original systems
and every actual measured average. Budget zero is included. -/
theorem exists_ae_borel_classical_log_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        (T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨16 / c ^ 2, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by omega
  filter_upwards [hae d hd] with T hT
  obtain ⟨ε₀, hpos, hhalf, hcharged⟩ := hT
  refine ⟨ε₀, hpos, hhalf, ?_⟩
  intro K ε hε hsmall
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hbound := hcharged (4 * d ^ 4 * K ^ 5) ε hε hsmall
  constructor
  · intro hreach
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      hbound.1 (borelAllScoreReachable_subset_pureReachable hd0 ε hreach)
  · intro hreach
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      hbound.2.2.1 (borelAllPVMScoreReachable_subset_purePVMReachable hd0 ε hreach)

/-- Applied fixed-target rates. -/
theorem exists_ae_borel_classical_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (T ∈ borelAllScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        (T ∈ borelAllPVMScoreReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉} d K ε →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) :=
  exists_ae_borel_classical_log_constant_of_imageVolumeBound (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication
