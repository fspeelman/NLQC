import NLQCLean.Arithmetic.PhaseTranscendence
import NLQCLean.Exact.ExactPurityAlgebraicity
import NLQCLean.Invariants.LocalUnitaryPurity

/-!
# Exact exclusion of algebraic-angle controlled phases

Every exact implementation of a controlled phase forces its exponential
phase to be algebraic, for every real angle.
The normalized purity of a nonzero algebraic-angle controlled phase is
transcendental. Algebraicity of exact witness purity values therefore excludes
every finite pure protocol and every finite common-map mixed protocol, also
for targets in the full local-unitary orbit.

The proved rational semialgebraic witness graph supplies algebraicity of
each exact purity value. The physical predicates, unrestricted original
registers, and purity normalization are those from `ScalarCriticalValues`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix

/-- The full-angle controlled phase is a unitary target. -/
theorem controlledPhase_unitaryTarget (θ : ℝ) : UnitaryTarget (controlledPhase θ) :=
  ⟨(controlledPhase_unitary θ).1, (controlledPhase_unitary θ).2⟩

/-- Every matrix in the actual local double orbit of a controlled phase is
a unitary target. -/
theorem unitaryTarget_of_mem_controlledPhase_orbit {θ : ℝ}
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase θ)) :
    UnitaryTarget U := by
  rcases hU with ⟨L, hL, R, hR, rfl⟩
  have hC : controlledPhase θ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (controlledPhase_unitary θ).2
  have hV : L * controlledPhase θ * R ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem
        (localUnitaries_subset_unitary hL) hC)
      (localUnitaries_subset_unitary hR)
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.mem_unitaryGroup_iff.mp hV⟩

/-- Exact-value algebraicity contradicts controlled-phase transcendence,
using exactly the normalization in the physical witness adapter. -/
theorem controlledPhase_purity_not_mem
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    purity ((2 : ℝ) ^ 4)⁻¹ (controlledPhase θ) ∉ exactPurityValues 2 := by
  intro hmem
  apply transcendental_purity_controlledPhase hθ0 hθ
  have hnorm : ((2 : ℝ) ^ 4)⁻¹ = 1 / 16 := by norm_num
  simpa only [hnorm] using isAlgebraic_of_mem_exactPurityValues 2 hmem

/-- Purity invariance extends the obstruction to every member of the full
local-unitary orbit. -/
theorem controlledPhase_orbit_purity_not_mem
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase θ)) :
    purity ((2 : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues 2 := by
  rw [purity_eq_of_mem_unitaryDoubleOrbit ((2 : ℝ) ^ 4)⁻¹ hU]
  exact controlledPhase_purity_not_mem hθ0 hθ

/-- Any real controlled-phase angle whose actual normalized purity is an
exact witness value has an algebraic exponential phase. No algebraicity or
nonzero condition is imposed on the angle itself. -/
theorem isAlgebraic_exp_angle_of_controlledPhase_purity_mem
    {θ : ℝ}
    (hmem : purity ((2 : ℝ) ^ 4)⁻¹ (controlledPhase θ) ∈ exactPurityValues 2) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hpurity := isAlgebraic_of_mem_exactPurityValues 2 hmem
  have hnorm : ((2 : ℝ) ^ 4)⁻¹ = 1 / 16 := by norm_num
  have hvalue : IsAlgebraic ℚ (phasePurityValue θ) := by
    simpa only [hnorm, purity_controlledPhase, phasePurityValue] using hpurity
  exact isAlgebraic_exp_angle_of_cos (isAlgebraic_cos_of_phasePurityValue hvalue)

section Protocols

variable {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
variable {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Exact pure implementation of the two-qubit controlled phase implies
algebraicity of its exponential phase for every real angle. All original
finite resource, kept, message and discarded registers are arbitrary. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
    {θ : ℝ} (hP : P.PerformsUnitary (controlledPhase θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hscore : scoreU (controlledPhase θ) P.operationalChannel = 1 := by
    change P.operationalChannel = adConj (controlledPhase θ) at hP
    rw [hP, scoreU_adConj_self (controlledPhase_unitaryTarget θ).isIsometry]
  exact isAlgebraic_exp_angle_of_controlledPhase_purity_mem
    (P.purity_mem_exactPurityValues_of_score_eq_one (controlledPhase_unitaryTarget θ) hscore)

/-- Exact common-map finite-mixed implementation implies the same
algebraicity statement for every real angle. A selected pure component has
score at least the mixed score, and the isometry bound forces score one. -/
theorem MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin 2 × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin 2 × ρB) ℂ}
    {DA : Matrix (Fin 2 × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin 2 × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hm : m.mixedChannel VA VB DA DB = adConj (controlledPhase θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB (controlledPhase θ)
  let P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hge : 1 ≤ scoreU (controlledPhase θ) P.operationalChannel := by
    rw [hm, scoreU_adConj_self (controlledPhase_unitaryTarget θ).isIsometry] at hk
    exact hk
  have hF := P.isIsometry_globalIsometry.submatrix_equiv
    (outputRegroup (Fin 2) (Fin 2) εA εB) (Equiv.refl _)
  have hle : scoreU (controlledPhase θ) P.operationalChannel ≤ 1 :=
    scoreU_le_one (controlledPhase_unitaryTarget θ).isIsometry hF
  exact isAlgebraic_exp_angle_of_controlledPhase_purity_mem
    (P.purity_mem_exactPurityValues_of_score_eq_one
      (controlledPhase_unitaryTarget θ) (le_antisymm hle hge))

/-- A pure protocol on arbitrary finite original registers cannot implement
a nonzero algebraic-angle controlled phase. The exact purity algebraicity
theorem supplies the contradiction for every finite architecture. -/
theorem PureProtocol.not_performsUnitary_controlledPhase
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ¬ P.PerformsUnitary (controlledPhase θ) :=
  P.not_performsUnitary_of_purity_not_mem (controlledPhase_unitaryTarget θ)
    (controlledPhase_purity_not_mem hθ0 hθ)

/-- The pure operational exclusion also holds for the entire local orbit. -/
theorem PureProtocol.not_performsUnitary_controlledPhase_orbit
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase θ)) :
    ¬ P.PerformsUnitary U :=
  P.not_performsUnitary_of_purity_not_mem (unitaryTarget_of_mem_controlledPhase_orbit hU)
    (controlledPhase_orbit_purity_not_mem hθ0 hθ hU)

/-- Finite mixing with common physical maps cannot implement the controlled
phase. The resource decomposition and all eight original register types are
arbitrary, and both message registers remain explicit. -/
theorem MixedResource.mixedChannel_ne_adConj_controlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin 2 × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin 2 × ρB) ℂ}
    {DA : Matrix (Fin 2 × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin 2 × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    m.mixedChannel VA VB DA DB ≠ adConj (controlledPhase θ) :=
  m.mixedChannel_ne_adConj_of_purity_not_mem hVA hVB hDA hDB
    (controlledPhase_unitaryTarget θ)
    (controlledPhase_purity_not_mem hθ0 hθ)

/-- The common-map finite-mixed operational exclusion also holds for every
target in the controlled phase's local-unitary orbit. -/
theorem MixedResource.mixedChannel_ne_adConj_controlledPhase_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin 2 × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin 2 × ρB) ℂ}
    {DA : Matrix (Fin 2 × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin 2 × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase θ)) :
    m.mixedChannel VA VB DA DB ≠ adConj U :=
  m.mixedChannel_ne_adConj_of_purity_not_mem hVA hVB hDA hDB
    (unitaryTarget_of_mem_controlledPhase_orbit hU)
    (controlledPhase_orbit_purity_not_mem hθ0 hθ hU)

/-- Named pure-protocol exclusion for the angle one. -/
theorem PureProtocol.not_performsUnitary_controlledPhase_one
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB) :
    ¬ P.PerformsUnitary (controlledPhase 1) :=
  P.not_performsUnitary_controlledPhase
    one_ne_zero isAlgebraic_one

/-- Named common-map finite-mixed exclusion for the angle one. -/
theorem MixedResource.mixedChannel_ne_adConj_controlledPhase_one
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin 2 × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin 2 × ρB) ℂ}
    {DA : Matrix (Fin 2 × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin 2 × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    m.mixedChannel VA VB DA DB ≠ adConj (controlledPhase 1) :=
  m.mixedChannel_ne_adConj_controlledPhase
    hVA hVB hDA hDB one_ne_zero isAlgebraic_one

end Protocols

/-- The target precedes every arbitrary finite pure and common-map mixed
architecture in this combined exclusion statement. -/
theorem controlledPhase_no_finite_exact_implementation
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    NoFinitePureImplementation (controlledPhase θ) ∧
      NoFiniteMixedImplementation (controlledPhase θ) := by
  constructor
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    exact P.not_performsUnitary_controlledPhase hθ0 hθ
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n m VA VB DA DB
      hVA hVB hDA hDB
    exact m.mixedChannel_ne_adConj_controlledPhase
      hVA hVB hDA hDB hθ0 hθ

/-- Every member of the controlled phase's full local-unitary orbit has the
same arbitrary-finite pure and common-map mixed exclusion. -/
theorem controlledPhase_orbit_no_finite_exact_implementation
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase θ)) :
    NoFinitePureImplementation U ∧ NoFiniteMixedImplementation U := by
  constructor
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    exact P.not_performsUnitary_controlledPhase_orbit
      hθ0 hθ hU
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n m VA VB DA DB
      hVA hVB hDA hDB
    exact m.mixedChannel_ne_adConj_controlledPhase_orbit
      hVA hVB hDA hDB hθ0 hθ hU

/-- The named angle-one controlled phase excludes every finite pure and
common-map mixed architecture. -/
theorem controlledPhase_one_no_finite_exact_implementation :
    NoFinitePureImplementation (controlledPhase 1) ∧
      NoFiniteMixedImplementation (controlledPhase 1) :=
  controlledPhase_no_finite_exact_implementation
    one_ne_zero isAlgebraic_one

/-- The complete local-unitary orbit of the named angle-one phase has the
same exact exclusion. -/
theorem controlledPhase_one_orbit_no_finite_exact_implementation
    {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2) (Fin 2) (controlledPhase 1)) :
    NoFinitePureImplementation U ∧ NoFiniteMixedImplementation U :=
  controlledPhase_orbit_no_finite_exact_implementation
    one_ne_zero isAlgebraic_one hU

end NLQCLean
