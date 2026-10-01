import NLQCLean.Exact.FiniteExactRestriction
import NLQCLean.Exact.SpectatorControlledPhase
import NLQCLean.Exact.LocalChannelRestriction

/-!
# Exact exclusion of controlled phases with identity spectators

Fixing one spectator input in each laboratory and discarding the actual
spectator outputs restricts the target channel to a two-qubit controlled
phase. Exact pure or common-map finite-mixed implementation therefore forces
algebraicity of the exponential phase for every real angle. Nonzero algebraic
angles are excluded, including throughout the full local-unitary orbit.

The spectator types are independent arbitrary finite nonempty types. All
eight original internal register types remain independently universe-polymorphic.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀

open Matrix ClassicalCommunication
open scoped Kronecker

variable {σA : Type u₁} {σB : Type u₂}
variable [Fintype σA] [Fintype σB] [DecidableEq σA] [DecidableEq σB]

/-- Absorb all four local orbit factors into actual local input and output
maps, leaving the checked two-qubit controlled-phase restriction. -/
theorem spectatorControlledPhase_local_unitary_restrictedChannel_eq
    (θ : ℝ) (a0 : σA) (b0 : σB)
    {LA RA : Matrix (Fin 2 × σA) (Fin 2 × σA) ℂ}
    {LB RB : Matrix (Fin 2 × σB) (Fin 2 × σB) ℂ}
    (hLA : LA ∈ Matrix.unitaryGroup (Fin 2 × σA) ℂ)
    (hLB : LB ∈ Matrix.unitaryGroup (Fin 2 × σB) ℂ)
    (hRA : RA ∈ Matrix.unitaryGroup (Fin 2 × σA) ℂ)
    (hRB : RB ∈ Matrix.unitaryGroup (Fin 2 × σB) ℂ) :
    localChannelRestriction (RAᴴ * spectatorInputIsometry a0)
      (RBᴴ * spectatorInputIsometry b0)
      (spectatorOutputStinespring σA * LAᴴ)
      (spectatorOutputStinespring σB * LBᴴ)
      ((LA ⊗ₖ LB) * spectatorControlledPhase θ * (RA ⊗ₖ RB)) =
      adConj (controlledPhase θ) := by
  rw [localChannelRestriction_local_unitary_cancel
    (spectatorInputIsometry a0) (spectatorInputIsometry b0)
    (spectatorOutputStinespring σA) (spectatorOutputStinespring σB)
    (spectatorControlledPhase θ) hLA hLB hRA hRB]
  exact spectatorControlledPhase_restrictedChannel_eq θ a0 b0

section Protocols

variable [Nonempty σA] [Nonempty σB]
variable {ρA : Type u₃} {ρB : Type u₄} {κA : Type u₅} {κB : Type u₆}
variable {μA : Type u₇} {μB : Type u₈} {εA : Type u₉} {εB : Type u₁₀}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable {VA : Matrix (κA × μA) ((Fin 2 × σA) × ρA) ℂ}
variable {VB : Matrix (κB × μB) ((Fin 2 × σB) × ρB) ℂ}
variable {DA : Matrix ((Fin 2 × σA) × εA) (κA × μB) ℂ}
variable {DB : Matrix ((Fin 2 × σB) × εB) (κB × μA) ℂ}

/-- At every real angle, exact pure implementation of the first-qubit
controlled phase with identity spectators forces an algebraic phase. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB)
    {θ : ℝ} (hP : P.PerformsUnitary (spectatorControlledPhase θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  let a0 : σA := Classical.choice inferInstance
  let b0 : σB := Classical.choice inferInstance
  exact P.isAlgebraic_exp_angle_of_exact_local_restriction
    (spectatorInputIsometry a0) (spectatorInputIsometry b0)
    (spectatorOutputStinespring σA) (spectatorOutputStinespring σB)
    (spectatorInputIsometry_isometry a0) (spectatorInputIsometry_isometry b0)
    (spectatorOutputStinespring_isometry σA) (spectatorOutputStinespring_isometry σB)
    (spectatorControlledPhase_restrictedChannel_eq θ a0 b0) hP

/-- The same necessary phase algebraicity holds for actual common-map
finite-mixed exact implementation, with arbitrary original registers. -/
theorem MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hm : m.mixedChannel VA VB DA DB = adConj (spectatorControlledPhase θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  let a0 : σA := Classical.choice inferInstance
  let b0 : σB := Classical.choice inferInstance
  exact m.isAlgebraic_exp_angle_of_exact_local_restriction hVA hVB hDA hDB
    (spectatorInputIsometry a0) (spectatorInputIsometry b0)
    (spectatorOutputStinespring σA) (spectatorOutputStinespring σB)
    (spectatorInputIsometry_isometry a0) (spectatorInputIsometry_isometry b0)
    (spectatorOutputStinespring_isometry σA) (spectatorOutputStinespring_isometry σB)
    (spectatorControlledPhase_restrictedChannel_eq θ a0 b0) hm

/-- Exactness anywhere in the full local-unitary orbit of the spectator
gate implies algebraicity of the original angle's exponential phase. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase_orbit
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB)
    {θ : ℝ}
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase θ))
    (hP : P.PerformsUnitary U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rcases hU with ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩,
    R, ⟨RA, hRA, RB, hRB, rfl⟩, rfl⟩
  let a0 : σA := Classical.choice inferInstance
  let b0 : σB := Classical.choice inferInstance
  exact P.isAlgebraic_exp_angle_of_exact_local_restriction
    (RAᴴ * spectatorInputIsometry a0) (RBᴴ * spectatorInputIsometry b0)
    (spectatorOutputStinespring σA * LAᴴ) (spectatorOutputStinespring σB * LBᴴ)
    ((isIsometry_conjTranspose_of_unitary hRA).mul (spectatorInputIsometry_isometry a0))
    ((isIsometry_conjTranspose_of_unitary hRB).mul (spectatorInputIsometry_isometry b0))
    ((spectatorOutputStinespring_isometry σA).mul (isIsometry_conjTranspose_of_unitary hLA))
    ((spectatorOutputStinespring_isometry σB).mul (isIsometry_conjTranspose_of_unitary hLB))
    (spectatorControlledPhase_local_unitary_restrictedChannel_eq θ a0 b0 hLA hLB hRA hRB) hP

/-- Full local-orbit phase algebraicity for common-map finite mixtures.
The inverse local factors are physical isometries composed with the actual
input embeddings and spectator-output Stinespring maps. -/
theorem MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ}
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase θ))
    (hm : m.mixedChannel VA VB DA DB = adConj U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rcases hU with ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩,
    R, ⟨RA, hRA, RB, hRB, rfl⟩, rfl⟩
  let a0 : σA := Classical.choice inferInstance
  let b0 : σB := Classical.choice inferInstance
  exact m.isAlgebraic_exp_angle_of_exact_local_restriction hVA hVB hDA hDB
    (RAᴴ * spectatorInputIsometry a0) (RBᴴ * spectatorInputIsometry b0)
    (spectatorOutputStinespring σA * LAᴴ) (spectatorOutputStinespring σB * LBᴴ)
    ((isIsometry_conjTranspose_of_unitary hRA).mul (spectatorInputIsometry_isometry a0))
    ((isIsometry_conjTranspose_of_unitary hRB).mul (spectatorInputIsometry_isometry b0))
    ((spectatorOutputStinespring_isometry σA).mul (isIsometry_conjTranspose_of_unitary hLA))
    ((spectatorOutputStinespring_isometry σB).mul (isIsometry_conjTranspose_of_unitary hLB))
    (spectatorControlledPhase_local_unitary_restrictedChannel_eq θ a0 b0 hLA hLB hRA hRB) hm

/-- No pure protocol implements a nonzero algebraic-angle spectator gate. -/
theorem PureProtocol.not_performsUnitary_spectatorControlledPhase
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ¬ P.PerformsUnitary (spectatorControlledPhase θ) := by
  intro hP
  exact transcendental_exp_angle hθ0 hθ
    (P.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase hP)

/-- No common-map finite mixture implements a nonzero algebraic-angle
spectator gate. Both messages and all original register types are unrestricted. -/
theorem MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    m.mixedChannel VA VB DA DB ≠ adConj (spectatorControlledPhase θ) := by
  intro hm
  exact transcendental_exp_angle hθ0 hθ
    (m.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase hVA hVB hDA hDB hm)

/-- The pure exclusion covers the full local-unitary orbit. -/
theorem PureProtocol.not_performsUnitary_spectatorControlledPhase_orbit
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase θ)) :
    ¬ P.PerformsUnitary U := by
  intro hP
  exact transcendental_exp_angle hθ0 hθ
    (P.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase_orbit hU hP)

/-- The common-map mixed exclusion covers the full local-unitary orbit. -/
theorem MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase θ)) :
    m.mixedChannel VA VB DA DB ≠ adConj U := by
  intro hm
  exact transcendental_exp_angle hθ0 hθ
    (m.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase_orbit
      hVA hVB hDA hDB hU hm)

/-- The angle-one first-qubit controlled phase has no exact pure implementation. -/
theorem PureProtocol.not_performsUnitary_spectatorControlledPhase_one
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB) :
    ¬ P.PerformsUnitary (spectatorControlledPhase 1) :=
  P.not_performsUnitary_spectatorControlledPhase one_ne_zero isAlgebraic_one

/-- The angle-one spectator gate has no exact common-map mixed implementation. -/
theorem MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    m.mixedChannel VA VB DA DB ≠ adConj (spectatorControlledPhase 1) :=
  m.mixedChannel_ne_adConj_spectatorControlledPhase
    hVA hVB hDA hDB one_ne_zero isAlgebraic_one

/-- Every target in the angle-one spectator gate's full local orbit is excluded. -/
theorem PureProtocol.not_performsUnitary_spectatorControlledPhase_one_orbit
    (P : PureProtocol (Fin 2 × σA) (Fin 2 × σB) ρA ρB κA κB μA μB
      (Fin 2 × σA) (Fin 2 × σB) εA εB)
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase 1)) :
    ¬ P.PerformsUnitary U :=
  P.not_performsUnitary_spectatorControlledPhase_orbit one_ne_zero isAlgebraic_one hU

/-- Angle-one full-orbit exclusion for actual common-map finite mixtures. -/
theorem MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix ((Fin 2 × σA) × (Fin 2 × σB)) ((Fin 2 × σA) × (Fin 2 × σB)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (Fin 2 × σA) (Fin 2 × σB) (spectatorControlledPhase 1)) :
    m.mixedChannel VA VB DA DB ≠ adConj U :=
  m.mixedChannel_ne_adConj_spectatorControlledPhase_orbit
    hVA hVB hDA hDB one_ne_zero isAlgebraic_one hU

end Protocols

end NLQCLean
