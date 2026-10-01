import NLQCLean.Exact.BitstringControlledPhase
import NLQCLean.Exact.FiniteExactRestriction

/-!
# Exact exclusion of the source first-qubit gate

For every positive number of qubits per party, exact implementation forces an
algebraic exponential phase. This covers the angle-one target and its full
local-unitary orbit, on arbitrary finite pure/common-map mixed architectures.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

attribute [local implicit_reducible] Matrix

open Matrix ClassicalCommunication
open scoped Kronecker

variable {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
variable {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable {k : ℕ}

/-- The source necessary condition for any real angle and every positive qubit count. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB)
    {θ : ℝ} (hP : P.PerformsUnitary (bitstringControlledPhase k θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) :=
  P.isAlgebraic_exp_angle_of_exact_local_restriction
    (bitstringInputIsometry k) (bitstringInputIsometry k)
    (bitstringOutputStinespring k) (bitstringOutputStinespring k)
    (bitstringInputIsometry_isometry k) (bitstringInputIsometry_isometry k)
    (bitstringOutputStinespring_isometry k) (bitstringOutputStinespring_isometry k)
    (bitstringControlledPhase_restrictedChannel_eq k θ) hP

/-- Common-map finite mixtures satisfy the same all-qubit necessary condition. -/
theorem MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hm : m.mixedChannel VA VB DA DB = adConj (bitstringControlledPhase k θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) :=
  m.isAlgebraic_exp_angle_of_exact_local_restriction hVA hVB hDA hDB
    (bitstringInputIsometry k) (bitstringInputIsometry k)
    (bitstringOutputStinespring k) (bitstringOutputStinespring k)
    (bitstringInputIsometry_isometry k) (bitstringInputIsometry_isometry k)
    (bitstringOutputStinespring_isometry k) (bitstringOutputStinespring_isometry k)
    (bitstringControlledPhase_restrictedChannel_eq k θ) hm

/-- Inverse local unitaries are physical input and output maps, so the full
source local orbit has the same necessary condition. -/
theorem PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase_orbit
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB)
    {θ : ℝ} {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k θ)) (hP : P.PerformsUnitary U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rcases hU with ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩,
    R, ⟨RA, hRA, RB, hRB, rfl⟩, rfl⟩
  exact P.isAlgebraic_exp_angle_of_exact_local_restriction
    (RAᴴ * bitstringInputIsometry k) (RBᴴ * bitstringInputIsometry k)
    (bitstringOutputStinespring k * LAᴴ) (bitstringOutputStinespring k * LBᴴ)
    ((isIsometry_conjTranspose_of_unitary hRA).mul (bitstringInputIsometry_isometry k))
    ((isIsometry_conjTranspose_of_unitary hRB).mul (bitstringInputIsometry_isometry k))
    ((bitstringOutputStinespring_isometry k).mul (isIsometry_conjTranspose_of_unitary hLA))
    ((bitstringOutputStinespring_isometry k).mul (isIsometry_conjTranspose_of_unitary hLB))
    (by
      change localChannelRestriction _ _ _ _ _ = _
      rw [localChannelRestriction_local_unitary_cancel _ _ _ _ _ hLA hLB hRA hRB]
      exact bitstringControlledPhase_restrictedChannel_eq k θ) hP

/-- Local-unitary cancellation is common to every mixed component. -/
theorem MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k θ)) (hm : m.mixedChannel VA VB DA DB = adConj U) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rcases hU with ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩,
    R, ⟨RA, hRA, RB, hRB, rfl⟩, rfl⟩
  exact m.isAlgebraic_exp_angle_of_exact_local_restriction hVA hVB hDA hDB
    (RAᴴ * bitstringInputIsometry k) (RBᴴ * bitstringInputIsometry k)
    (bitstringOutputStinespring k * LAᴴ) (bitstringOutputStinespring k * LBᴴ)
    ((isIsometry_conjTranspose_of_unitary hRA).mul (bitstringInputIsometry_isometry k))
    ((isIsometry_conjTranspose_of_unitary hRB).mul (bitstringInputIsometry_isometry k))
    ((bitstringOutputStinespring_isometry k).mul (isIsometry_conjTranspose_of_unitary hLA))
    ((bitstringOutputStinespring_isometry k).mul (isIsometry_conjTranspose_of_unitary hLB))
    (by
      change localChannelRestriction _ _ _ _ _ = _
      rw [localChannelRestriction_local_unitary_cancel _ _ _ _ _ hLA hLB hRA hRB]
      exact bitstringControlledPhase_restrictedChannel_eq k θ) hm

/-- No exact pure implementation of a first-qubit phase at a nonzero algebraic angle. -/
theorem PureProtocol.not_performsUnitary_bitstringControlledPhase
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ¬ P.PerformsUnitary (bitstringControlledPhase k θ) := by
  intro hP
  exact transcendental_exp_angle hθ0 hθ
    (P.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase hP)

theorem MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    m.mixedChannel VA VB DA DB ≠ adConj (bitstringControlledPhase k θ) := by
  intro hm
  exact transcendental_exp_angle hθ0 hθ
    (m.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase hVA hVB hDA hDB hm)

/-- Every unitary in the source gate's full local orbit is excluded. -/
theorem PureProtocol.not_performsUnitary_bitstringControlledPhase_orbit
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k θ)) : ¬ P.PerformsUnitary U := by
  intro hP
  exact transcendental_exp_angle hθ0 hθ
    (P.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase_orbit hU hP)

theorem MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ)
    {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k θ)) : m.mixedChannel VA VB DA DB ≠ adConj U := by
  intro hm
  exact transcendental_exp_angle hθ0 hθ
    (m.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase_orbit
      hVA hVB hDA hDB hU hm)

/-- The paper's named angle-one gate is excluded for every positive qubit count. -/
theorem PureProtocol.not_performsUnitary_bitstringControlledPhase_one
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB) :
    ¬ P.PerformsUnitary (bitstringControlledPhase k 1) :=
  P.not_performsUnitary_bitstringControlledPhase one_ne_zero isAlgebraic_one

theorem MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    m.mixedChannel VA VB DA DB ≠ adConj (bitstringControlledPhase k 1) :=
  m.mixedChannel_ne_adConj_bitstringControlledPhase hVA hVB hDA hDB
    one_ne_zero isAlgebraic_one

/-- The full local-unitary orbit of the named source gate is excluded. -/
theorem PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit
    (P : PureProtocol (QubitString (k + 1)) (QubitString (k + 1))
      ρA ρB κA κB μA μB (QubitString (k + 1)) (QubitString (k + 1)) εA εB)
    {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k 1)) : ¬ P.PerformsUnitary U :=
  P.not_performsUnitary_bitstringControlledPhase_orbit one_ne_zero isAlgebraic_one hU

theorem MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one_orbit
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (QubitString (k + 1) × ρA) ℂ}
    {VB : Matrix (κB × μB) (QubitString (k + 1) × ρB) ℂ}
    {DA : Matrix (QubitString (k + 1) × εA) (κA × μB) ℂ}
    {DB : Matrix (QubitString (k + 1) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ}
    (hU : U ∈ unitaryDoubleOrbit (QubitString (k + 1)) (QubitString (k + 1))
      (bitstringControlledPhase k 1)) : m.mixedChannel VA VB DA DB ≠ adConj U :=
  m.mixedChannel_ne_adConj_bitstringControlledPhase_orbit hVA hVB hDA hDB
    one_ne_zero isAlgebraic_one hU

end NLQCLean
