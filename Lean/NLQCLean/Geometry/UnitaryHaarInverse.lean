import NLQCLean.Geometry.UnitaryHaar

/-!
# Inversion invariance of probability Haar measure on the unitary group

Adjoint and inversion preserve the relevant Haar bounds. Right translates and the
inverse of the compact probability Haar measure are left invariant with mass
one, so the proved uniqueness step identifies them with `unitaryHaar`.
-/

namespace NLQCLean

open MeasureTheory
open scoped ENNReal

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The compact unitary Haar measure is right invariant. -/
instance isMulRightInvariant_unitaryHaar : (unitaryHaar n).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap : Measure.map (· * g) (unitaryHaar n) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ,
      unitaryHaar_univ]
  have h := unitary_invariant_measure_eq_smul n (Measure.map (· * g) (unitaryHaar n))
  rw [hmap, one_smul] at h
  exact h

/-- The compact unitary Haar measure is invariant under inversion, i.e. the adjoint. -/
instance isInvInvariant_unitaryHaar : (unitaryHaar n).IsInvInvariant := by
  have hinv : (unitaryHaar n).inv Set.univ = 1 := by
    rw [Measure.inv_apply, Set.inv_univ, unitaryHaar_univ]
  have : IsFiniteMeasure (unitaryHaar n).inv := ⟨by rw [hinv]; exact ENNReal.one_lt_top⟩
  have h := unitary_invariant_measure_eq_smul n (unitaryHaar n).inv
  rw [hinv, one_smul] at h
  exact ⟨h⟩

theorem unitaryHaar_preimage_inv (S : Set (Matrix.unitaryGroup n ℂ)) :
    unitaryHaar n (Inv.inv ⁻¹' S) = unitaryHaar n S :=
  Measure.measure_preimage_inv _ _

end NLQCLean
