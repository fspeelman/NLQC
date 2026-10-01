/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.VectorSard
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit of vector-valued Sard

The checks print the vendored Morse--Sard theorem and the project wrappers, and audit their
axioms. The examples apply the wrappers with a source of higher dimension than the target, so that
the wrappers are not the easy case of a smaller source. The concrete map
`(a, b, c) ↦ (a, b ^ 2 + c ^ 2)` from `ℝ × ℝ × ℝ` to `ℝ × ℝ` is shown to be critical on the
nonempty line `b = c = 0`, and the wrapper makes the image of that line null.
-/

set_option format.width 120

section

open MeasureTheory Module Set

open scoped ContDiff

namespace NLQCTests.VectorSardAudit

open NLQCLean

/-! ## Statements and axioms -/

#check @NLQCLean.Vendor.TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero
#check @NLQCLean.criticalImage_addHaar_eq_zero
#check @NLQCLean.criticalImage_volume_eq_zero
#check @NLQCLean.rankDeficientImage_addHaar_eq_zero

/--
info: 'NLQCLean.Vendor.TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Vendor.TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero

/--
info: 'NLQCLean.criticalImage_addHaar_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.criticalImage_addHaar_eq_zero

/--
info: 'NLQCLean.criticalImage_volume_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.criticalImage_volume_eq_zero

/--
info: 'NLQCLean.rankDeficientImage_addHaar_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rankDeficientImage_addHaar_eq_zero

/-! ## Source of higher dimension than the target -/

/-- Three-dimensional source and two-dimensional target. -/
theorem euclidean_finrank_target_lt_source :
    finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  simp

/-- The wrapper specialized to smooth maps from three- to two-dimensional Euclidean space, with an
arbitrary critical subset and the canonical volume of the target. -/
theorem euclidean_criticalImage_volume_eq_zero
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (s : Set (EuclideanSpace ℝ (Fin 3)))
    (hs : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x)) : volume (f '' s) = 0 :=
  criticalImage_volume_eq_zero hf hs

/-- The rank form, specialized to the same dimensions. -/
theorem euclidean_rankDeficientImage_volume_eq_zero
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (s : Set (EuclideanSpace ℝ (Fin 3)))
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range
      (fderiv ℝ f x : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) < 2) :
    volume (f '' s) = 0 :=
  rankDeficientImage_addHaar_eq_zero volume hf fun x hx ↦ by simpa using hs x hx

/-- The first coordinate together with the squared norm of the last two coordinates. -/
noncomputable def firstCoordinateAndSquaredNorm : ℝ × ℝ × ℝ → ℝ × ℝ :=
  fun p ↦ (p.1, p.2.1 ^ 2 + p.2.2 ^ 2)

/-- The line on which `firstCoordinateAndSquaredNorm` is critical. -/
def firstAxis : Set (ℝ × ℝ × ℝ) := {p | p.2.1 = 0 ∧ p.2.2 = 0}

/-- The concrete map also has a three-dimensional source and a two-dimensional target. -/
theorem finrank_target_lt_source : finrank ℝ (ℝ × ℝ) < finrank ℝ (ℝ × ℝ × ℝ) := by
  simp

/-- The critical line is nonempty. -/
theorem firstAxis_nonempty : firstAxis.Nonempty :=
  ⟨0, by simp [firstAxis]⟩

/-- The concrete map is smooth. -/
theorem contDiff_firstCoordinateAndSquaredNorm :
    ContDiff ℝ ∞ firstCoordinateAndSquaredNorm := by
  unfold firstCoordinateAndSquaredNorm
  fun_prop

/-- On the first axis the second component has a minimum, so its derivative vanishes and the
derivative of the whole map misses the second coordinate direction. -/
theorem not_surjective_fderiv_of_mem_firstAxis {p : ℝ × ℝ × ℝ} (hp : p ∈ firstAxis) :
    ¬ Function.Surjective (fderiv ℝ firstCoordinateAndSquaredNorm p) := by
  intro hsurj
  have hd : HasFDerivAt (fun q ↦ (firstCoordinateAndSquaredNorm q).2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ firstCoordinateAndSquaredNorm p)) p :=
    ((contDiff_firstCoordinateAndSquaredNorm.differentiable (by simp)) p).hasFDerivAt.snd
  have hmin : IsLocalMin (fun q ↦ (firstCoordinateAndSquaredNorm q).2) p :=
    Filter.Eventually.of_forall fun q ↦ by
      simp only [firstCoordinateAndSquaredNorm, hp.1, hp.2]
      nlinarith [sq_nonneg q.2.1, sq_nonneg q.2.2]
  have hzero := IsLocalMin.hasFDerivAt_eq_zero hmin hd
  obtain ⟨v, hv⟩ := hsurj (0, 1)
  have hv' := congrArg (fun A : ℝ × ℝ × ℝ →L[ℝ] ℝ ↦ A v) hzero
  simp [hv] at hv'

/-- The concrete smooth map from three to two dimensions sends its nonempty critical line to a
null set of the Lebesgue measure `volume.prod volume` of the target. -/
theorem firstCoordinateAndSquaredNorm_image_firstAxis_volume_eq_zero :
    volume (firstCoordinateAndSquaredNorm '' firstAxis) = 0 :=
  criticalImage_addHaar_eq_zero ((volume : Measure ℝ).prod volume)
    contDiff_firstCoordinateAndSquaredNorm
    fun _ hp ↦ not_surjective_fderiv_of_mem_firstAxis hp

#check @euclidean_criticalImage_volume_eq_zero
#check @euclidean_rankDeficientImage_volume_eq_zero
#check @firstCoordinateAndSquaredNorm_image_firstAxis_volume_eq_zero

/--
info: 'NLQCTests.VectorSardAudit.euclidean_criticalImage_volume_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms euclidean_criticalImage_volume_eq_zero

/--
info: 'NLQCTests.VectorSardAudit.euclidean_rankDeficientImage_volume_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms euclidean_rankDeficientImage_volume_eq_zero

/--
info: 'NLQCTests.VectorSardAudit.firstCoordinateAndSquaredNorm_image_firstAxis_volume_eq_zero'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms firstCoordinateAndSquaredNorm_image_firstAxis_volume_eq_zero

end NLQCTests.VectorSardAudit

end
