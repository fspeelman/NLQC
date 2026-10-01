/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.VectorSard
import NLQCLean.Geometry.CriticalNormalImages

/-!
# Haar-null unitary sets from smooth rank-deficient covers

Let `f : E → V` be a globally smooth map on a finite-dimensional real space,
decoded into complex square matrices by a real-linear equivalence `L`, and let
the full ambient derivative of `f` have real rank at most `r` at every point of
an arbitrary set `T`, where `r + (card n)² < 2 (card n)²`. Every point of
`T × Herm` is then a critical point of the right normal thickening
`(x, Q) ↦ L (f x) (I + Q)`, so vector-valued Sard makes the thickened image
volume-null.

Consequently a Borel set of unitaries, each of which is a decoded value of one
of countably many such maps on its witness set, is Haar-null: its right normal
image lies in the countable union of null thickened images, and the
normal-volume identity with positive normal mass forces Haar measure zero.

The witness sets are arbitrary: no measurability or openness is needed.

## Main results

* `volume_image_normalThickening_eq_zero`: the thickened image of a uniformly
  rank-deficient witness set is volume-null.
* `unitaryHaar_eq_zero_of_rankDeficient_cover`: a Borel unitary set covered by
  countably many smooth uniformly rank-deficient witness maps is Haar-null.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius _root_.ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n]
  {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The right normal thickening of a smooth map over an arbitrary set of points
at which the full derivative has rank at most `r`, with
`r + (card n)² < 2 (card n)²`, has volume-null image. -/
theorem volume_image_normalThickening_eq_zero (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) {T : Set E} {r : ℕ}
    (hrank : ∀ x ∈ T, Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2) :
    volume (normalThickening L f '' (T ×ˢ Set.univ)) = 0 :=
  criticalImage_volume_eq_zero (contDiff_normalThickening L hf)
    (not_surjective_fderiv_normalThickening_on L
      (fun _ _ => (hf.differentiable (by simp)).differentiableAt) hrank hr)

/-- A Borel set of unitaries, each a decoded value of one of countably many smooth
maps at a point of its witness set where the full derivative has rank at most `r`,
with `r + (card n)² < 2 (card n)²`, is Haar-null. -/
theorem unitaryHaar_eq_zero_of_rankDeficient_cover {ι : Type*} [Countable ι]
    (L : ι → V ≃ₗ[ℝ] Matrix n n ℂ) (f : ι → E → V) (T : ι → Set E) {r : ℕ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hrank : ∀ i, ∀ x ∈ T i,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (f i) x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ i, ∃ x ∈ T i, L i (f i x) = (U : Matrix n n ℂ)) :
    unitaryHaar n S = 0 :=
  unitaryHaar_eq_zero_of_normalThickening_cover (E := fun _ => E) (V := fun _ => V) L f T hS
    hcover fun i => volume_image_normalThickening_eq_zero (L i) (hf i) (hrank i) hr

end NLQCLean
