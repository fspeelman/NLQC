/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.RationalProjection
import NLQCLean.Semialgebraic.SundogBridge
import NLQCLean.Semialgebraic.Projection

/-!
# Rational descriptions in Euclidean coordinates

Rational semialgebraic sets have polynomial sign descriptions with rational
coefficients. The constructive projection theorem eliminates any finite
number of coordinates while preserving that coefficient field. Forgetting
the rational restriction gives the existing real semialgebraic predicate.
-/

namespace NLQCLean

/-- A Euclidean set with a Boolean rational polynomial sign description. -/
def RationalSemialgebraic {n : ℕ} (S : Set (RealEuclidean n)) : Prop :=
  RationalQE.SADef n ((WithLp.toLp 2) ⁻¹' S)

namespace RationalQE

/-- Pullback by a coordinate selection preserves rational descriptions. -/
theorem SADef.coordinate_preimage {n m : ℕ} {S : Set (Fin n → ℝ)}
    (hS : SADef n S) (f : Fin n → Fin m) :
    SADef m ((fun g : Fin m → ℝ => g ∘ f) ⁻¹' S) := by
  induction hS with
  | pos p hp =>
    have h := SADef.pos (MvPolynomial.rename f p) (rationalPolynomialSubring_rename hp f)
    convert h using 1
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, MvPolynomial.eval_rename]
  | compl _ ih =>
    simpa only [Set.preimage_compl] using ih.compl
  | union _ _ ihs iht =>
    simpa only [Set.preimage_union] using ihs.union iht

end RationalQE

namespace RationalSemialgebraic

/-- The rational restriction refines the library's real predicate. -/
theorem semialgebraic {n : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) : Semialgebraic S :=
  (semialgebraic_iff_sadef S).mpr hS.to_real

/-- Arbitrary coordinate selections preserve the coefficient field. -/
theorem coordinate_preimage {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (f : Fin n → Fin m) :
    RationalSemialgebraic (coordinateProjection f ⁻¹' S) := by
  have h := RationalQE.SADef.coordinate_preimage hS f
  exact h

/-- Eliminate the last real coordinate, including the zero-dimensional case. -/
theorem projection {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : RationalSemialgebraic S) :
    RationalSemialgebraic (coordinateProjection (Fin.castAdd 1) '' S) := by
  unfold RationalSemialgebraic
  rw [toLp_preimage_image_coordinateProjection_castAdd]
  exact RationalQE.sadef_proj hS

/-- Eliminate any finite number of trailing coordinates with no external premise. -/
theorem first_projection {n m : ℕ} {S : Set (RealEuclidean (n + m))}
    (hS : RationalSemialgebraic S) :
    RationalSemialgebraic (coordinateProjection (Fin.castAdd m) '' S) := by
  induction m with
  | zero =>
    simpa only [show coordinateProjection (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id from rfl,
      Set.image_id] using hS
  | succ m ih =>
    have hs := hS.projection
    have h := ih hs
    convert h using 1
    rw [Set.image_image]
    rfl

end RationalSemialgebraic
end NLQCLean
