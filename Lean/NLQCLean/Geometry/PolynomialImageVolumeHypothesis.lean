/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The explicit polynomial image-volume hypothesis

`paper/conditional-quantitative-proof.md` states this polynomial image-volume
contract. The quantitative theorems take `PolynomialImageVolumeBound` as an ordinary argument.
No proof of this property, axiom asserting it, or instance supplying it is introduced.

All coordinates have the real Euclidean inner product and its Lebesgue measure.
In particular, source balls do not use the sup norm on a function space. Polynomial
coefficients are unrestricted; only the number of constraints and total degrees are bounded.
-/

section

open MeasureTheory
open scoped ENNReal

namespace NLQCLean

/-- Real Euclidean coordinates, with the l2 norm and orthonormal-coordinate volume. -/
abbrev RealEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The full target-dimensional real Jacobian, including zero singular values. -/
noncomputable def topRealJacobian {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) : ℝ :=
  Real.sqrt (LinearMap.det (L.comp L.adjoint).toLinearMap)

theorem topRealJacobian_nonneg {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) : 0 ≤ topRealJacobian L :=
  Real.sqrt_nonneg _

/-- The Lebesgue volume of the open Euclidean unit ball, as an extended nonnegative real.
The measure is normalized by an orthonormal coordinate cube of volume one. -/
noncomputable def euclideanUnitBallVolume (m : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : RealEuclidean m) 1)

/-- At most twenty polynomial equations and weak inequalities, each of total degree
at most one hundred. There is no restriction on their real coefficients. -/
structure PolynomialBasicClosedFormat (a : ℕ) where
  numEquations : ℕ
  numInequalities : ℕ
  constraint_count : numEquations + numInequalities ≤ 20
  equations : Fin numEquations → MvPolynomial (Fin a) ℝ
  inequalities : Fin numInequalities → MvPolynomial (Fin a) ℝ
  equations_degree : ∀ i, (equations i).totalDegree ≤ 100
  inequalities_degree : ∀ i, (inequalities i).totalDegree ≤ 100

/-- The set described by the format, with inequalities oriented as `g(x) ≥ 0`.
No auxiliary quantified coordinates or additional implicit constraints occur. -/
def PolynomialBasicClosedFormat.source {a : ℕ} (F : PolynomialBasicClosedFormat a) :
    Set (RealEuclidean a) :=
  {x | (∀ i, MvPolynomial.eval (fun j ↦ x j) (F.equations i) = 0) ∧
    (∀ i, 0 ≤ MvPolynomial.eval (fun j ↦ x j) (F.inequalities i))}

/-- A coordinatewise real polynomial map of total degree at most one hundred. -/
structure BoundedPolynomialMap (a m : ℕ) where
  coordinates : Fin m → MvPolynomial (Fin a) ℝ
  degree_le : ∀ j, (coordinates j).totalDegree ≤ 100

/-- Evaluate the polynomial coordinates in the Euclidean source and target spaces. -/
noncomputable def BoundedPolynomialMap.eval {a m : ℕ} (p : BoundedPolynomialMap a m)
    (x : RealEuclidean a) : RealEuclidean m :=
  WithLp.toLp 2 (fun j ↦ MvPolynomial.eval (fun i ↦ x i) (p.coordinates j))

/-- The polynomial image-volume property with its universal constant fixed. Compactness, radius, and the Jacobian bound
are checked only on the exact basic closed source. Empty sources are allowed. -/
def PolynomialImageVolumeBoundWith (C : ℝ) : Prop :=
  ∀ (a m : ℕ), 1 ≤ a → 1 ≤ m →
    ∀ (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m),
      IsCompact F.source → F.source ⊆ Metric.closedBall 0 3 →
      ∀ B : ℝ, 0 ≤ B →
        (∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B) →
        volume (p.eval '' F.source) ≤
          ENNReal.ofReal (C ^ (a + m)) * euclideanUnitBallVolume m * ENNReal.ofReal B

/-- The sole geometric hypothesis of T: one `C ≥ 1` works simultaneously for all positive
source/target dimensions, all allowed formats, all coefficients, and all `B ≥ 0`.
This is a transparent proposition, not an axiom or a typeclass. -/
def PolynomialImageVolumeBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ PolynomialImageVolumeBoundWith C

/-- Extract the single dimension-uniform constant from an explicit proof argument. -/
theorem PolynomialImageVolumeBound.exists_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ PolynomialImageVolumeBoundWith C :=
  hGeom

end NLQCLean

end
