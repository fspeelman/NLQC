/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.ProjectionTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Audit of the semialgebraic projection theorem

The unchanged proposition `SemialgebraicProjectionTheorem` now has a closed
proof. Its expanded type and axioms are pinned below. The examples apply the
theorem itself (not the bridge alone): in dimension zero, where the proof
passes through `Fin.snoc` on `Fin 0`, and to the nonlinear set
`{p | p 1 ^ 2 = p 0}`, whose projection to the first coordinate is the
nonnegative half-line.
-/

namespace NLQCTests.SemialgebraicProjectionAudit

open NLQCLean

/-! ### Type and axioms -/

/-- info: semialgebraicProjectionTheorem : SemialgebraicProjectionTheorem -/
#guard_msgs in
#check @NLQCLean.semialgebraicProjectionTheorem

/-- The proposition proved, with its definition unfolded. -/
example : ∀ n : ℕ, ∀ A : Set (RealEuclidean (n + 1)), Semialgebraic A →
    Semialgebraic (coordinateProjection (Fin.castAdd 1) '' A) :=
  semialgebraicProjectionTheorem

/--
info: 'NLQCLean.semialgebraicProjectionTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NLQCLean.semialgebraicProjectionTheorem

/-! ### Dimension zero -/

/-- The open half-line `{x | 0 < x 0}` in `RealEuclidean 1`. -/
theorem semialgebraic_positive_halfLine :
    Semialgebraic {x : RealEuclidean 1 | 0 < x 0} :=
  ⟨PolynomialSignDNF.atom ⟨MvPolynomial.X 0, .positive⟩, by
    ext x
    simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]⟩

/-- Projection to the zero-dimensional space, through the proved theorem. -/
example : Semialgebraic
    (coordinateProjection (Fin.castAdd 1) '' {x : RealEuclidean 1 | 0 < x 0}) :=
  semialgebraicProjectionTheorem 0 _ semialgebraic_positive_halfLine

/-- The projection of the empty subset of the line, through the proved theorem. -/
example : Semialgebraic
    (coordinateProjection (Fin.castAdd 1) '' (∅ : Set (RealEuclidean 1))) :=
  semialgebraicProjectionTheorem 0 _ Semialgebraic.empty

/-- The zero-dimensional projection is the whole one-point space. -/
example : coordinateProjection (Fin.castAdd 1) '' {x : RealEuclidean 1 | 0 < x 0} =
    Set.univ := by
  ext y
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  refine ⟨WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) 1), ?_, ?_⟩
  · change (0 : ℝ) < (Fin.snoc (WithLp.ofLp y) 1 : Fin 1 → ℝ) (Fin.last 0)
    rw [Fin.snoc_last]
    exact one_pos
  · ext j
    exact j.elim0

/-! ### A nonlinear projection -/

/-- The parabola `{p | p 1 ^ 2 = p 0}` as a zero atom of `X 1 ^ 2 - X 0`. -/
theorem semialgebraic_parabola :
    Semialgebraic {p : RealEuclidean 2 | p 1 ^ 2 = p 0} :=
  ⟨PolynomialSignDNF.atom
    ⟨(MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ), .zero⟩, by
    ext p
    simp [PolynomialSignAtom.Holds, PolynomialSign.Holds, sub_eq_zero]⟩

/-- Its projection to the first coordinate is semialgebraic by the theorem. -/
theorem semialgebraic_parabola_projection :
    Semialgebraic
      (coordinateProjection (Fin.castAdd 1) '' {p : RealEuclidean 2 | p 1 ^ 2 = p 0}) :=
  semialgebraicProjectionTheorem 1 _ semialgebraic_parabola

/-- The projection is exactly the nonnegative half-line: a real number has a
real square root if and only if it is nonnegative. -/
theorem parabola_projection_eq :
    coordinateProjection (Fin.castAdd 1) '' {p : RealEuclidean 2 | p 1 ^ 2 = p 0} =
      {x : RealEuclidean 1 | 0 ≤ x 0} := by
  have h0 : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := rfl
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p 1 ^ 2 = p 0 at hp
    change 0 ≤ coordinateProjection (Fin.castAdd 1) p 0
    rw [coordinateProjection_apply, h0, ← hp]
    exact sq_nonneg _
  · intro hx
    change 0 ≤ x 0 at hx
    refine ⟨WithLp.toLp 2 ![x 0, Real.sqrt (x 0)], ?_, ?_⟩
    · change (WithLp.toLp 2 ![x 0, Real.sqrt (x 0)] : RealEuclidean 2) 1 ^ 2 =
        (WithLp.toLp 2 ![x 0, Real.sqrt (x 0)] : RealEuclidean 2) 0
      simp [Real.sq_sqrt hx]
    · ext j
      fin_cases j
      simp [h0]

/-- Hence the nonnegative half-line is semialgebraic via projection. -/
example : Semialgebraic {x : RealEuclidean 1 | 0 ≤ x 0} :=
  parabola_projection_eq ▸ semialgebraic_parabola_projection

end NLQCTests.SemialgebraicProjectionAudit
