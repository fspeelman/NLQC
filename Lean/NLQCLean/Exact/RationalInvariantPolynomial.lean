import NLQCLean.Exact.WitnessRationalCoordinates
import NLQCLean.Exact.RationalPolynomialSmoothness
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Rational polynomials in target-matrix entries

The variable index records each target entry and its real or imaginary part.
Renaming these variables into the seven-block witness coordinates preserves
their evaluation exactly. These ambient rational polynomial functions are
smooth; invariance on unitary orbits is a separate hypothesis.
-/

noncomputable section

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- One real and one imaginary variable per entry of the bipartite target. -/
abbrev RationalMatrixEntryIndex (d : ℕ) :=
  ((Fin d × Fin d) × (Fin d × Fin d)) × Fin 2

/-- Raw real coordinates of the target matrix, with zero selecting real part. -/
def rationalMatrixCoordinates {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    RationalMatrixEntryIndex d → ℝ :=
  fun v => if v.2 = 0 then (U v.1.1 v.1.2).re else (U v.1.1 v.1.2).im

/-- Evaluate a rational polynomial in the actual real and imaginary target entries. -/
def rationalMatrixInvariant {d : ℕ} (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) (rationalMatrixCoordinates U) p

/-- Include the target-entry polynomial in the complete seven-block index. -/
def targetInvariantPolynomial (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℚ :=
  MvPolynomial.rename (ExactWitnessCoordinates.targetCoordinates d s) p

/-- The complete witness coordinates reconstruct every real and imaginary
coordinate of the independent target block. -/
theorem rationalMatrixCoordinates_targetCoordinates (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    rationalMatrixCoordinates ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 =
      z ∘ ExactWitnessCoordinates.targetCoordinates d s := by
  rw [← ExactWitnessCoordinates.coordinateMatrix_targetCoordinates d s z]
  funext v
  rcases v with ⟨⟨i, j⟩, b⟩
  fin_cases b <;> rfl

/-- Renaming into the target coordinates evaluates precisely the original
rational matrix polynomial, with no constraint on any witness block. -/
theorem targetInvariantPolynomial_evaluate (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) z (targetInvariantPolynomial d s p) =
      rationalMatrixInvariant p ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 := by
  rw [targetInvariantPolynomial, MvPolynomial.eval₂_rename, rationalMatrixInvariant,
    rationalMatrixCoordinates_targetCoordinates]

/-- Every rational polynomial in real and imaginary matrix entries is smooth
on the actual finite-dimensional real matrix space with its Frobenius norm. -/
@[fun_prop] theorem contDiff_rationalMatrixInvariant {d : ℕ}
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ) :
    ContDiff ℝ ∞ (rationalMatrixInvariant p) := by
  unfold rationalMatrixInvariant
  refine contDiff_rationalMvPolynomial_eval_comp (p := p) ?_
  intro v
  have hentry : ContDiff ℝ ∞
      (fun U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ => U v.1.1 v.1.2) :=
    ContDiff.matrixEntry contDiff_id v.1.1 v.1.2
  by_cases hv : v.2 = 0
  · simpa only [rationalMatrixCoordinates, hv, if_true] using ContDiff.complexRe hentry
  · simpa only [rationalMatrixCoordinates, hv, if_false] using ContDiff.complexIm hentry

end NLQCLean
