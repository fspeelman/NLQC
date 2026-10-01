import NLQCLean.Semialgebraic.RationalPolynomialImages
import NLQCLean.Arithmetic.PhysicalPolynomialConstraints

/-! Integer equations give rational sign descriptions with the same evaluation. -/

namespace NLQCLean

/-- Extending integer coefficients to the reals factors through the rationals. -/
theorem map_integerPolynomial_via_rat {σ : Type*} (p : MvPolynomial σ ℤ) :
    MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) p) =
      MvPolynomial.map (Int.castRingHom ℝ) p := by
  rw [MvPolynomial.map_map]
  congr 1

/-- The real extension of an integer polynomial has rational coefficients. -/
theorem rationalPolynomialSubring_int {σ : Type*} (p : MvPolynomial σ ℤ) :
    MvPolynomial.map (Int.castRingHom ℝ) p ∈ rationalPolynomialSubring σ :=
  ⟨MvPolynomial.map (Int.castRingHom ℚ) p, map_integerPolynomial_via_rat p⟩

/-- The existing integer-polynomial evaluation is unchanged by real extension. -/
theorem eval_map_integerPolynomial {σ : Type*} (x : σ → ℝ) (p : MvPolynomial σ ℤ) :
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) p) =
      PhysicalPolynomial.eval x p := by
  rw [MvPolynomial.eval_map]
  rfl

/-- Zero loci use the actual integer-polynomial evaluation in the physical model. -/
theorem RationalSemialgebraic.polynomial_zero_int {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    RationalSemialgebraic {x : RealEuclidean n | PhysicalPolynomial.eval (fun i => x i) p = 0} := by
  simpa only [eval_map_integerPolynomial] using
    RationalSemialgebraic.polynomial_zero _ (rationalPolynomialSubring_int p)

end NLQCLean
