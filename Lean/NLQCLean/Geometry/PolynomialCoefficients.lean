/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Format

/-!
# Finite coefficient coordinates for degree-bounded polynomials

The monomial indices have bounded total degree. Reconstruction
uses `MvPolynomial` coefficients; no geometric premise is involved.
-/

section

open scoped BigOperators

namespace NLQCLean

/-- Monomial exponents of total degree at most D, including the constant. -/
def DegreeMonomial (n D : ℕ) :=
  {d : Fin n →₀ ℕ // d.sum (fun _ e => e) ≤ D}

namespace DegreeMonomial

theorem coordinate_le {n D : ℕ} (d : DegreeMonomial n D) (i : Fin n) : d.val i ≤ D := by
  apply le_trans _ d.property
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

noncomputable instance {n D : ℕ} : Fintype (DegreeMonomial n D) :=
  Fintype.ofInjective (fun d i => (⟨d.val i, Nat.lt_succ_of_le (coordinate_le d i)⟩ : Fin (D + 1)))
    (by
      intro d e h
      apply Subtype.ext
      ext i
      exact congrArg Fin.val (congrFun h i))

end DegreeMonomial

/-- Euclidean coordinates indexed by all monomials of bounded total degree. -/
abbrev PolynomialCoefficients (n D : ℕ) := EuclideanSpace ℝ (DegreeMonomial n D)

namespace PolynomialCoefficients

variable {n D : ℕ}

/-- Reconstruct a polynomial from its finite coefficient vector. -/
noncomputable def polynomial (c : PolynomialCoefficients n D) : MvPolynomial (Fin n) ℝ :=
  ∑ d : DegreeMonomial n D, MvPolynomial.monomial d.val (c d)

/-- Extract the degree-bounded coefficients of any polynomial. -/
noncomputable def ofPolynomial (p : MvPolynomial (Fin n) ℝ) : PolynomialCoefficients n D :=
  WithLp.toLp 2 (fun d => p.coeff d.val)

@[simp] theorem ofPolynomial_apply (p : MvPolynomial (Fin n) ℝ) (d : DegreeMonomial n D) :
    ofPolynomial p d = p.coeff d.val := rfl

theorem totalDegree_polynomial (c : PolynomialCoefficients n D) :
    c.polynomial.totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans d.property

@[simp] theorem coeff_polynomial (c : PolynomialCoefficients n D) (d : DegreeMonomial n D) :
    c.polynomial.coeff d.val = c d := by
  classical
  simp only [polynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ he
    exact ite_eq_right (fun h => he (Subtype.ext h))
  · simp

@[simp] theorem ofPolynomial_polynomial (c : PolynomialCoefficients n D) :
    ofPolynomial c.polynomial = c := by
  ext d
  exact coeff_polynomial c d

theorem polynomial_ofPolynomial (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) :
    (ofPolynomial (D := D) p).polynomial = p := by
  classical
  ext d
  by_cases hd : d.sum (fun _ e => e) ≤ D
  · exact coeff_polynomial (ofPolynomial p) ⟨d, hd⟩
  · have hz (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ D) :
        q.coeff d = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      exact lt_of_le_of_lt hq (Nat.lt_of_not_ge hd)
    rw [hz _ (totalDegree_polynomial _), hz _ hp]

theorem polynomial_injective : Function.Injective (polynomial (n := n) (D := D)) := by
  intro c e h
  simpa using congrArg (ofPolynomial (D := D)) h

@[simp] theorem polynomial_zero : (0 : PolynomialCoefficients n D).polynomial = 0 := by
  simp [polynomial]

@[simp] theorem polynomial_eq_zero_iff (c : PolynomialCoefficients n D) :
    c.polynomial = 0 ↔ c = 0 := by
  rw [← polynomial_zero]
  exact polynomial_injective.eq_iff

@[simp] theorem polynomial_smul (t : ℝ) (c : PolynomialCoefficients n D) :
    (t • c).polynomial = t • c.polynomial := by
  classical
  simp [polynomial, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- Joint evaluation in coefficient and Euclidean point coordinates. -/
noncomputable def evaluate (c : PolynomialCoefficients n D) (x : RealEuclidean n) : ℝ :=
  MvPolynomial.eval (fun i => x i) c.polynomial

theorem evaluate_eq (c : PolynomialCoefficients n D) (x : RealEuclidean n) :
    c.evaluate x = ∑ d : DegreeMonomial n D, c d * ∏ i : Fin n, x i ^ d.val i := by
  classical
  simp only [evaluate, polynomial, map_sum, MvPolynomial.eval_monomial]
  congr 1
  funext d
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

@[fun_prop] theorem continuous_evaluate :
    Continuous (fun z : PolynomialCoefficients n D × RealEuclidean n => z.1.evaluate z.2) := by
  simp only [evaluate_eq]
  fun_prop

@[simp] theorem evaluate_smul (t : ℝ) (c : PolynomialCoefficients n D) (x : RealEuclidean n) :
    (t • c).evaluate x = t * c.evaluate x := by
  simp [evaluate]

/-- Positive normalization; the zero vector remains zero. -/
noncomputable def normalize (c : PolynomialCoefficients n D) : PolynomialCoefficients n D :=
  ‖c‖⁻¹ • c

@[simp] theorem normalize_zero : normalize (0 : PolynomialCoefficients n D) = 0 := by
  simp [normalize]

theorem norm_normalize {c : PolynomialCoefficients n D} (hc : c ≠ 0) :
    ‖c.normalize‖ = 1 := by
  simp [normalize, norm_smul, norm_ne_zero_iff.mpr hc]

theorem normalize_ne_zero {c : PolynomialCoefficients n D} (hc : c ≠ 0) :
    c.normalize ≠ 0 := by
  intro h
  have := norm_normalize hc
  simp [h] at this

theorem sign_normalize (s : PolynomialSign) {c : PolynomialCoefficients n D}
    (hc : c ≠ 0) (x : RealEuclidean n) :
    s.Holds (c.normalize.evaluate x) ↔ s.Holds (c.evaluate x) := by
  have hpos : 0 < ‖c‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hc)
  rw [normalize, evaluate_smul]
  cases s <;> simp only [PolynomialSign.Holds]
  · constructor <;> intro h <;> nlinarith
  · exact mul_eq_zero.trans (or_iff_right (ne_of_gt hpos))
  · exact mul_pos_iff_of_pos_left hpos

theorem isCompact_unitSphere :
    IsCompact {c : PolynomialCoefficients n D | ‖c‖ = 1} := by
  simpa only [Metric.sphere, dist_zero_right] using
    (isCompact_sphere (0 : PolynomialCoefficients n D) 1)

end PolynomialCoefficients
end NLQCLean
end
