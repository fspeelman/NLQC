import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Removing the maximal second-variable factor from an integer polynomial

The outer polynomial variable is `y`; its coefficients are integer
polynomials in `x`. Bounds are stated on the integer coefficients.
No elimination or transcendence hypothesis is used here.
-/

namespace NLQCLean

open Polynomial
open scoped BigOperators

abbrev IntBivariatePolynomial := Polynomial (Polynomial ℤ)

/-- Evaluation of an integer polynomial at a real point. -/
noncomputable def integerPolynomialEval (P : Polynomial ℤ) (x : ℝ) : ℝ :=
  P.eval₂ (Int.castRingHom ℝ) x

/-- The first argument is the inner variable and the second the outer one. -/
noncomputable def bivariateEval (Q : IntBivariatePolynomial) (c g : ℝ) : ℝ :=
  Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) c) g

/-- Separate bounds on both degrees, weaker than a total-degree bound. -/
def BivariateDegreeLE (Q : IntBivariatePolynomial) (L : ℕ) : Prop :=
  Q.natDegree ≤ L ∧ ∀ j, (Q.coeff j).natDegree ≤ L

/-- Height bounds every integer coefficient, including coefficients outside support. -/
def BivariateHeightLE (Q : IntBivariatePolynomial) (H : ℝ) : Prop :=
  ∀ j i, |((Q.coeff j).coeff i : ℝ)| ≤ H

/-- Repeated exact removal of the lowest power of the outer variable. -/
noncomputable def divideYPower (k : ℕ) (Q : IntBivariatePolynomial) : IntBivariatePolynomial :=
  (Polynomial.divX^[k]) Q

theorem divideYPower_coeff (k : ℕ) (Q : IntBivariatePolynomial) (j : ℕ) :
    (divideYPower k Q).coeff j = Q.coeff (j + k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [divideYPower, Function.iterate_succ_apply', Polynomial.coeff_divX]
    change (divideYPower k Q).coeff (j + 1) = _
    rw [ih]
    congr 1
    omega

theorem divideYPower_natDegree_le (k : ℕ) (Q : IntBivariatePolynomial) :
    (divideYPower k Q).natDegree ≤ Q.natDegree := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change ((Polynomial.divX^[k + 1]) Q).natDegree ≤ _
    rw [Function.iterate_succ_apply']
    exact Polynomial.natDegree_divX_le.trans ih

theorem divideYPower_factorization (k : ℕ) (Q : IntBivariatePolynomial)
    (hzero : ∀ j < k, Q.coeff j = 0) :
    (Polynomial.X : IntBivariatePolynomial) ^ k * divideYPower k Q = Q := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hj
  · rw [divideYPower_coeff, Nat.sub_add_cancel hj]
  · exact (hzero j (by omega)).symm

/-- Divide by exactly the maximal outer-variable power of a nonzero polynomial. -/
noncomputable def yPrimitive (Q : IntBivariatePolynomial) : IntBivariatePolynomial :=
  divideYPower Q.natTrailingDegree Q

theorem yPrimitive_factorization (Q : IntBivariatePolynomial) :
    (Polynomial.X : IntBivariatePolynomial) ^ Q.natTrailingDegree * yPrimitive Q = Q :=
  divideYPower_factorization _ Q (fun _ hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj)

theorem yPrimitive_constant_ne_zero {Q : IntBivariatePolynomial} (hQ : Q ≠ 0) :
    (yPrimitive Q).coeff 0 ≠ 0 := by
  rw [yPrimitive, divideYPower_coeff, zero_add]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQ

theorem yPrimitive_maximal {Q : IntBivariatePolynomial} (hQ : Q ≠ 0) :
    ¬ (Polynomial.X : IntBivariatePolynomial) ^ (Q.natTrailingDegree + 1) ∣ Q := by
  intro hdvd
  have hz := Polynomial.X_pow_dvd_iff.mp hdvd Q.natTrailingDegree (by omega)
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQ) hz

theorem yPrimitive_degreeLE {Q : IntBivariatePolynomial} {L : ℕ}
    (hQ : BivariateDegreeLE Q L) : BivariateDegreeLE (yPrimitive Q) L := by
  refine ⟨(divideYPower_natDegree_le _ Q).trans hQ.1, ?_⟩
  intro j
  rw [yPrimitive, divideYPower_coeff]
  exact hQ.2 _

theorem yPrimitive_heightLE {Q : IntBivariatePolynomial} {H : ℝ}
    (hQ : BivariateHeightLE Q H) : BivariateHeightLE (yPrimitive Q) H := by
  intro j i
  rw [yPrimitive, divideYPower_coeff]
  exact hQ _ _

theorem yPrimitive_eval_eq_zero {Q : IntBivariatePolynomial} {c g : ℝ}
    (hg : g ≠ 0) (hQ : bivariateEval Q c g = 0) : bivariateEval (yPrimitive Q) c g = 0 := by
  have h := congrArg (fun R => bivariateEval R c g) (yPrimitive_factorization Q)
  simp only [bivariateEval, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X] at h
  change g ^ Q.natTrailingDegree * bivariateEval (yPrimitive Q) c g = bivariateEval Q c g at h
  rw [hQ] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hg)

/-- Finite coefficient sums bound a univariate integer polynomial on `[-1,1]`. -/
theorem abs_integerPolynomialEval_le {P : Polynomial ℤ} {L : ℕ} {H c : ℝ}
    (hdegree : P.natDegree ≤ L) (hH : 0 ≤ H)
    (hheight : ∀ i, |(P.coeff i : ℝ)| ≤ H) (hc : |c| ≤ 1) :
    |integerPolynomialEval P c| ≤ (L + 1 : ℕ) * H := by
  rw [integerPolynomialEval, Polynomial.eval₂_eq_sum_range' _ (n := L + 1) (by omega)]
  calc
    _ ≤ ∑ i ∈ Finset.range (L + 1), |(P.coeff i : ℝ) * c ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (L + 1), H := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact (mul_le_mul (hheight i) (pow_le_one₀ (abs_nonneg _) hc)
        (by positivity) hH).trans_eq (mul_one H)
    _ = _ := by simp

theorem abs_zero_pow_sub_le {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (j : ℕ) :
    |(0 : ℝ) ^ j - g ^ j| ≤ g := by
  cases j with
  | zero => simp [hg0]
  | succ j =>
    rw [zero_pow (by omega), zero_sub, abs_neg, abs_of_nonneg (pow_nonneg hg0 _), pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hg0 hg1) hg0).trans_eq (one_mul _)

/-- Vanishing at positive `y=g` bounds the constant-in-y value by a direct
coefficient sum. The cubic bound retains the source's chosen normalization. -/
theorem bivariate_zero_constant_bound {Q : IntBivariatePolynomial} {L : ℕ} {H c g : ℝ}
    (hdegree : BivariateDegreeLE Q L) (hH : 0 ≤ H) (hheight : BivariateHeightLE Q H)
    (hc : |c| ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hzero : bivariateEval Q c g = 0) :
    |integerPolynomialEval (Q.coeff 0) c| ≤ g * (L + 1 : ℕ) ^ 3 * H := by
  have he : integerPolynomialEval (Q.coeff 0) c = bivariateEval Q c 0 := by
    simp [bivariateEval, integerPolynomialEval]
  have hd : Q.natDegree ≤ L := hdegree.1
  have hdiff : integerPolynomialEval (Q.coeff 0) c =
      bivariateEval Q c 0 - bivariateEval Q c g := by rw [hzero, sub_zero, ← he]
  rw [hdiff]
  rw [bivariateEval, bivariateEval,
    Polynomial.eval₂_eq_sum_range' _ (by omega : Q.natDegree < L + 1),
    Polynomial.eval₂_eq_sum_range' _ (by omega : Q.natDegree < L + 1),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range (L + 1),
        |integerPolynomialEval (Q.coeff j) c * ((0 : ℝ) ^ j - g ^ j)| := by
      simpa only [integerPolynomialEval, Polynomial.coe_eval₂RingHom, mul_sub]
        using Finset.abs_sum_le_sum_abs
          (fun j => integerPolynomialEval (Q.coeff j) c * ((0 : ℝ) ^ j - g ^ j))
          (Finset.range (L + 1))
    _ ≤ ∑ _j ∈ Finset.range (L + 1), ((L + 1 : ℕ) * H) * g := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (abs_integerPolynomialEval_le (hdegree.2 j) hH (hheight j) hc)
        (abs_zero_pow_sub_le hg0 hg1 j) (abs_nonneg _) (by positivity)
    _ = g * (L + 1 : ℕ) ^ 2 * H := by simp; ring
    _ ≤ _ := by
      have hL : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_pos L)
      have hp := pow_le_pow_right₀ hL (by decide : 2 ≤ 3)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hg0) hH

/-- The maximal-factor quotient supplies the source's boundary-value certificate. -/
theorem bivariate_primitive_root_certificate {Q : IntBivariatePolynomial}
    {L : ℕ} {H c g : ℝ} (hQ : Q ≠ 0) (hdegree : BivariateDegreeLE Q L)
    (hH : 1 ≤ H) (hheight : BivariateHeightLE Q H) (hc : |c| ≤ 1)
    (hg0 : 0 < g) (hg1 : g ≤ 1) (hzero : bivariateEval Q c g = 0) :
    (yPrimitive Q).coeff 0 ≠ 0 ∧
      ((yPrimitive Q).coeff 0).natDegree ≤ L ∧
      (∀ i, |(((yPrimitive Q).coeff 0).coeff i : ℝ)| ≤ H) ∧
      |integerPolynomialEval ((yPrimitive Q).coeff 0) c| ≤ g * (L + 1 : ℕ) ^ 3 * H := by
  have hd := yPrimitive_degreeLE hdegree
  have hh := yPrimitive_heightLE hheight
  exact ⟨yPrimitive_constant_ne_zero hQ, hd.2 0, hh 0,
    bivariate_zero_constant_bound hd (by linarith) hh hc hg0.le hg1
      (yPrimitive_eval_eq_zero hg0.ne' hzero)⟩

/-- Convert a two-variable integer polynomial to the iterated polynomial ring.
Index zero becomes the outer `y` variable; index one becomes the inner `x` variable. -/
noncomputable def bivariateOfMv : MvPolynomial (Fin 2) ℤ →+* IntBivariatePolynomial :=
  (Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).toRingHom).comp
    (MvPolynomial.finSuccEquiv ℤ 1).toRingHom

theorem bivariateOfMv_coeff (Q : MvPolynomial (Fin 2) ℤ) (j i : ℕ) :
    ((bivariateOfMv Q).coeff j).coeff i =
      MvPolynomial.coeff (Finsupp.cons j (Finsupp.single (0 : Fin 1) i)) Q := by
  change ((((MvPolynomial.finSuccEquiv ℤ 1) Q).map
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).toRingHom).coeff j).coeff i = _
  rw [Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1))
    (((MvPolynomial.finSuccEquiv ℤ 1) Q).coeff j)).coeff i = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.finSuccEquiv_coeff_coeff]
  rfl

theorem bivariateOfMv_ne_zero {Q : MvPolynomial (Fin 2) ℤ} (hQ : Q ≠ 0) :
    bivariateOfMv Q ≠ 0 := by
  intro hz
  have he : ((MvPolynomial.finSuccEquiv ℤ 1) Q).map
      (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).toRingHom = 0 := hz
  have h := (Polynomial.map_eq_zero_iff (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).injective).mp he
  apply hQ
  exact (MvPolynomial.finSuccEquiv ℤ 1).injective (by simpa using h)

theorem bivariateOfMv_degreeLE {Q : MvPolynomial (Fin 2) ℤ} {L : ℕ}
    (hdegree : Q.totalDegree ≤ L) : BivariateDegreeLE (bivariateOfMv Q) L := by
  constructor
  · change (((MvPolynomial.finSuccEquiv ℤ 1) Q).map
      (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).toRingHom).natDegree ≤ L
    exact Polynomial.natDegree_map_le.trans
      ((MvPolynomial.natDegree_finSuccEquiv Q).le.trans
        ((MvPolynomial.degreeOf_le_totalDegree Q 0).trans hdegree))
  · intro j
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [bivariateOfMv_coeff]
    by_contra hn
    have hm := MvPolynomial.mem_support_iff.mpr hn
    have h := (MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 2) hm).trans
      ((MvPolynomial.degreeOf_le_totalDegree Q 1).trans hdegree)
    change (Finsupp.cons j (Finsupp.single (0 : Fin 1) i)) (0 : Fin 1).succ ≤ L at h
    rw [Finsupp.cons_succ, Finsupp.single_eq_same] at h
    omega

theorem bivariateOfMv_heightLE {Q : MvPolynomial (Fin 2) ℤ} {H : ℝ}
    (hheight : ∀ m, |((MvPolynomial.coeff m Q : ℤ) : ℝ)| ≤ H) :
    BivariateHeightLE (bivariateOfMv Q) H := by
  intro j i
  rw [bivariateOfMv_coeff]
  exact hheight _

theorem bivariateEval_bivariateOfMv (Q : MvPolynomial (Fin 2) ℤ) (c g : ℝ) :
    bivariateEval (bivariateOfMv Q) c g =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons g (fun _ : Fin 1 => c)) Q := by
  have hr : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℝ) c) g).comp
      bivariateOfMv =
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons g (fun _ : Fin 1 => c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [bivariateOfMv, MvPolynomial.uniqueAlgEquiv]
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [bivariateOfMv, MvPolynomial.finSuccEquiv_X_zero]
      · simp [bivariateOfMv, MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.uniqueAlgEquiv]
  exact RingHom.congr_fun hr Q

end NLQCLean
