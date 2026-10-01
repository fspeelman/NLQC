import NLQCLean.Semialgebraic.Format
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smoothness of rational and real polynomial evaluation

Polynomial evaluation is differentiable to every order, including smooth
infinity and analytic top. The substitution theorem only asks that each
coordinate function be smooth and does not require the variable index to be
finite. The finite-coordinate and Euclidean wrappers require only `Fintype`.
Rational coefficients are evaluated through the actual coefficient map to ℝ.
-/

namespace NLQCLean

universe u v w

open scoped ContDiff

/-- Coordinatewise smooth substitution into an arbitrary real multivariate
polynomial is smooth to the same order. There is no finiteness or decidable
equality assumption on the polynomial's variable index. -/
@[fun_prop] theorem contDiff_mvPolynomial_eval_comp
    {σ : Type u} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {order : WithTop ℕ∞} {f : E → σ → ℝ}
    (hf : ∀ i, ContDiff ℝ order (fun x => f x i)) (p : MvPolynomial σ ℝ) :
    ContDiff ℝ order (fun x => MvPolynomial.eval (f x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ order (fun _ : E => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hf i)

/-- Polynomial evaluation on finite scalar coordinate functions, at every
smoothness order and with no decidable equality assumption. -/
@[fun_prop] theorem contDiff_mvPolynomial_eval_pi
    {σ : Type u} [Fintype σ] (order : WithTop ℕ∞) (p : MvPolynomial σ ℝ) :
    ContDiff ℝ order (fun x : σ → ℝ => MvPolynomial.eval x p) :=
  contDiff_mvPolynomial_eval_comp (fun i => contDiff_apply ℝ ℝ i) p

/-- Polynomial evaluation on Euclidean space with arbitrary finite indices. -/
@[fun_prop] theorem contDiff_mvPolynomial_eval_euclidean
    {σ : Type u} [Fintype σ] (order : WithTop ℕ∞) (p : MvPolynomial σ ℝ) :
    ContDiff ℝ order (fun x : EuclideanSpace ℝ σ => MvPolynomial.eval (fun i => x i) p) :=
  contDiff_mvPolynomial_eval_comp (fun i => contDiff_piLp_apply 2 (i := i)) p

/-- The `RealEuclidean` form of polynomial evaluation, generalized from
order one to every order. -/
@[fun_prop] theorem contDiff_mvPolynomial_eval_of_order
    {d : ℕ} (order : WithTop ℕ∞) (p : MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ order (fun x : RealEuclidean d => MvPolynomial.eval (fun i => x i) p) :=
  contDiff_mvPolynomial_eval_euclidean order p

/-- Rational polynomials evaluated over ℝ after coordinatewise smooth
substitution. The coefficient map is explicit. -/
@[fun_prop] theorem contDiff_rationalMvPolynomial_eval_comp
    {σ : Type u} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {order : WithTop ℕ∞} {f : E → σ → ℝ}
    (hf : ∀ i, ContDiff ℝ order (fun x => f x i)) (p : MvPolynomial σ ℚ) :
    ContDiff ℝ order (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (f x) p) := by
  simpa only [MvPolynomial.eval₂_eq_eval_map] using
    contDiff_mvPolynomial_eval_comp hf (MvPolynomial.map (algebraMap ℚ ℝ) p)

/-- Rational polynomial evaluation on arbitrary finite Euclidean indices. -/
@[fun_prop] theorem contDiff_rationalMvPolynomial_eval_euclidean
    {σ : Type u} [Fintype σ] (order : WithTop ℕ∞) (p : MvPolynomial σ ℚ) :
    ContDiff ℝ order (fun x : EuclideanSpace ℝ σ =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => x i) p) :=
  contDiff_rationalMvPolynomial_eval_comp (fun i => contDiff_piLp_apply 2 (i := i)) p

/-- The rational coefficient form on the actual `RealEuclidean` type. -/
@[fun_prop] theorem contDiff_rationalMvPolynomial_eval_of_order
    {d : ℕ} (order : WithTop ℕ∞) (p : MvPolynomial (Fin d) ℚ) :
    ContDiff ℝ order (fun x : RealEuclidean d =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => x i) p) :=
  contDiff_rationalMvPolynomial_eval_euclidean order p

/-- A finite family of real coordinate polynomials gives a smooth Euclidean
map, with independently universe-polymorphic source and target indices. -/
@[fun_prop] theorem contDiff_mvPolynomial_map_euclidean
    {σ : Type u} {τ : Type w} [Fintype σ] [Fintype τ]
    (order : WithTop ℕ∞) (q : τ → MvPolynomial σ ℝ) :
    ContDiff ℝ order (fun x : EuclideanSpace ℝ σ =>
      WithLp.toLp 2 (fun j => MvPolynomial.eval (fun i => x i) (q j))) := by
  apply (contDiff_piLp 2).2
  intro j
  exact contDiff_mvPolynomial_eval_euclidean order (q j)

/-- Every smoothness order for the existing polynomial-map presentation. -/
@[fun_prop] theorem contDiff_polynomialMap_of_order
    {d e : ℕ} (order : WithTop ℕ∞) (q : Fin e → MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ order (PolynomialSignDNF.polynomialMap q) :=
  contDiff_mvPolynomial_map_euclidean order q

/-- A finite rational polynomial map is smooth after extending its actual
coefficients to ℝ. Source and target index universes are independent. -/
@[fun_prop] theorem contDiff_rationalMvPolynomial_map_euclidean
    {σ : Type u} {τ : Type w} [Fintype σ] [Fintype τ]
    (order : WithTop ℕ∞) (q : τ → MvPolynomial σ ℚ) :
    ContDiff ℝ order (fun x : EuclideanSpace ℝ σ =>
      WithLp.toLp 2 (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => x i) (q j))) := by
  apply (contDiff_piLp 2).2
  intro j
  exact contDiff_rationalMvPolynomial_eval_euclidean order (q j)

end NLQCLean
