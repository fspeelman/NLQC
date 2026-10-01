import NLQCLean.Exact.RationalPolynomialSmoothness

/-! Arbitrary smoothness orders, minimal finite index assumptions and standard axioms. -/

open scoped ContDiff

set_option pp.universes true in
#check @NLQCLean.contDiff_mvPolynomial_eval_comp
set_option pp.universes true in
#check @NLQCLean.contDiff_mvPolynomial_eval_pi
set_option pp.universes true in
#check @NLQCLean.contDiff_mvPolynomial_eval_euclidean
set_option pp.universes true in
#check @NLQCLean.contDiff_mvPolynomial_eval_of_order
set_option pp.universes true in
#check @NLQCLean.contDiff_rationalMvPolynomial_eval_comp
set_option pp.universes true in
#check @NLQCLean.contDiff_rationalMvPolynomial_eval_euclidean
set_option pp.universes true in
#check @NLQCLean.contDiff_rationalMvPolynomial_eval_of_order
set_option pp.universes true in
#check @NLQCLean.contDiff_mvPolynomial_map_euclidean
set_option pp.universes true in
#check @NLQCLean.contDiff_polynomialMap_of_order
set_option pp.universes true in
#check @NLQCLean.contDiff_rationalMvPolynomial_map_euclidean

example {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ σ => MvPolynomial.eval (fun i => x i) p) :=
  NLQCLean.contDiff_mvPolynomial_eval_euclidean ∞ p

example {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℚ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ σ =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => x i) p) :=
  NLQCLean.contDiff_rationalMvPolynomial_eval_euclidean ∞ p

example {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ σ => MvPolynomial.eval (fun i => x i) p) :=
  NLQCLean.contDiff_mvPolynomial_eval_euclidean ⊤ p

/-- info: 'NLQCLean.contDiff_mvPolynomial_eval_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_mvPolynomial_eval_comp
/-- info: 'NLQCLean.contDiff_mvPolynomial_eval_of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_mvPolynomial_eval_of_order
/-- info: 'NLQCLean.contDiff_rationalMvPolynomial_eval_of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_rationalMvPolynomial_eval_of_order
/-- info: 'NLQCLean.contDiff_polynomialMap_of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_polynomialMap_of_order
/-- info: 'NLQCLean.contDiff_rationalMvPolynomial_map_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_rationalMvPolynomial_map_euclidean
