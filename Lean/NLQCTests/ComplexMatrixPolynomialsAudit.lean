import NLQCLean.Arithmetic.ComplexMatrixPolynomials

/-! Full statements and standard-axiom checks for integer complex-matrix polynomials. -/

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluate_constant
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluate_subtract
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.eval_realPart
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.eval_imagPart
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluateMatrix_matrixIdentity
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluateMatrix_matrixConjTranspose
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluateMatrix_matrixRealign
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluateMatrix_submatrix
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluate_matrixTrace
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.eval_purityNumerator
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.purity_evaluateMatrix
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.eval_matrixEqualityConstraint
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.matrixIsometryConstraint_eval_eq_zero_iff

/-- info: 'NLQCLean.PhysicalPolynomial.ComplexPair.purity_evaluateMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.ComplexPair.purity_evaluateMatrix

/-- info: 'NLQCLean.PhysicalPolynomial.ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff

/-- info: 'NLQCLean.PhysicalPolynomial.ComplexPair.matrixIsometryConstraint_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.ComplexPair.matrixIsometryConstraint_eval_eq_zero_iff

open NLQCLean.PhysicalPolynomial

example {σ ι : Type*} [Fintype ι] (c : ℝ) (x : σ → ℝ)
    (P : Matrix (ι × ι) (ι × ι) (ComplexPair σ)) :
    NLQCLean.purity c (ComplexPair.evaluateMatrix x P) =
      c * eval x (ComplexPair.purityNumerator P) :=
  ComplexPair.purity_evaluateMatrix c x P

example {σ m n : Type*} [Fintype m] [Fintype n] (x : σ → ℝ)
    (P Q : Matrix m n (ComplexPair σ)) :
    eval x (ComplexPair.matrixEqualityConstraint P Q) = 0 ↔
      ComplexPair.evaluateMatrix x P = ComplexPair.evaluateMatrix x Q :=
  ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff x P Q

example {σ m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (x : σ → ℝ)
    (P : Matrix m n (ComplexPair σ)) :
    eval x (ComplexPair.matrixIsometryConstraint P) = 0 ↔
      NLQCLean.IsIsometry (ComplexPair.evaluateMatrix x P) :=
  ComplexPair.matrixIsometryConstraint_eval_eq_zero_iff x P
