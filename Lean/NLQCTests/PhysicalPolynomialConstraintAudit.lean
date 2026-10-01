import NLQCLean.Arithmetic.PhysicalPolynomialConstraints

/-! # Integer normalization/isometry equations and their sum of squares -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.unitResourceConstraint_eval_eq_zero_iff
#check @NLQCLean.PhysicalPolynomial.unitResourceConstraint_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.unitResourceConstraint_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.unitResourceConstraint_eval_eq_zero_iff

#check @NLQCLean.PhysicalPolynomial.isometryRealConstraint_eval
#check @NLQCLean.PhysicalPolynomial.isometryImagConstraint_eval
set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.isometryConstraints_eval_eq_zero_iff
#check @NLQCLean.PhysicalPolynomial.isometryRealConstraint_degree_le
#check @NLQCLean.PhysicalPolynomial.isometryImagConstraint_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.isometryConstraints_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.isometryConstraints_eval_eq_zero_iff

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.constraintSumSquares_eval_eq_zero_iff

/-- info: 'NLQCLean.PhysicalPolynomial.constraintSumSquares_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.constraintSumSquares_eval_eq_zero_iff

#check @NLQCLean.PhysicalPolynomial.constraintSumSquares_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.constraintSumSquares_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.constraintSumSquares_degree_le
