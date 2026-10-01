import NLQCLean.Exact.RationalInvariantPolynomial

/-! Full types and axioms of rational target-entry polynomial evaluation. -/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.rationalMatrixInvariant

set_option pp.universes true in
#check @NLQCLean.rationalMatrixCoordinates_targetCoordinates
#print axioms NLQCLean.rationalMatrixCoordinates_targetCoordinates

set_option pp.universes true in
#check @NLQCLean.targetInvariantPolynomial_evaluate
/-- info: 'NLQCLean.targetInvariantPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.targetInvariantPolynomial_evaluate

set_option pp.universes true in
#check @NLQCLean.contDiff_rationalMatrixInvariant
/-- info: 'NLQCLean.contDiff_rationalMatrixInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.contDiff_rationalMatrixInvariant
