import NLQCLean.Arithmetic.ControlledPhaseScorePolynomial

/-! # Two phase coordinates and exact denominator sixteen -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.totalDegree_bind₁_le_of_linear_variables

/-- info: 'NLQCLean.PhysicalPolynomial.totalDegree_bind₁_le_of_linear_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.totalDegree_bind₁_le_of_linear_variables

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.card_phaseScoreCoordinateIndex

/-- info: 'NLQCLean.PhysicalPolynomial.card_phaseScoreCoordinateIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.card_phaseScoreCoordinateIndex

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_degree_le

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate_angle

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_evaluate_angle
