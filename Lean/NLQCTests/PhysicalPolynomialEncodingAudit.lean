import NLQCLean.Arithmetic.PhysicalPolynomialEncoding

/-! # five-block integer physical-constraint encoding -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalCoordinatesEquiv

/-- info: 'NLQCLean.PhysicalPolynomial.physicalCoordinatesEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalCoordinatesEquiv

#check @NLQCLean.PhysicalPolynomial.card_physicalCoordinateIndex

/-- info: 'NLQCLean.PhysicalPolynomial.card_physicalCoordinateIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.card_physicalCoordinateIndex

#check @NLQCLean.PhysicalPolynomial.physicalConstraintPolynomial_degree_le
#check @NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_degree_le

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_eq_zero_iff

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_eq_zero_iff

#check @NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_coordinates_eq_zero_iff

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_coordinates_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_eval_coordinates_eq_zero_iff

example : Fintype.card (NLQCLean.PhysicalPolynomial.PhysicalCoordinateIndex 0 (fun _ => 0)) = 0 := by
  rw [NLQCLean.PhysicalPolynomial.card_physicalCoordinateIndex]
  norm_num [NLQCLean.physicalRawRealCoordinateCount]

example : NLQCLean.PhysicalPolynomial.unitResourceConstraint
    (σ := Unit) (ε := Fin 0) (fun _ => ()) = -1 := by
  simp [NLQCLean.PhysicalPolynomial.unitResourceConstraint]
