import NLQCLean.Exact.TargetWitnessPolynomial

/-! Full statements and standard-axiom checks for the actual target-witness equations. -/

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.ComplexPair.evaluateMatrix_vectorInsert
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetPolynomial_evaluate
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.witnessInsertPolynomial_evaluate
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.globalPolynomial_evaluate
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetPhysicalConstraintPolynomial_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetWitnessConstraintPolynomial_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetCoisometryConstraintPolynomial_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetFrozenConstraintPolynomial_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetConstraintPolynomial_eval_eq_zero_iff
set_option pp.universes true in
#check @NLQCLean.ExactWitnessPolynomial.targetPurityPolynomial_evaluate

/-- info: 'NLQCLean.ExactWitnessPolynomial.globalPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessPolynomial.globalPolynomial_evaluate

/-- info: 'NLQCLean.ExactWitnessPolynomial.targetConstraintPolynomial_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessPolynomial.targetConstraintPolynomial_eval_eq_zero_iff

/-- info: 'NLQCLean.ExactWitnessPolynomial.targetPurityPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessPolynomial.targetPurityPolynomial_evaluate

open NLQCLean NLQCLean.ExactWitnessCoordinates NLQCLean.ExactWitnessPolynomial

example (d : ℕ) (s : ForwardShape) (y : Blocks d s) :
    (∀ i, PhysicalPolynomial.eval (coordinatesEquiv d s y)
      (targetConstraintPolynomial d s i) = 0) ↔ y ∈ targetExactWitnessSet d s := by
  simpa using targetConstraintPolynomial_eval_eq_zero_iff d s (coordinatesEquiv d s y)

example (d : ℕ) (s : ForwardShape) (y : Blocks d s) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (coordinatesEquiv d s y)
      (targetPurityPolynomial d s) = purity ((d : ℝ) ^ 4)⁻¹ y.1 := by
  simpa using targetPurityPolynomial_evaluate d s (coordinatesEquiv d s y)
