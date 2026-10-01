import NLQCLean.Exact.ExactPurityAlgebraicity

/-! Full statements and axioms for actual finite-architecture purity algebraicity. -/

set_option pp.universes true in
#check @NLQCLean.rationalSemialgebraic_exactWitnessCoordinateSet
set_option pp.universes true in
#check @NLQCLean.exactWitnessPurityMap_apply
set_option pp.universes true in
#check @NLQCLean.exactWitnessPurityMap_image
set_option pp.universes true in
#check @NLQCLean.rationalSemialgebraic_shapePurityValues
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_of_mem_shapePurityValues
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_of_mem_exactPurityValues
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_int_of_mem_exactPurityValues

/-- info: 'NLQCLean.rationalSemialgebraic_shapePurityValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rationalSemialgebraic_shapePurityValues
/-- info: 'NLQCLean.isAlgebraic_of_mem_exactPurityValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isAlgebraic_of_mem_exactPurityValues
/-- info: 'NLQCLean.isAlgebraic_int_of_mem_exactPurityValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isAlgebraic_int_of_mem_exactPurityValues

example (d : ℕ) {t : ℝ} (ht : t ∈ NLQCLean.exactPurityValues d) :
    IsAlgebraic ℚ t := NLQCLean.isAlgebraic_of_mem_exactPurityValues d ht

set_option pp.universes true in
#check @NLQCLean.RationalSemialgebraic.polynomial_zero_int
/-- info: 'NLQCLean.RationalSemialgebraic.polynomial_zero_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.polynomial_zero_int
