import NLQCLean.Exact.FiniteExactRestriction

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

/-! Full logical/internal register universes and explicit ideal equations for exact restriction. -/

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol_arbitrary_logical
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_exact_local_restriction
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_exact_local_restriction

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_exact_local_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_exact_local_restriction
/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_exact_local_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_exact_local_restriction
