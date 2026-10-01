import NLQCLean.Models.ClassicalCommunication.DensityScoreFunctionals

/-! # Continuity is derived for original operation score functionals -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.continuousMatrixOperationRealScore

/-- info: 'NLQCLean.ClassicalCommunication.continuousMatrixOperationRealScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.continuousMatrixOperationRealScore
