import NLQCLean.Bounds.ArbitraryFiniteClassicalAlmostEvery

/-! # Target threshold preceding all original registers, scores and errors -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#print NLQCLean.ClassicalCommunication.AllFiniteClassicalLogBound

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound

/-- info: 'NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant_of_imageVolumeBound

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_ae_arbitrary_finite_classical_log_constant
