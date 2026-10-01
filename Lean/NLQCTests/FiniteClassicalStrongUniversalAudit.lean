import NLQCLean.Bounds.FiniteClassicalStrongUniversal

/-! # Improved unitary universal finite-shape dimension factor -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_log_constant_of_external
