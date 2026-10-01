import NLQCLean.Bounds.FiniteClassicalHaar

/-!
# Finite-shape free-classical quantitative transfers

Full types expose the three geometry premises, outer measure, finite
score classes, dimension factors and universal quantifier order.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant_of_external
