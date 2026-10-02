import NLQCLean.Bounds.FiniteClassicalHaar

/-!
# Finite-shape free-classical quantitative transfers

Full types expose outer measure, finite
score classes, dimension factors and universal quantifier order.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_haar_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_haar_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_log_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_log_constant
