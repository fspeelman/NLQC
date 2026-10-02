import NLQCLean.Bounds.FiniteClassicalQubits

/-! # Quantum-footprint qubit forms, not initial-resource qubits -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.quantumFootprint_log_of_tenth_power_bound

/-- info: 'NLQCLean.ClassicalCommunication.quantumFootprint_log_of_tenth_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.quantumFootprint_log_of_tenth_power_bound

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_qubit_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_qubit_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_unitary_universal_qubit_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_qubit_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_qubit_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_pvm_universal_qubit_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_qubit_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_qubit_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_classical_strong_unitary_universal_qubit_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_ae_finite_classical_qubit_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_ae_finite_classical_qubit_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_ae_finite_classical_qubit_constant
