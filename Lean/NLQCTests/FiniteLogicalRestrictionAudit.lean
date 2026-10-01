import NLQCLean.Models.ClassicalCommunication.FiniteLogicalRestriction

/-! # pure and common-map mixed logical-input protocol restrictions -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_resource
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_hasQuantumFootprint_iff

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_hasQuantumFootprint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_hasQuantumFootprint_iff

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_operationalChannel

#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_hasMixedQuantumFootprint_iff
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_componentProtocol
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_mixedOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_mixedOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.precomposeLogicalInputs_mixedOperationalChannel
