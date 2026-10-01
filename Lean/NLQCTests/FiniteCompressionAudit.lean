import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression

/-!
# finite classical compression and operational-error transfer

The full types preserve rank-based support, quantum message dimensions,
selected-outcome alphabets, target scores and fifth-power charged footprint.
Operational errors imply only a score transfer, not error preservation.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_resource_support_protocol

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_resource_support_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_resource_support_protocol

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.branchChannel_krausMap

/-- info: 'NLQCLean.ClassicalCommunication.branchChannel_krausMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.branchChannel_krausMap

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_eq_sum_outcomeChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_eq_sum_outcomeChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_eq_sum_outcomeChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_preserving_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_preserving_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_preserving_linearScore

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_bounded_outcomes_charged_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_bounded_outcomes_charged_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_bounded_outcomes_charged_linearScore

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_eq_coherentMixedChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_eq_coherentMixedChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_eq_coherentMixedChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError
