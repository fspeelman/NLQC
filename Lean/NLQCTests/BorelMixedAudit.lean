import NLQCLean.Models.ClassicalCommunication.BorelMixedCompression

/-! # Actual common-map mixed Borel channels, component selection and original-error adapters -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.withResource

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.componentProtocol_localMaps

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.hasMixedQuantumFootprint_iff_rank_bound

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_single

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.hasMixedQuantumFootprint_iff_componentwise

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedOperationalChannel_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_hasQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_of_rank_cost

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_of_rank_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_linearScore_ge_of_rank_cost

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_bounded_outcomes_charged_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_bounded_outcomes_charged_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_component_bounded_outcomes_charged_linearScore

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_mixedOperationalChannel_eq_one

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_mixedOperationalChannel_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_mixedOperationalChannel_eq_one

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_mixedOperationalChannel_le_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_mixedOperationalChannel_le_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_mixedOperationalChannel_le_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedQuantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel_mixedOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel_mixedOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel_mixedOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_mixedOperationalChannel_le_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_mixedOperationalChannel_le_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_mixedOperationalChannel_le_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedQuantumFootprint_pvmTVError

/-! Common maps are retained before selecting a resource component.
The mixed cap bounds each Schmidt rank and the two quantum messages,
including zero-weight components. Finite score selection preserves the
cap and does not assert equality of channels or operational errors.
Original diamond and joint-TV hypotheses concern the actual averaged
Borel channel. Arbitrary shared randomness is a separate extension. -/
