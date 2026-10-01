import NLQCLean.Models.ClassicalCommunication.BorelRankCompression

/-! # Rank-sized compression and original-error adapters for pure Borel protocols -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_bounded_outcomes_charged_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_bounded_outcomes_charged_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_bounded_outcomes_charged_linearScore

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_operationalChannel_eq_one

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_operationalChannel_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.trace_choiMatrix_operationalChannel_eq_one

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_le_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_le_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scoreU_le_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_quantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.isPVMOutcomeChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_le_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_le_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.one_sub_scorePVM_le_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_quantumFootprint_pvmTVError

/-! The protocol arguments retain arbitrary original finite resource,
quantum-message and local workspace types, and arbitrary standard-Borel
outcome spaces. The selected finite resource spaces use the original
Schmidt rank, both final alphabets are bounded by `(d * rank) ^ 2 + 1`,
and the charged budget is `4 * d ^ 4 * K ^ 5`. Operational error enters
through the original-channel score inequality before compression. -/
