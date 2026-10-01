import NLQCLean.Models.ClassicalCommunication.BorelSharedRandomness

/-! # Original averaged Borel channels and branchwise cap-preserving score transfer -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_completelyPositive_tracePreserving_family

/-- info: 'NLQCLean.ClassicalCommunication.integrable_completelyPositive_tracePreserving_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_completelyPositive_tracePreserving_family

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_measurable_completelyPositive_tracePreserving_family

/-- info: 'NLQCLean.ClassicalCommunication.integrable_measurable_completelyPositive_tracePreserving_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_measurable_completelyPositive_tracePreserving_family

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_linearScore_completelyPositive_tracePreserving_family

/-- info: 'NLQCLean.ClassicalCommunication.integrable_linearScore_completelyPositive_tracePreserving_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_linearScore_completelyPositive_tracePreserving_family

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.averageOperationalChannel_apply

/-- info: 'NLQCLean.ClassicalCommunication.averageOperationalChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.averageOperationalChannel_apply

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.linearScore_averageOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.linearScore_averageOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.linearScore_averageOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.averageOperationalChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.averageOperationalChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.averageOperationalChannel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.averageOperationalChannel_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.averageOperationalChannel_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.averageOperationalChannel_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.one_sub_scoreU_averageOperationalChannel_le_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.one_sub_scoreU_averageOperationalChannel_le_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.one_sub_scoreU_averageOperationalChannel_le_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.isPVMOutcomeChannel_averageOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.isPVMOutcomeChannel_averageOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.isPVMOutcomeChannel_averageOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.one_sub_scorePVM_averageOperationalChannel_le_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.one_sub_scorePVM_averageOperationalChannel_le_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.one_sub_scorePVM_averageOperationalChannel_le_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_sharedRandom_channelFamily

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_sharedRandom_channelFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_sharedRandom_channelFamily

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_apply

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_apply

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_sharedRandomOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_sharedRandomOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_sharedRandomOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandomOperationalChannel_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_sharedRandom_branch_linearScore_ge_hasQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_mixedSharedRandom_channelFamily

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_mixedSharedRandom_channelFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_mixedSharedRandom_channelFamily

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_apply

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_apply

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedSharedRandomOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedSharedRandomOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_mixedSharedRandomOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandomOperationalChannel_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_mixedSharedRandom_branch_component_linearScore_ge_hasQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_sharedRandom_quantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_sharedRandom_quantumFootprint_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_pureReachable_of_mixedSharedRandom_quantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mem_purePVMReachable_of_mixedSharedRandom_quantumFootprint_pvmTVError

/-! Full types quantify over dependent original finite resource,
quantum-message and workspace registers and over dependent standard-Borel
outcome spaces. Mixed component counts also vary with the randomness
branch. Channel and score integrability are derived from the measured
actual CP/TP family; the footprint cap is almost-everywhere branchwise.
The original averaged diamond/joint-TV errors are converted before
high-score branch or common-map component selection. -/
