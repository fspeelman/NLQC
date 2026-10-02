import NLQCLean.Models.ClassicalCommunication.BorelChannelNormalization

/-! # Derived complete positivity and trace preservation of Borel operational channels -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.isClosed_posSemidef_set

/-- info: 'NLQCLean.ClassicalCommunication.isClosed_posSemidef_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.isClosed_posSemidef_set

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.convex_posSemidef_set

/-- info: 'NLQCLean.ClassicalCommunication.convex_posSemidef_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.convex_posSemidef_set

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.posSemidef_integral

/-- info: 'NLQCLean.ClassicalCommunication.posSemidef_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.posSemidef_integral

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.completelyPositive_integral

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_integral

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_tensorContinuousChannels_prod

/-- info: 'NLQCLean.ClassicalCommunication.integrable_tensorContinuousChannels_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_tensorContinuousChannels_prod

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integral_tensorContinuousChannels_prod

/-- info: 'NLQCLean.ClassicalCommunication.integral_tensorContinuousChannels_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integral_tensorContinuousChannels_prod

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationDensity_ae_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationDensity_ae_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationDensity_ae_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_tracePreserving
