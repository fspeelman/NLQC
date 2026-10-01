import NLQCLean.Models.ClassicalCommunication.JointDensityChannels

/-! # measurable joint scores and derived integrability -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.tensorContinuousChannelsRealBilinear

/-- info: 'NLQCLean.ClassicalCommunication.tensorContinuousChannelsRealBilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.tensorContinuousChannelsRealBilinear

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.tensorContinuousChannels_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.tensorContinuousChannels_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.tensorContinuousChannels_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.measurable_jointDensityChannelScore

/-- info: 'NLQCLean.ClassicalCommunication.measurable_jointDensityChannelScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.measurable_jointDensityChannelScore

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.jointDensityChannelScore_fubini

/-- info: 'NLQCLean.ClassicalCommunication.jointDensityChannelScore_fubini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.jointDensityChannelScore_fubini
