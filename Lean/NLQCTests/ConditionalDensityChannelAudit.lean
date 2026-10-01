import NLQCLean.Models.ClassicalCommunication.ConditionalDensityChannels

/-! # Every-outcome conditional integration and linear scores -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_conditionalDensityChannelScoreLeft

/-- info: 'NLQCLean.ClassicalCommunication.integrable_conditionalDensityChannelScoreLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_conditionalDensityChannelScoreLeft

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.conditionalDensityChannelScoreLeft

/-- info: 'NLQCLean.ClassicalCommunication.conditionalDensityChannelScoreLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.conditionalDensityChannelScoreLeft

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integral_conditionalDensityChannelScoreLeft

/-- info: 'NLQCLean.ClassicalCommunication.integral_conditionalDensityChannelScoreLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integral_conditionalDensityChannelScoreLeft
