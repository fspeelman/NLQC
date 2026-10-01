import NLQCLean.Exact.LocalChannelRestriction

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.localChannelRestriction_eq_channelOf
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.isIsometry_conjTranspose_of_unitary
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.localChannelRestriction_local_unitary_cancel
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.localChannelRestriction_reindex

/-- info: 'NLQCLean.ClassicalCommunication.localChannelRestriction_local_unitary_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.localChannelRestriction_local_unitary_cancel
/-- info: 'NLQCLean.ClassicalCommunication.localChannelRestriction_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.localChannelRestriction_reindex
