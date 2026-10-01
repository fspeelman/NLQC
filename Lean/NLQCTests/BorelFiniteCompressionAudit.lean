import NLQCLean.Models.ClassicalCommunication.BorelFiniteCompression

/-! # finite protocols selected from original Borel instruments -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.channelOf_operationStinespring

/-- info: 'NLQCLean.ClassicalCommunication.channelOf_operationStinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.channelOf_operationStinespring

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.branchChannel_eq_decoder_composition

/-- info: 'NLQCLean.ClassicalCommunication.branchChannel_eq_decoder_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.branchChannel_eq_decoder_composition

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_finite_protocol_preserving_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_finite_protocol_preserving_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.exists_finite_protocol_preserving_linearScore

/-! Scope guard: the selected finite protocol preserves a prescribed real-linear
score and the original resource; no whole-channel or diamond-error preservation
is part of this statement. The alphabets use original input dimensions. -/
