import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder

/-! # local CP/TP decoding and rectangular ideal channel restriction -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

#check @NLQCLean.ClassicalCommunication.twoLevelDecoderStinespring_isometry
#check @NLQCLean.ClassicalCommunication.twoLevelDecoderInstrument

/-- info: 'NLQCLean.ClassicalCommunication.twoLevelDecoderStinespring_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.twoLevelDecoderStinespring_isometry

#check @NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_completelyPositive

#check @NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_trace

/-- info: 'NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_trace

#check @NLQCLean.ClassicalCommunication.twoLevelDecoderChannel_comp_embedding
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.tensorChannels_channelOf_regrouped
#check @NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_completelyPositive

#check @NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_trace
#check @NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_ideal_restriction

/-- info: 'NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_ideal_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.rectangularTwoLevelDecoderChannel_ideal_restriction

example : NLQCLean.IsIsometry (NLQCLean.ClassicalCommunication.twoLevelDecoderStinespring
    (d := 3) (by decide)) := NLQCLean.ClassicalCommunication.twoLevelDecoderStinespring_isometry _
