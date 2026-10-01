import NLQCLean.Models.ClassicalCommunication.CPVectorInstrument

/-! # CP-valued instrument representation, with original quantum systems -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

#check @NLQCLean.ClassicalCommunication.channelFromUnnormalizedChoi_unnormalizedChoi
#check @NLQCLean.ClassicalCommunication.unnormalizedChoi_channelFromUnnormalizedChoi
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.unnormalizedChoiContinuousRealLinearEquiv

/-- info: 'NLQCLean.ClassicalCommunication.channelFromUnnormalizedChoi_unnormalizedChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.channelFromUnnormalizedChoi_unnormalizedChoi

/-- info: 'NLQCLean.ClassicalCommunication.unnormalizedChoi_channelFromUnnormalizedChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.unnormalizedChoi_channelFromUnnormalizedChoi

/-- info: 'NLQCLean.ClassicalCommunication.unnormalizedChoiContinuousRealLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.unnormalizedChoiContinuousRealLinearEquiv

#check @NLQCLean.ClassicalCommunication.completelyPositive_iff_unnormalizedChoi_posSemidef

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_iff_unnormalizedChoi_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_iff_unnormalizedChoi_posSemidef

#check @NLQCLean.ClassicalCommunication.tracePreserving_iff_ptraceA_unnormalizedChoi

/-- info: 'NLQCLean.ClassicalCommunication.tracePreserving_iff_ptraceA_unnormalizedChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.tracePreserving_iff_ptraceA_unnormalizedChoi

#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.toChoiInstrument_toCPInstrument
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.toCPInstrument_toChoiInstrument
set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.cpVectorInstrumentChoiEquiv

/-- info: 'NLQCLean.ClassicalCommunication.cpVectorInstrumentChoiEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.cpVectorInstrumentChoiEquiv

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_positive_normalized_density

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_positive_normalized_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_positive_normalized_density
