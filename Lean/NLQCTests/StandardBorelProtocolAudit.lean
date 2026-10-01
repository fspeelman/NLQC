import NLQCLean.Models.ClassicalCommunication.StandardBorelProtocol

/-! # Original CP-valued Borel protocols and derived score integrability -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.measurable_unnormalizedChoi_iff

/-- info: 'NLQCLean.ClassicalCommunication.measurable_unnormalizedChoi_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.measurable_unnormalizedChoi_iff

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.output_nonempty

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.output_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.output_nonempty

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityA_spec

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityA_spec

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityB_spec

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.densityB_spec

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.measurable_jointDecoder

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.measurable_jointDecoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.measurable_jointDecoder

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_tracePreserving

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_tracePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.jointDecoder_tracePreserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_jointScore

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_jointScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_jointScore
