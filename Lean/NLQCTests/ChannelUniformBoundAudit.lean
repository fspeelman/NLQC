import NLQCLean.Models.ClassicalCommunication.ChannelUniformBound

/-! # Dimension-only bounds on CP trace-preserving operation norms -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.operator_norm_le_one
#check @NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_matrixUnit_entry_bound
#check @NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_norm_le

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_matrixUnit_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_matrixUnit_entry_bound

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_tracePreserving_norm_le

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_completelyPositive_tracePreserving_norm_bound

/-- info: 'NLQCLean.ClassicalCommunication.exists_completelyPositive_tracePreserving_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_completelyPositive_tracePreserving_norm_bound
