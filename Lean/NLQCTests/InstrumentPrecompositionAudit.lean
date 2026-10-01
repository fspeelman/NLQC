import NLQCLean.Models.ClassicalCommunication.InstrumentPrecomposition

/-! # Isometric input precomposition of CP instruments -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.precompositionTraceRealLinear_nonneg

/-- info: 'NLQCLean.ClassicalCommunication.precompositionTraceRealLinear_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.precompositionTraceRealLinear_nonneg

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.operationPrecomposition_eq_zero_of_trace_eq_zero

/-- info: 'NLQCLean.ClassicalCommunication.operationPrecomposition_eq_zero_of_trace_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.operationPrecomposition_eq_zero_of_trace_eq_zero

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.withDensity_operationPrecomposition

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.withDensity_operationPrecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.withDensity_operationPrecomposition

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.traceProbability_precomposeIsometry

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.traceProbability_precomposeIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.traceProbability_precomposeIsometry

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.ae_precompositionTraceWeight_smul_normalizedDensity

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.ae_precompositionTraceWeight_smul_normalizedDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.ae_precompositionTraceWeight_smul_normalizedDensity

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.normalizedPrecompositionDensity_spec

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.normalizedPrecompositionDensity_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.normalizedPrecompositionDensity_spec
