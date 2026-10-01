import NLQCLean.Models.ClassicalCommunication.ChoiVectorInstrument

/-! # Derived trace probability and countably additive Choi densities -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.traceProbability_real_apply

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.traceProbability_real_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.traceProbability_real_apply

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_eq_zero_of_traceProbability_eq_zero

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_eq_zero_of_traceProbability_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_eq_zero_of_traceProbability_eq_zero

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_absolutelyContinuous

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_absolutelyContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.choiMeasure_absolutelyContinuous

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_integrable_density

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_integrable_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_integrable_density
