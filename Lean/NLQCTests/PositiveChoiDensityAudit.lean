import NLQCLean.Models.ClassicalCommunication.ChoiDensityPositivity

/-! # Derived positive normalized instrument densities -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ae_posSemidef_of_forall_setIntegral_posSemidef

/-- info: 'NLQCLean.ClassicalCommunication.ae_posSemidef_of_forall_setIntegral_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ae_posSemidef_of_forall_setIntegral_posSemidef

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_posSemidef

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_posSemidef

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_trace

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.density_ae_trace

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.integral_density_inputMarginal

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.integral_density_inputMarginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.integral_density_inputMarginal

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_positive_normalized_density

/-- info: 'NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_positive_normalized_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ChoiVectorInstrument.exists_positive_normalized_density
