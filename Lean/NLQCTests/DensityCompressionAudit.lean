import NLQCLean.Models.ClassicalCommunication.SequentialDensityCompression

/-! # finite density selections and sequential good sections -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_normalized

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_normalized

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_finite_score_preserving_density_instrument

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_finite_score_preserving_density_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.exists_finite_score_preserving_density_instrument

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_sequential_score_preserving_density_instruments

/-- info: 'NLQCLean.ClassicalCommunication.exists_sequential_score_preserving_density_instruments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_sequential_score_preserving_density_instruments
