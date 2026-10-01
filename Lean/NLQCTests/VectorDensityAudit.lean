import NLQCLean.Models.ClassicalCommunication.ChoiInstrumentDensities

/-!
# Derived finite-dimensional vector-measure densities

No density or reconstruction field is assumed in this representation theorem.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finiteDimensional_vectorMeasure_density

/-- info: 'NLQCLean.ClassicalCommunication.exists_finiteDimensional_vectorMeasure_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finiteDimensional_vectorMeasure_density
