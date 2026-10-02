import NLQCLean.Exact.ExactBadDecomposition

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.MatrixRepresentation.exists_invariant_separating

set_option pp.universes true in
#check @NLQCLean.MatrixRepresentation.exists_finite_separating_invariants

set_option pp.universes true in
#check @NLQCLean.exists_finite_unitaryDoubleOrbit_separating

set_option pp.universes true in
#check @NLQCLean.exists_finite_pvmBasisOrbit_separating

set_option pp.universes true in
#check @NLQCLean.finite_of_semialgebraic_scalar_null

set_option pp.universes true in
#check @NLQCLean.mem_targetExactWitnessSet_local

set_option pp.universes true in
#check @NLQCLean.unitaryDoubleOrbit_subset_exactTargets

set_option pp.universes true in
#check @NLQCLean.finite_exactTargets_values

set_option pp.universes true in
#check @NLQCLean.exists_finset_exactTargets_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.mem_unitaryDoubleOrbit_of_mem_connectedComponentIn

set_option pp.universes true in
#check @NLQCLean.mem_unitaryDoubleOrbit_of_continuousOn_path

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_unitaryDoubleOrbit_eq_zero

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_pvmBasisOrbit_eq_zero

set_option pp.universes true in
#check @NLQCLean.exactUnitaryBad_eq_iUnion_exactTargets

set_option pp.universes true in
#check @NLQCLean.PureProtocol.mem_exactUnitaryBad

set_option pp.universes true in
#check @NLQCLean.exists_exactUnitaryBad_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_exactUnitaryBad_eq_zero

/-- info: 'NLQCLean.MatrixRepresentation.exists_invariant_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MatrixRepresentation.exists_invariant_separating

/-- info: 'NLQCLean.MatrixRepresentation.exists_finite_separating_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MatrixRepresentation.exists_finite_separating_invariants

/-- info: 'NLQCLean.exists_finite_unitaryDoubleOrbit_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finite_unitaryDoubleOrbit_separating

/-- info: 'NLQCLean.exists_finite_pvmBasisOrbit_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finite_pvmBasisOrbit_separating

/-- info: 'NLQCLean.finite_of_semialgebraic_scalar_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.finite_of_semialgebraic_scalar_null

/-- info: 'NLQCLean.mem_targetExactWitnessSet_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_targetExactWitnessSet_local

/-- info: 'NLQCLean.unitaryDoubleOrbit_subset_exactTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryDoubleOrbit_subset_exactTargets

/-- info: 'NLQCLean.finite_exactTargets_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.finite_exactTargets_values

/-- info: 'NLQCLean.exists_finset_exactTargets_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finset_exactTargets_eq_iUnion_orbits

/-- info: 'NLQCLean.mem_unitaryDoubleOrbit_of_mem_connectedComponentIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_unitaryDoubleOrbit_of_mem_connectedComponentIn

/-- info: 'NLQCLean.mem_unitaryDoubleOrbit_of_continuousOn_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_unitaryDoubleOrbit_of_continuousOn_path

/-- info: 'NLQCLean.unitaryHaar_unitaryDoubleOrbit_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_unitaryDoubleOrbit_eq_zero

/-- info: 'NLQCLean.unitaryHaar_pvmBasisOrbit_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_pvmBasisOrbit_eq_zero

/-- info: 'NLQCLean.exactUnitaryBad_eq_iUnion_exactTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exactUnitaryBad_eq_iUnion_exactTargets

/-- info: 'NLQCLean.PureProtocol.mem_exactUnitaryBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.mem_exactUnitaryBad

/-- info: 'NLQCLean.exists_exactUnitaryBad_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exactUnitaryBad_eq_iUnion_orbits

/-- info: 'NLQCLean.unitaryHaar_exactUnitaryBad_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_exactUnitaryBad_eq_zero
