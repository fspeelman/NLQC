import NLQCLean.Exact.PVMBadDecomposition

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.IsPolyZeroSet.semialgebraic_image

set_option pp.universes true in
#check @NLQCLean.fderiv_eq_zero_of_pvmMotion

set_option pp.universes true in
#check @NLQCLean.volume_pvmInvariantScalarPhi_image_eq_zero

set_option pp.universes true in
#check @NLQCLean.isPolyZeroSet_isExactPVMWitness

set_option pp.universes true in
#check @NLQCLean.pvmBasisOrbit_subset_pvmExactTargets

set_option pp.universes true in
#check @NLQCLean.finite_pvmExactTargets_values

set_option pp.universes true in
#check @NLQCLean.exists_finset_pvmExactTargets_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.mem_pvmBasisOrbit_of_mem_connectedComponentIn

set_option pp.universes true in
#check @NLQCLean.mem_pvmBasisOrbit_of_continuousOn_path

set_option pp.universes true in
#check @NLQCLean.pvmExactTargets_eq_protocols

set_option pp.universes true in
#check @NLQCLean.exactPVMBad_eq_iUnion_pvmExactTargets

set_option pp.universes true in
#check @NLQCLean.PureProtocol.mem_exactPVMBad

set_option pp.universes true in
#check @NLQCLean.exists_exactPVMBad_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_exactPVMBad_eq_zero

/-- info: 'NLQCLean.IsPolyZeroSet.semialgebraic_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.IsPolyZeroSet.semialgebraic_image

/-- info: 'NLQCLean.fderiv_eq_zero_of_pvmMotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.fderiv_eq_zero_of_pvmMotion

/-- info: 'NLQCLean.volume_pvmInvariantScalarPhi_image_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.volume_pvmInvariantScalarPhi_image_eq_zero

/-- info: 'NLQCLean.isPolyZeroSet_isExactPVMWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isPolyZeroSet_isExactPVMWitness

/-- info: 'NLQCLean.pvmBasisOrbit_subset_pvmExactTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmBasisOrbit_subset_pvmExactTargets

/-- info: 'NLQCLean.finite_pvmExactTargets_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.finite_pvmExactTargets_values

/-- info: 'NLQCLean.exists_finset_pvmExactTargets_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finset_pvmExactTargets_eq_iUnion_orbits

/-- info: 'NLQCLean.mem_pvmBasisOrbit_of_mem_connectedComponentIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_pvmBasisOrbit_of_mem_connectedComponentIn

/-- info: 'NLQCLean.mem_pvmBasisOrbit_of_continuousOn_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_pvmBasisOrbit_of_continuousOn_path

/-- info: 'NLQCLean.pvmExactTargets_eq_protocols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmExactTargets_eq_protocols

/-- info: 'NLQCLean.exactPVMBad_eq_iUnion_pvmExactTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exactPVMBad_eq_iUnion_pvmExactTargets

/-- info: 'NLQCLean.PureProtocol.mem_exactPVMBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.mem_exactPVMBad

/-- info: 'NLQCLean.exists_exactPVMBad_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_exactPVMBad_eq_iUnion_orbits

/-- info: 'NLQCLean.unitaryHaar_exactPVMBad_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_exactPVMBad_eq_zero
