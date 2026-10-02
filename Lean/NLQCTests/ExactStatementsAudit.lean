import NLQCLean.Exact.RigidityStatements
import NLQCLean.Exact.UnequalDimensions
import NLQCLean.Exact.CompressionFiniteOrbits
import NLQCLean.Exact.PaperFoundations
import NLQCLean.Exact.PVMPathFactorization

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.linearMap_ext_of_pure

set_option pp.universes true in
#check @NLQCLean.rigidity_of_pure_states

set_option pp.universes true in
#check @NLQCLean.PureProtocol.performsUnitary_iff_frozen

set_option pp.universes true in
#check @NLQCLean.twoSidedExact_iff_flag

set_option pp.universes true in
#check @NLQCLean.duplicated_labels

set_option pp.universes true in
#check @NLQCLean.compression_state

set_option pp.universes true in
#check @NLQCLean.mem_exactUnitaryBad_iff_frozen

set_option pp.universes true in
#check @NLQCLean.volume_invariantScalarPhiGen_image_eq_zero

set_option pp.universes true in
#check @NLQCLean.isPolyZeroSet_isExactWitnessGen

set_option pp.universes true in
#check @NLQCLean.exists_finset_genExactTargets_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.PureProtocol.mem_iUnion_genExactTargets

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_iUnion_genExactTargets_eq_zero

set_option pp.universes true in
#check @NLQCLean.ae_unitary_no_exact_protocol_gen

/-- info: 'NLQCLean.linearMap_ext_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.linearMap_ext_of_pure

/-- info: 'NLQCLean.rigidity_of_pure_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rigidity_of_pure_states

/-- info: 'NLQCLean.PureProtocol.performsUnitary_iff_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.performsUnitary_iff_frozen

/-- info: 'NLQCLean.twoSidedExact_iff_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.twoSidedExact_iff_flag

/-- info: 'NLQCLean.duplicated_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.duplicated_labels

/-- info: 'NLQCLean.compression_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.compression_state

/-- info: 'NLQCLean.mem_exactUnitaryBad_iff_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.mem_exactUnitaryBad_iff_frozen

/-- info: 'NLQCLean.volume_invariantScalarPhiGen_image_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.volume_invariantScalarPhiGen_image_eq_zero

/-- info: 'NLQCLean.isPolyZeroSet_isExactWitnessGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isPolyZeroSet_isExactWitnessGen

/-- info: 'NLQCLean.exists_finset_genExactTargets_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finset_genExactTargets_eq_iUnion_orbits

/-- info: 'NLQCLean.PureProtocol.mem_iUnion_genExactTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.mem_iUnion_genExactTargets

/-- info: 'NLQCLean.unitaryHaar_iUnion_genExactTargets_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_iUnion_genExactTargets_eq_zero

/-- info: 'NLQCLean.ae_unitary_no_exact_protocol_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_unitary_no_exact_protocol_gen

set_option pp.universes true in
#check @NLQCLean.PureProtocol.exists_compressed_forward_bounds

/-- info: 'NLQCLean.PureProtocol.exists_compressed_forward_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.exists_compressed_forward_bounds

set_option pp.universes true in
#check @NLQCLean.exactUnitaryFixedRank_eq_iUnion

/-- info: 'NLQCLean.exactUnitaryFixedRank_eq_iUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exactUnitaryFixedRank_eq_iUnion

set_option pp.universes true in
#check @NLQCLean.exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits

/-- info: 'NLQCLean.exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_isHaar_characterization

/-- info: 'NLQCLean.unitaryHaar_isHaar_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_isHaar_characterization

set_option pp.universes true in
#check @NLQCLean.exists_stinespring

/-- info: 'NLQCLean.exists_stinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_stinespring

set_option pp.universes true in
#check @NLQCLean.fact_TS_projection

/-- info: 'NLQCLean.fact_TS_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.fact_TS_projection

set_option pp.universes true in
#check @NLQCLean.SemialgebraicMapOn.coordinate

/-- info: 'NLQCLean.SemialgebraicMapOn.coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.SemialgebraicMapOn.coordinate

set_option pp.universes true in
#check @NLQCLean.exists_pvm_factorization

/-- info: 'NLQCLean.exists_pvm_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_pvm_factorization

set_option pp.universes true in
#check @NLQCLean.pvm_path_factorization

/-- info: 'NLQCLean.pvm_path_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvm_path_factorization
