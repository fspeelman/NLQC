import NLQCLean.Exact.BitstringExactExclusion
import NLQCLean.Results.Unitary

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.card_qubitString
set_option pp.universes true in
#check @NLQCLean.bitstringControlledPhase_source_apply
set_option pp.universes true in
#check @NLQCLean.bitstringControlledPhase_restrictedChannel_eq
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one_orbit

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase

/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase_orbit

/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase_orbit

/-- info: 'NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one

/-- info: 'NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one

/-- info: 'NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit

/-- info: 'NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.mixedChannel_ne_adConj_bitstringControlledPhase_one_orbit

set_option pp.universes true in
#check @NLQCLean.bitstringControlledPhase_unitary
/-- info: 'NLQCLean.bitstringControlledPhase_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bitstringControlledPhase_unitary

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_first_qubit_phase_algebraic
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_first_qubit_phase_algebraic
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_first_qubit_one_exact_exclusion
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_first_qubit_one_exact_exclusion
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_first_qubit_one_local_orbit_exact_exclusion
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_first_qubit_one_local_orbit_exact_exclusion
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.first_qubit_controlled_phase_purity

/-- info: 'NLQCLean.Results.Unitary.pure_first_qubit_one_exact_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.pure_first_qubit_one_exact_exclusion

/-- info: 'NLQCLean.Results.Unitary.mixed_first_qubit_one_exact_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.mixed_first_qubit_one_exact_exclusion
