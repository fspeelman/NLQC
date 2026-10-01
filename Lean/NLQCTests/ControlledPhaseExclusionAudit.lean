import NLQCLean.Exact.ControlledPhaseExclusion
import NLQCLean.Results.Unitary

/-! Full types, arbitrary original register universes and standard axioms for unconditional controlled-phase exclusion. -/

set_option pp.universes true in
#check @NLQCLean.isAlgebraic_exp_angle_of_controlledPhase_purity_mem
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_controlledPhase
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_controlledPhase
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_controlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_controlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.controlledPhase_no_finite_exact_implementation
set_option pp.universes true in
#check @NLQCLean.controlledPhase_one_no_finite_exact_implementation
set_option pp.universes true in
#check @NLQCLean.controlledPhase_one_orbit_no_finite_exact_implementation

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_controlledPhase
/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_controlledPhase
/-- info: 'NLQCLean.controlledPhase_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_no_finite_exact_implementation
/-- info: 'NLQCLean.controlledPhase_one_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_one_no_finite_exact_implementation
/-- info: 'NLQCLean.controlledPhase_one_orbit_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.controlledPhase_one_orbit_no_finite_exact_implementation

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_controlled_phase_phase_algebraic
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_controlled_phase_phase_algebraic
set_option pp.universes true in
#check @NLQCLean.Results.Unitary.controlled_phase_one_no_finite_exact_implementation
/-- info: 'NLQCLean.Results.Unitary.controlled_phase_one_no_finite_exact_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.controlled_phase_one_no_finite_exact_implementation
