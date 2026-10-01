import NLQCLean.Exact.SpectatorExactExclusion

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

/-! Full types and standard logical axioms for arbitrary-spectator exact exclusion. -/

set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_local_unitary_restrictedChannel_eq
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_orbit
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase_one
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one
set_option pp.universes true in
#check @NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase_one_orbit
set_option pp.universes true in
#check @NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one_orbit

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase
/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase
/-- info: 'NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_spectatorControlledPhase_orbit
/-- info: 'NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_spectatorControlledPhase_orbit
/-- info: 'NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase_one_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.not_performsUnitary_spectatorControlledPhase_one_orbit
/-- info: 'NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.mixedChannel_ne_adConj_spectatorControlledPhase_one_orbit
