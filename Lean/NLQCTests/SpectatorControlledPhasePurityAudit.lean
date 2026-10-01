import NLQCLean.Invariants.SpectatorControlledPhasePurity

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

/-! Full statements and axioms of the source spectator purity formula. -/

set_option pp.universes true in
#check @NLQCLean.realign_gram_sq_trace_diagonal
/-- info: 'NLQCLean.realign_gram_sq_trace_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.realign_gram_sq_trace_diagonal

set_option pp.universes true in
#check @NLQCLean.realign_gram_sq_trace_diagonal_spectators
/-- info: 'NLQCLean.realign_gram_sq_trace_diagonal_spectators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.realign_gram_sq_trace_diagonal_spectators

set_option pp.universes true in
#check @NLQCLean.purity_spectatorControlledPhase_scale
/-- info: 'NLQCLean.purity_spectatorControlledPhase_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_spectatorControlledPhase_scale

set_option pp.universes true in
#check @NLQCLean.purity_spectatorControlledPhase
/-- info: 'NLQCLean.purity_spectatorControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_spectatorControlledPhase

set_option pp.universes true in
#check @NLQCLean.purity_bitstringControlledPhase
/-- info: 'NLQCLean.purity_bitstringControlledPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_bitstringControlledPhase
