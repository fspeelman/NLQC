import NLQCLean.Invariants.LocalUnitaryPurity

/-! Full types and axioms for finite local-unitary purity invariance. -/

set_option pp.universes true in
#check @NLQCLean.trace_gram_sq_mul_unitaries
/-- info: 'NLQCLean.trace_gram_sq_mul_unitaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.trace_gram_sq_mul_unitaries

set_option pp.universes true in
#check @NLQCLean.realign_local_factors
/-- info: 'NLQCLean.realign_local_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.realign_local_factors

set_option pp.universes true in
#check @NLQCLean.purity_local_unitary_mul
/-- info: 'NLQCLean.purity_local_unitary_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_local_unitary_mul

set_option pp.universes true in
#check @NLQCLean.purity_eq_of_mem_unitaryDoubleOrbit
/-- info: 'NLQCLean.purity_eq_of_mem_unitaryDoubleOrbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_eq_of_mem_unitaryDoubleOrbit
