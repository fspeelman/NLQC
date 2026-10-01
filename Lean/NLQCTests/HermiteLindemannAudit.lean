import NLQCLean.Vendor.HermiteLindemann.Basic

/-! Full statements and standard-axiom checks for the compatibility port. -/

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.linearIndependent_exp
/-- info: 'NLQCLean.HermiteLindemann.linearIndependent_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.linearIndependent_exp

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.algebraicIndependent_exp
/-- info: 'NLQCLean.HermiteLindemann.algebraicIndependent_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.algebraicIndependent_exp

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.transcendental_exp
/-- info: 'NLQCLean.HermiteLindemann.transcendental_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.transcendental_exp

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.transcendental_e
/-- info: 'NLQCLean.HermiteLindemann.transcendental_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.transcendental_e

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.transcendental_pi
/-- info: 'NLQCLean.HermiteLindemann.transcendental_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.transcendental_pi

set_option pp.universes true in
#check @NLQCLean.HermiteLindemann.transcendental_log
/-- info: 'NLQCLean.HermiteLindemann.transcendental_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.HermiteLindemann.transcendental_log
