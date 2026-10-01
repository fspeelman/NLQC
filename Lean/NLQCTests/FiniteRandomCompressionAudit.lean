import NLQCLean.Models.ClassicalCommunication.FiniteRandomCompression

/-! # Integrated finite mixed-branch target scores -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_pureReachable_of_integrated_finite_mixed_score

/-- info: 'NLQCLean.ClassicalCommunication.mem_pureReachable_of_integrated_finite_mixed_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_pureReachable_of_integrated_finite_mixed_score

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_purePVMReachable_of_integrated_finite_mixed_score

/-- info: 'NLQCLean.ClassicalCommunication.mem_purePVMReachable_of_integrated_finite_mixed_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_purePVMReachable_of_integrated_finite_mixed_score
