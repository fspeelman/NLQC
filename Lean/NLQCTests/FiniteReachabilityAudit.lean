import NLQCLean.Models.ClassicalCommunication.FiniteReachability

/-!
# finite-shape reachability transfers

The full types retain the fifth-power charge and expose the finite-shape
scope. Zero-budget statements use normalization, not a dimension box.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finitePureScoreReachable_subset_pureReachable

/-- info: 'NLQCLean.ClassicalCommunication.finitePureScoreReachable_subset_pureReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finitePureScoreReachable_subset_pureReachable

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finiteMixedScoreReachable_subset_pureReachable

/-- info: 'NLQCLean.ClassicalCommunication.finiteMixedScoreReachable_subset_pureReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finiteMixedScoreReachable_subset_pureReachable

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finitePurePVMScoreReachable_subset_purePVMReachable

/-- info: 'NLQCLean.ClassicalCommunication.finitePurePVMScoreReachable_subset_purePVMReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finitePurePVMScoreReachable_subset_purePVMReachable

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_subset_purePVMReachable

/-- info: 'NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_subset_purePVMReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_subset_purePVMReachable

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finitePureScoreReachable_zero_budget

/-- info: 'NLQCLean.ClassicalCommunication.finitePureScoreReachable_zero_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finitePureScoreReachable_zero_budget

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_zero_budget

/-- info: 'NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_zero_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.finiteMixedPVMScoreReachable_zero_budget
