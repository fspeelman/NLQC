import NLQCLean.Models.ClassicalCommunication.BranchSelection

/-! # high-score probability branch selection -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_good_score_ge_integral

/-- info: 'NLQCLean.ClassicalCommunication.exists_good_score_ge_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_good_score_ge_integral

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_linearScore_ge

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_linearScore_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_linearScore_ge

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_component_linearScore_ge

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_component_linearScore_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_protocol_branch_component_linearScore_ge
