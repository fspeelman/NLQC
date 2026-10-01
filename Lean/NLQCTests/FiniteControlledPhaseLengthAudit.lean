import NLQCLean.Bounds.FiniteControlledPhaseLength

/-! # Finite-shape phase length and simultaneous worst-case targets -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.exists_finiteControlledPhase_length_constant_of_external

/-- info: 'NLQCLean.exists_finiteControlledPhase_length_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finiteControlledPhase_length_constant_of_external

set_option pp.universes true in
#check @NLQCLean.exists_finiteControlledPhase_worst_case_constant_of_external

/-- info: 'NLQCLean.exists_finiteControlledPhase_worst_case_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_finiteControlledPhase_worst_case_constant_of_external

set_option pp.universes true in
#check @NLQCLean.finiteControlledPhaseAngles_union_subset_charged

/-- info: 'NLQCLean.finiteControlledPhaseAngles_union_subset_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.finiteControlledPhaseAngles_union_subset_charged
