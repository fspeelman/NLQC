import NLQCLean.Bounds.FiniteControlledPhaseQubits

/-! # initial-resource accounting for finite LOSCC -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.schmidtRank_sq_le_resource_card_product

/-- info: 'NLQCLean.schmidtRank_sq_le_resource_card_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.schmidtRank_sq_le_resource_card_product

set_option pp.universes true in
#check @NLQCLean.qubit_lower_of_tenth_power_and_squared_footprint

/-- info: 'NLQCLean.qubit_lower_of_tenth_power_and_squared_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.qubit_lower_of_tenth_power_and_squared_footprint

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound

/-- info: 'NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_external

/-- info: 'NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteLOSCCControlledPhase_qubit_bound_of_external
