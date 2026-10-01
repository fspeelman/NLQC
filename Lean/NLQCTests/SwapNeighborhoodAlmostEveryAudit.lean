import NLQCLean.Bounds.SwapNeighborhoodAlmostEvery

/-!
# Restricted almost-every unitary precision rate

Full types expose the regional hypothesis, target-only threshold, all budgets,
four error/model predicates, arbitrary register universes, and the three external
geometry premises. Only the standard logical axioms occur in the proof closure.
-/

set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.exists_ae_swapNeighborhood_forbidden_error_constant

/-- info: 'NLQCLean.exists_ae_swapNeighborhood_forbidden_error_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_swapNeighborhood_forbidden_error_constant

set_option pp.universes true in
#check @NLQCLean.exists_ae_swapNeighborhood_resource_constant_of_external

/-- info: 'NLQCLean.exists_ae_swapNeighborhood_resource_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_swapNeighborhood_resource_constant_of_external

set_option pp.universes true in
#check @NLQCLean.exists_ae_swapNeighborhood_physical_resource_constant_of_external

/-- info: 'NLQCLean.exists_ae_swapNeighborhood_physical_resource_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_swapNeighborhood_physical_resource_constant_of_external
