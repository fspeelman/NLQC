import NLQCLean.Exact.InvariantCriticalValues

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.hasDerivAt_invariant_forwardOverlap_zero
set_option pp.universes true in
#check @NLQCLean.hasDerivAt_invariantScalarPhi_line
set_option pp.universes true in
#check @NLQCLean.fderiv_invariantScalarPhi_eq_zero
set_option pp.universes true in
#check @NLQCLean.volume_invariantScalarPhi_image_eq_zero
set_option pp.universes true in
#check @NLQCLean.invariant_mem_exactInvariantValues
set_option pp.universes true in
#check @NLQCLean.PureProtocol.invariant_mem_exactInvariantValues_of_score_eq_one

/-- info: 'NLQCLean.hasDerivAt_invariant_forwardOverlap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.hasDerivAt_invariant_forwardOverlap_zero

/-- info: 'NLQCLean.hasDerivAt_invariantScalarPhi_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.hasDerivAt_invariantScalarPhi_line

/-- info: 'NLQCLean.fderiv_invariantScalarPhi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.fderiv_invariantScalarPhi_eq_zero

/-- info: 'NLQCLean.volume_invariantScalarPhi_image_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.volume_invariantScalarPhi_image_eq_zero

/-- info: 'NLQCLean.invariant_mem_exactInvariantValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.invariant_mem_exactInvariantValues

/-- info: 'NLQCLean.PureProtocol.invariant_mem_exactInvariantValues_of_score_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.invariant_mem_exactInvariantValues_of_score_eq_one
