import NLQCLean.Semialgebraic.RationalImages

/-! Full statements and axiom checks for coefficient-preserving projection. -/

set_option pp.universes true in
#check @NLQCLean.polynomialSubring.emod_mem
set_option pp.universes true in
#check @NLQCLean.rationalPolynomialSubring_finSuccEquiv
set_option pp.universes true in
#check @NLQCLean.RationalQE.SADef.to_real
set_option pp.universes true in
#check @NLQCLean.RationalQE.diagramPartition_all
set_option pp.universes true in
#check @NLQCLean.RationalQE.elim_signVector
set_option pp.universes true in
#check @NLQCLean.RationalQE.sadef_sign_char
set_option pp.universes true in
#check @NLQCLean.RationalQE.sadef_proj
set_option pp.universes true in
#check @NLQCLean.RationalSemialgebraic.semialgebraic
set_option pp.universes true in
#check @NLQCLean.RationalSemialgebraic.coordinate_preimage
set_option pp.universes true in
#check @NLQCLean.RationalSemialgebraic.projection
set_option pp.universes true in
#check @NLQCLean.RationalSemialgebraic.first_projection

/-- info: 'NLQCLean.RationalQE.sadef_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalQE.sadef_proj
/-- info: 'NLQCLean.RationalSemialgebraic.first_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.first_projection
