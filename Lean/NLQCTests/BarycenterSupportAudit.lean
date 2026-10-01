import NLQCLean.Models.ClassicalCommunication.BarycenterSupport

/-!
# good-set integral support

Full types expose all measure, normalization, model and external premises.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integral_mem_convexHull_image

/-- info: 'NLQCLean.ClassicalCommunication.integral_mem_convexHull_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integral_mem_convexHull_image

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_integral_support

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_integral_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_integral_support

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_hermitian_marginal_score_integral_support

/-- info: 'NLQCLean.ClassicalCommunication.exists_hermitian_marginal_score_integral_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_hermitian_marginal_score_integral_support

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_normalized_hermitian_marginal_score_integral_support

/-- info: 'NLQCLean.ClassicalCommunication.exists_normalized_hermitian_marginal_score_integral_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_normalized_hermitian_marginal_score_integral_support
