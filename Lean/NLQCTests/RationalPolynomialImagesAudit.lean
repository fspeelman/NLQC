import NLQCLean.Semialgebraic.RationalPolynomialImages

/-! Full types and axioms for rational polynomial graphs and images. -/

open NLQCLean

set_option pp.universes true in
#check @RationalSemialgebraic.coordinate_equiv_image
set_option pp.universes true in
#check @RationalSemialgebraic.last_projection
set_option pp.universes true in
#check @RationalSemialgebraic.polynomial_graph
set_option pp.universes true in
#check @RationalSemialgebraic.polynomial_image
set_option pp.universes true in
#check @RationalSemialgebraic.polynomial_graph_rat
set_option pp.universes true in
#check @RationalSemialgebraic.polynomial_image_rat

/-- info: 'NLQCLean.RationalSemialgebraic.last_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.last_projection
/-- info: 'NLQCLean.RationalSemialgebraic.polynomial_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.polynomial_graph
/-- info: 'NLQCLean.RationalSemialgebraic.polynomial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.polynomial_image
/-- info: 'NLQCLean.RationalSemialgebraic.polynomial_image_rat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.RationalSemialgebraic.polynomial_image_rat
