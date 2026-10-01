import NLQCLean.Arithmetic.RationalSemialgebraicBoundary

/-! Full types and axioms for algebraicity of rational semialgebraic null sets. -/

open NLQCLean.RationalQE

set_option pp.universes true in
#check @SADef.exists_nonzero_rational_polynomial_zero_of_measure_eq_zero
set_option pp.universes true in
#check @SADef.isAlgebraic_of_scalar_measure_eq_zero
set_option pp.universes true in
#check @SADef.isAlgebraic_int_of_scalar_measure_eq_zero
set_option pp.universes true in
#check @SADef.isAlgebraic_of_euclidean_measure_eq_zero
set_option pp.universes true in
#check @SADef.isAlgebraic_int_of_euclidean_measure_eq_zero

/-- info: 'NLQCLean.RationalQE.SADef.isAlgebraic_of_scalar_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SADef.isAlgebraic_of_scalar_measure_eq_zero
/-- info: 'NLQCLean.RationalQE.SADef.isAlgebraic_int_of_scalar_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SADef.isAlgebraic_int_of_scalar_measure_eq_zero
/-- info: 'NLQCLean.RationalQE.SADef.isAlgebraic_of_euclidean_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SADef.isAlgebraic_of_euclidean_measure_eq_zero
/-- info: 'NLQCLean.RationalQE.SADef.isAlgebraic_int_of_euclidean_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SADef.isAlgebraic_int_of_euclidean_measure_eq_zero
