import NLQCLean.Arithmetic.SeparationCertificate

/-!
# Unconditional integer factor and cosine certificates

Full types retain input/output systems, all premises and constants.

-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.divideYPower_factorization

/-- info: 'NLQCLean.divideYPower_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.divideYPower_factorization

set_option pp.universes true in
#check @NLQCLean.yPrimitive_constant_ne_zero

/-- info: 'NLQCLean.yPrimitive_constant_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.yPrimitive_constant_ne_zero

set_option pp.universes true in
#check @NLQCLean.bivariate_primitive_root_certificate

/-- info: 'NLQCLean.bivariate_primitive_root_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariate_primitive_root_certificate

set_option pp.universes true in
#check @NLQCLean.bivariateOfMv_ne_zero

/-- info: 'NLQCLean.bivariateOfMv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariateOfMv_ne_zero

set_option pp.universes true in
#check @NLQCLean.bivariateOfMv_degreeLE

/-- info: 'NLQCLean.bivariateOfMv_degreeLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariateOfMv_degreeLE

set_option pp.universes true in
#check @NLQCLean.bivariateOfMv_heightLE

/-- info: 'NLQCLean.bivariateOfMv_heightLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariateOfMv_heightLE

set_option pp.universes true in
#check @NLQCLean.bivariateEval_bivariateOfMv

/-- info: 'NLQCLean.bivariateEval_bivariateOfMv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariateEval_bivariateOfMv

set_option pp.universes true in
#check @NLQCLean.cosineTransform_natDegree

/-- info: 'NLQCLean.cosineTransform_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.cosineTransform_natDegree

set_option pp.universes true in
#check @NLQCLean.cosineTransform_height_le

/-- info: 'NLQCLean.cosineTransform_height_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.cosineTransform_height_le

set_option pp.universes true in
#check @NLQCLean.abs_cosine_eval_eq_inv_pow_norm_transform

/-- info: 'NLQCLean.abs_cosine_eval_eq_inv_pow_norm_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.abs_cosine_eval_eq_inv_pow_norm_transform

set_option pp.universes true in
#check @NLQCLean.one_le_abs_integerPolynomialEval_of_constant

/-- info: 'NLQCLean.one_le_abs_integerPolynomialEval_of_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.one_le_abs_integerPolynomialEval_of_constant

set_option pp.universes true in
#check @NLQCLean.one_le_abs_cosineTransform_top_coeff

/-- info: 'NLQCLean.one_le_abs_cosineTransform_top_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.one_le_abs_cosineTransform_top_coeff

set_option pp.universes true in
#check @NLQCLean.one_le_cosineTransform_height_bound

/-- info: 'NLQCLean.one_le_cosineTransform_height_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.one_le_cosineTransform_height_bound

set_option pp.universes true in
#check @NLQCLean.bivariate_cosine_gap_lower_bound_of_complex_separation

/-- info: 'NLQCLean.bivariate_cosine_gap_lower_bound_of_complex_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.bivariate_cosine_gap_lower_bound_of_complex_separation

set_option pp.universes true in
#check @NLQCLean.polynomial_separation_gap_bound_pos

/-- info: 'NLQCLean.polynomial_separation_gap_bound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.polynomial_separation_gap_bound_pos

set_option pp.universes true in
#check @NLQCLean.abs_cos_one_eval_eq_inv_pow_norm_transform

/-- info: 'NLQCLean.abs_cos_one_eval_eq_inv_pow_norm_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.abs_cos_one_eval_eq_inv_pow_norm_transform
