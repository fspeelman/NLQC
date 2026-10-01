import NLQCLean.Approx.GenericSpectralThresholds

/-!
# Intrinsic Haar nullity and fixed-target spectral thresholds

Full types expose the nonvanishing witness, Haar measure, target-before-budget
quantifier order, and all eight score/operational-error reachable sets.
No quantitative geometry or arithmetic input is required.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.unitaryHaar_polynomial_zeroSet_eq_zero

/-- info: 'NLQCLean.unitaryHaar_polynomial_zeroSet_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryHaar_polynomial_zeroSet_eq_zero

set_option pp.universes true in
#check @NLQCLean.ae_unitary_rank_linear_full

/-- info: 'NLQCLean.ae_unitary_rank_linear_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_unitary_rank_linear_full

set_option pp.universes true in
#check @NLQCLean.ae_unitary_operatorSchmidtRank_full

/-- info: 'NLQCLean.ae_unitary_operatorSchmidtRank_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_unitary_operatorSchmidtRank_full

set_option pp.universes true in
#check @NLQCLean.ae_pvmColumnSchmidtRank_full

/-- info: 'NLQCLean.ae_pvmColumnSchmidtRank_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_pvmColumnSchmidtRank_full

set_option pp.universes true in
#check @NLQCLean.ae_unitary_pos_schmidtWeight_lower_bound

/-- info: 'NLQCLean.ae_unitary_pos_schmidtWeight_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_unitary_pos_schmidtWeight_lower_bound

set_option pp.universes true in
#check @NLQCLean.ae_pvm_pos_uniform_schmidtWeight_lower_bound

/-- info: 'NLQCLean.ae_pvm_pos_uniform_schmidtWeight_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_pvm_pos_uniform_schmidtWeight_lower_bound

set_option pp.universes true in
#check @NLQCLean.ae_full_spectral_footprint_threshold

/-- info: 'NLQCLean.ae_full_spectral_footprint_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_full_spectral_footprint_threshold

-- Low-dimensional endpoints still use the Haar probability measure.
example : ∀ᵐ (U : Matrix.unitaryGroup (Fin 0 × Fin 0) ℂ)
    ∂NLQCLean.unitaryHaar (Fin 0 × Fin 0),
    (NLQCLean.labChoiMatrix (U : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ)).rank = 0 ^ 2 :=
  NLQCLean.ae_unitary_operatorSchmidtRank_full 0

example : ∀ᵐ (M : Matrix.unitaryGroup (Fin 1 × Fin 1) ℂ)
    ∂NLQCLean.unitaryHaar (Fin 1 × Fin 1),
    ∀ i, (NLQCLean.pvmConjugateColumnMatrix
      (M : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) i).rank = 1 :=
  NLQCLean.ae_pvmColumnSchmidtRank_full 1
