import NLQCLean.Arithmetic.PhysicalPolynomialHeight

/-! # Explicit coefficient heights of physical polynomials -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalConstraintPolynomial_massLE

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintPolynomial_massLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintPolynomial_massLE

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_massLE

/-- info: 'NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_massLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_massLE

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_massLE

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_massLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_massLE

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_realAbs_le

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_realAbs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_realAbs_le

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.CoefficientMassLE.binary_bound

/-- info: 'NLQCLean.PhysicalPolynomial.CoefficientMassLE.binary_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.CoefficientMassLE.binary_bound

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_binary_massLE

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_binary_massLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_binary_massLE

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE_of_four_mul_box

/-- info: 'NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE_of_four_mul_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalConstraintSumSquares_massLE_of_four_mul_box

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_natAbs_le_of_four_mul_box

/-- info: 'NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_natAbs_le_of_four_mul_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.controlledPhaseScoreNumeratorPolynomial_coefficient_natAbs_le_of_four_mul_box

namespace NLQCLean.PhysicalPolynomial

/-! The literal box `s i ≤ K` and the exact natural-number constants are pinned. -/

example {K : ℕ} (hK : 1 ≤ K) (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K)
    (q : PhysicalConstraintIndex 2 s) :
    CoefficientMassLE (physicalConstraintPolynomial 2 s q) (5 * K ^ 2) :=
  physicalConstraintPolynomial_massLE hK s hs q

example {K : ℕ} (hK : 1 ≤ K) (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (physicalConstraintSumSquares 2 s) (525 * K ^ 8) :=
  physicalConstraintSumSquares_massLE hK s hs

example {K : ℕ} (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (physicalScoreNumeratorPolynomial 2 s) (2 ^ 23 * K ^ 14) :=
  physicalScoreNumeratorPolynomial_massLE s hs

example {K : ℕ} (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial s) (2 ^ (23 + 14 * K)) :=
  controlledPhaseScoreNumeratorPolynomial_binary_massLE s hs

example {K : ℕ} (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ 4 * K) :
    CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial s) (2 ^ 51 * K ^ 14) :=
  controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box s hs

end NLQCLean.PhysicalPolynomial
