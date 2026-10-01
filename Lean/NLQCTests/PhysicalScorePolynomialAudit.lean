import NLQCLean.Arithmetic.PhysicalScorePolynomial

/-! # integer score encoding with separate target coordinates -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.card_physicalScoreCoordinateIndex

/-- info: 'NLQCLean.PhysicalPolynomial.card_physicalScoreCoordinateIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.card_physicalScoreCoordinateIndex

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_degree_le

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_evaluate

/-- info: 'NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalGlobalPolynomial_evaluate

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_degree_le

/-- info: 'NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_degree_le

set_option pp.universes true in
#check @NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_evaluate

/-- info: 'NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PhysicalPolynomial.physicalScoreNumeratorPolynomial_evaluate

open NLQCLean NLQCLean.PhysicalPolynomial

-- Target entries are not silently counted as physical coordinates.
example (s : Fin 8 → ℕ) :
    Fintype.card (PhysicalScoreCoordinateIndex 2 s) =
      physicalRawRealCoordinateCount 2 s + 32 := by
  simpa using card_physicalScoreCoordinateIndex 2 s
