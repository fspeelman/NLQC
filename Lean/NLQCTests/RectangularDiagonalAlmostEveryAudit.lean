import NLQCLean.Bounds.RectangularDiagonalAlmostEvery

/-!
# Rectangular diagonal measure, normalization and resource-rate audit

Full types retain the normalized original diamond predicate, arbitrary original
finite registers, pure/common-map mixed semantics, both charged messages, and
the target-only threshold. The phase law and physical gate equality are
checked separately from the resource rates.
-/

set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.measurePreserving_rectangularAlternatingPhase
#print axioms NLQCLean.measurePreserving_rectangularAlternatingPhase

set_option pp.universes true in
#check @NLQCLean.measurePreserving_rectangularAlternatingAngleMod
#print axioms NLQCLean.measurePreserving_rectangularAlternatingAngleMod

set_option pp.universes true in
#check @NLQCLean.controlledPhase_rectangularAlternatingAngleMod
#print axioms NLQCLean.controlledPhase_rectangularAlternatingAngleMod

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.mixedOperationalChannel_ofPureProtocol

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteRectangularDiagonal_log_bound

/-- info: 'NLQCLean.exists_ae_finiteRectangularDiagonal_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteRectangularDiagonal_log_bound

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteRectangularDiagonal_qubit_bound

/-- info: 'NLQCLean.exists_ae_finiteRectangularDiagonal_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteRectangularDiagonal_qubit_bound

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound

/-- info: 'NLQCLean.exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteLOSCCRectangularDiagonal_qubit_bound

set_option pp.universes true in
#check @NLQCLean.exists_ae_paidRectangularDiagonal_qubit_bound

/-- info: 'NLQCLean.exists_ae_paidRectangularDiagonal_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_paidRectangularDiagonal_qubit_bound

set_option pp.universes true in
#check @NLQCLean.exists_ae_chargedRectangularDiagonal_qubit_bound

/-- info: 'NLQCLean.exists_ae_chargedRectangularDiagonal_qubit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_chargedRectangularDiagonal_qubit_bound
