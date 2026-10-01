import NLQCLean.Models.ClassicalCommunication.FiniteOutputRestriction
import NLQCLean.Results.Unitary

/-! # output protocols preserve charge and whole pure/mixed channels -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.channelOf_composeOutputStinespring

/-- info: 'NLQCLean.ClassicalCommunication.channelOf_composeOutputStinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.channelOf_composeOutputStinespring

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_operationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_mixedOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_mixedOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_mixedOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_hasQuantumFootprint_iff

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_hasQuantumFootprint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.postcomposeLogicalOutputs_hasQuantumFootprint_iff

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_operationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedOperationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedOperationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedOperationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_diamondError_le

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_diamondError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_diamondError_le

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedDiamondError_le

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedDiamondError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.restrictRectangularDiagonal_mixedDiamondError_le

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.finite_rectangular_diagonal_diamond_error_le

/-- info: 'NLQCLean.Results.Unitary.finite_rectangular_diagonal_diamond_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.finite_rectangular_diagonal_diamond_error_le

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.finite_mixed_rectangular_diagonal_diamond_error_le

/-- info: 'NLQCLean.Results.Unitary.finite_mixed_rectangular_diagonal_diamond_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.finite_mixed_rectangular_diagonal_diamond_error_le
