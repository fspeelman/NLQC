import NLQCLean.Invariants.RectangularControlledPhase

/-! # rectangular two-level and local-phase matrix identities -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

#check @NLQCLean.coordinateInclusionMatrix_adjoint_mul
set_option pp.universes true in
#check @NLQCLean.coordinateInclusionMatrix_isometry
#check @NLQCLean.rectangularTwoLevelIsometry_isometry

/-- info: 'NLQCLean.coordinateInclusionMatrix_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.coordinateInclusionMatrix_isometry

/-- info: 'NLQCLean.rectangularTwoLevelIsometry_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rectangularTwoLevelIsometry_isometry

#check @NLQCLean.rectangularDiagonalPhase_unitary
#check @NLQCLean.rectangularDiagonalPhase_restriction

/-- info: 'NLQCLean.rectangularDiagonalPhase_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rectangularDiagonalPhase_restriction

#check @NLQCLean.rectangularDiagonalPhase_intertwines

/-- info: 'NLQCLean.rectangularDiagonalPhase_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rectangularDiagonalPhase_intertwines

#check @NLQCLean.qubitPhaseCorrectionA_unitary
#check @NLQCLean.qubitPhaseCorrectionB_unitary
#check @NLQCLean.normSq_qubitGlobalPhaseCorrection
#check @NLQCLean.qubitDiagonalPhase_local_reduction

/-- info: 'NLQCLean.qubitDiagonalPhase_local_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.qubitDiagonalPhase_local_reduction

set_option pp.universes true in
#check @NLQCLean.rectangularDiagonalPhase_local_reduction

/-- info: 'NLQCLean.rectangularDiagonalPhase_local_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rectangularDiagonalPhase_local_reduction
