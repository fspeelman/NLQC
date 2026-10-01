import NLQCLean.Exact.WitnessRationalCoordinates

/-! Full types and axioms for the original seven-block raw coordinates. -/

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.coordinatesEquiv

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.coordinateMatrix_targetCoordinates
/-- info: 'NLQCLean.ExactWitnessCoordinates.coordinateMatrix_targetCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.coordinateMatrix_targetCoordinates

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.coordinateVector_witnessCoordinates
/-- info: 'NLQCLean.ExactWitnessCoordinates.coordinateVector_witnessCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.coordinateVector_witnessCoordinates

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_physicalBlocks
/-- info: 'NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_physicalBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_physicalBlocks

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_symm_liftPhysicalCoordinates
/-- info: 'NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_symm_liftPhysicalCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.physicalCoordinatesEquiv_symm_liftPhysicalCoordinates

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_symm_apply_apply
/-- info: 'NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_symm_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_symm_apply_apply

set_option pp.universes true in
#check @NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_apply_symm_apply
/-- info: 'NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_apply_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ExactWitnessCoordinates.coordinatesEquiv_apply_symm_apply
