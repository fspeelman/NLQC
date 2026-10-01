import NLQCLean.Arithmetic.ChargedPhysicalCoordinates

/-!
# Sharp physical coordinate count and attained architecture

No rational-coefficient, elimination or positivity certificate is assumed.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.finrank_physicalBlocks_eq_rawRealCoordinateCount

/-- info: 'NLQCLean.finrank_physicalBlocks_eq_rawRealCoordinateCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.finrank_physicalBlocks_eq_rawRealCoordinateCount

set_option pp.universes true in
#check @NLQCLean.sharp_qubit_decoder_dimensions

/-- info: 'NLQCLean.sharp_qubit_decoder_dimensions' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.sharp_qubit_decoder_dimensions

set_option pp.universes true in
#check @NLQCLean.sharp_qubit_rawRealCoordinateCount_le

/-- info: 'NLQCLean.sharp_qubit_rawRealCoordinateCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.sharp_qubit_rawRealCoordinateCount_le

set_option pp.universes true in
#check @NLQCLean.PureProtocol.exists_qubit_compressed_coordinate_certificate

/-- info: 'NLQCLean.PureProtocol.exists_qubit_compressed_coordinate_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.exists_qubit_compressed_coordinate_certificate

set_option pp.universes true in
#check @NLQCLean.exists_qubit_unitaryScoreMaximum_coordinate_certificate

/-- info: 'NLQCLean.exists_qubit_unitaryScoreMaximum_coordinate_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_qubit_unitaryScoreMaximum_coordinate_certificate
