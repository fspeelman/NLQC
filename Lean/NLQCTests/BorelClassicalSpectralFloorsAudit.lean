import NLQCLean.Approx.BorelClassicalSpectralFloors

/-! Full types and standard-axiom checks for quantum-footprint Borel floors.
Source proof label: `lem:free-classical-floors`.
The actual channel definitions and architecture fields are printed as well. -/

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

#print NLQCLean.ClassicalCommunication.BorelSystems
#print NLQCLean.ClassicalCommunication.BorelRandomSystems
#print NLQCLean.ClassicalCommunication.BorelSystems.Protocol
#print NLQCLean.ClassicalCommunication.BorelRandomSystems.Protocol
#print NLQCLean.ClassicalCommunication.borelScoreReachable
#print NLQCLean.ClassicalCommunication.borelPVMScoreReachable
#print NLQCLean.ClassicalCommunication.borelSharedRandomScoreReachable
#print NLQCLean.ClassicalCommunication.borelSharedRandomPVMScoreReachable
#print NLQCLean.ClassicalCommunication.borelAllScoreReachable
#print NLQCLean.ClassicalCommunication.borelAllPVMScoreReachable

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scoreU_le_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scoreU_le_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scoreU_le_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scorePVM_le_max_column_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scorePVM_le_max_column_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.scorePVM_le_max_column_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scoreU_le_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scoreU_le_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scoreU_le_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scorePVM_le_max_column_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scorePVM_le_max_column_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_scorePVM_le_max_column_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_exact_schmidt_rank_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_exact_schmidt_rank_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_exact_schmidt_rank_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_exact_schmidt_rank_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_exact_schmidt_rank_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_exact_schmidt_rank_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.swap_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.swap_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.swap_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_swap_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_swap_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_swap_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.generalizedBellPVM_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.generalizedBellPVM_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.generalizedBellPVM_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_generalizedBellPVM_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_generalizedBellPVM_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_generalizedBellPVM_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_spectral_floor_of_diamondError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_spectral_floor_of_diamondError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.unitary_spectral_floor_of_diamondError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_spectral_floor_of_diamondError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_spectral_floor_of_diamondError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_unitary_spectral_floor_of_diamondError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_spectral_floor_of_pvmTVError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_spectral_floor_of_pvmTVError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.pvm_spectral_floor_of_pvmTVError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_spectral_floor_of_pvmTVError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_spectral_floor_of_pvmTVError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixed_pvm_spectral_floor_of_pvmTVError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scoreU_le_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scoreU_le_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scoreU_le_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scorePVM_le_max_column_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scorePVM_le_max_column_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_scorePVM_le_max_column_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_exact_schmidt_rank_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_exact_schmidt_rank_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_exact_schmidt_rank_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_swap_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_swap_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_swap_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_generalizedBellPVM_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_generalizedBellPVM_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_generalizedBellPVM_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_spectral_floor_of_diamondError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_spectral_floor_of_diamondError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_unitary_spectral_floor_of_diamondError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_spectral_floor_of_pvmTVError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_spectral_floor_of_pvmTVError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.sharedRandom_pvm_spectral_floor_of_pvmTVError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scoreU_le_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scoreU_le_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scoreU_le_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scorePVM_le_max_column_schmidtMass
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scorePVM_le_max_column_schmidtMass' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_scorePVM_le_max_column_schmidtMass

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_full_spectral_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_full_spectral_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_full_spectral_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_exact_schmidt_rank_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_exact_schmidt_rank_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_exact_schmidt_rank_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_swap_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_swap_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_swap_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_generalizedBellPVM_quantumFootprint_floor

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_spectral_floor_of_diamondError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_spectral_floor_of_diamondError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_unitary_spectral_floor_of_diamondError

#print NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_spectral_floor_of_pvmTVError
/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_spectral_floor_of_pvmTVError' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.mixedSharedRandom_pvm_spectral_floor_of_pvmTVError

#print NLQCLean.ClassicalCommunication.ae_borel_classical_full_spectral_threshold
/-- info: 'NLQCLean.ClassicalCommunication.ae_borel_classical_full_spectral_threshold' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.ae_borel_classical_full_spectral_threshold
