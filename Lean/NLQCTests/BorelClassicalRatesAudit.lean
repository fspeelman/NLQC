import NLQCLean.Bounds.BorelClassicalRates

/-! Full types and standard-axiom guards for actual original-channel Borel rates.
The intrinsic data and target definitions are printed alongside their witnesses.
External quantitative wrappers expose exactly the three geometry premises. -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

#print NLQCLean.ClassicalCommunication.BorelSystems

#print NLQCLean.ClassicalCommunication.BorelRandomSystems

#print NLQCLean.ClassicalCommunication.borelAllScoreReachable

#print NLQCLean.ClassicalCommunication.borelAllPVMScoreReachable

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.BorelSystems.ofTypes

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.BorelRandomSystems.ofTypes

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_quantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelScoreReachable_of_mixedQuantumFootprint_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_quantumFootprint_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelPVMScoreReachable_of_mixedQuantumFootprint_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_sharedRandom_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom_diamondError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom_diamondError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomScoreReachable_of_mixedSharedRandom_diamondError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_sharedRandom_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom_pvmTVError

/-- info: 'NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom_pvmTVError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.mem_borelSharedRandomPVMScoreReachable_of_mixedSharedRandom_pvmTVError

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_haar_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_haar_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_unitary_universal_log_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_pvm_universal_log_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_borel_classical_strong_unitary_universal_log_constant_of_external

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant

/-- info: 'NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant_of_external

/-- info: 'NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant_of_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_ae_borel_classical_log_constant_of_external
