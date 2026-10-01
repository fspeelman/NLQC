import NLQCLean.Models.ClassicalCommunication.BorelOperationalChannel

/-! # Whole operational integrals independent of RN versions -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.integrable_jointDensityChannel

/-- info: 'NLQCLean.ClassicalCommunication.integrable_jointDensityChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.integrable_jointDensityChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_ae_eq

/-- info: 'NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.CPVectorInstrument.reconstructed_density_ae_eq

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_operationDensity

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_operationDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.integrable_operationDensity

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.score_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.score_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.score_operationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.linearScore_operationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_eq_of_reconstructed_densities

/-- info: 'NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_eq_of_reconstructed_densities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol.operationalChannel_eq_of_reconstructed_densities
