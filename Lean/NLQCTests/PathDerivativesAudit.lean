import NLQCLean.Exact.PathDerivatives
import NLQCLean.LinearAlgebra.LinearODE

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.linearODE_existsUnique

set_option pp.universes true in
#check @NLQCLean.linearODE_existsUnique_matrix

set_option pp.universes true in
#check @NLQCLean.exists_localSkew_target_velocity

set_option pp.universes true in
#check @NLQCLean.pvm_target_velocity

set_option pp.universes true in
#check @NLQCLean.exists_continuous_pvm_generators

/-- info: 'NLQCLean.linearODE_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.linearODE_existsUnique

/-- info: 'NLQCLean.linearODE_existsUnique_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.linearODE_existsUnique_matrix

/-- info: 'NLQCLean.exists_localSkew_target_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_localSkew_target_velocity

/-- info: 'NLQCLean.pvm_target_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvm_target_velocity

/-- info: 'NLQCLean.exists_continuous_pvm_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_continuous_pvm_generators
