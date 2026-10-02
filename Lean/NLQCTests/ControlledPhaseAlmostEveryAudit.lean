import NLQCLean.Bounds.ControlledPhaseAlmostEvery
import NLQCLean.Bounds.FiniteControlledPhaseAlmostEvery

/-!
# Charged almost-every controlled-phase resource rates

Full types expose all measure, normalization, model and external premises.
-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound

/-- info: 'NLQCLean.exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound

set_option pp.universes true in
#check @NLQCLean.exists_ae_chargedControlledPhase_resource_constant

/-- info: 'NLQCLean.exists_ae_chargedControlledPhase_resource_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_chargedControlledPhase_resource_constant

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound

/-- info: 'NLQCLean.exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteControlledPhase_log_bound_of_imageVolumeBound

set_option pp.universes true in
#check @NLQCLean.exists_ae_finiteControlledPhase_log_bound

/-- info: 'NLQCLean.exists_ae_finiteControlledPhase_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_ae_finiteControlledPhase_log_bound
