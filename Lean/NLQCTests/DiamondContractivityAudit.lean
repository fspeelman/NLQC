import NLQCLean.Models.StinespringDiamondContractivity

/-! # All-complex-matrix and all-ancilla diamond contractivity -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.frobInner_ptraceB

/-- info: 'NLQCLean.frobInner_ptraceB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.frobInner_ptraceB

set_option pp.universes true in
#check @NLQCLean.traceNorm_ptraceB_le

/-- info: 'NLQCLean.traceNorm_ptraceB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.traceNorm_ptraceB_le

set_option pp.universes true in
#check @NLQCLean.traceNorm_channelOf_le

/-- info: 'NLQCLean.traceNorm_channelOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.traceNorm_channelOf_le

set_option pp.universes true in
#check @NLQCLean.amplify_channelOf

/-- info: 'NLQCLean.amplify_channelOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.amplify_channelOf

set_option pp.universes true in
#check @NLQCLean.traceNorm_amplify_adConj_isometry

/-- info: 'NLQCLean.traceNorm_amplify_adConj_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.traceNorm_amplify_adConj_isometry

set_option pp.universes true in
#check @NLQCLean.diamondNorm_stinespring_isometry_sandwich_le

/-- info: 'NLQCLean.diamondNorm_stinespring_isometry_sandwich_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.diamondNorm_stinespring_isometry_sandwich_le

set_option pp.universes true in
#check @NLQCLean.diamondError_stinespring_isometry_sandwich_le

/-- info: 'NLQCLean.diamondError_stinespring_isometry_sandwich_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.diamondError_stinespring_isometry_sandwich_le
