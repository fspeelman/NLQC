import NLQCLean.Models.ClassicalCommunication.InstrumentCompression
import NLQCLean.Models.ClassicalCommunication.KrausRepresentation
import NLQCLean.Models.ClassicalCommunication.FiniteProtocol
import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Models.ClassicalCommunication.TensorChannels
import NLQCLean.Models.ClassicalCommunication.ProtocolCompression

/-!
# Finite instrument and charged conversion boundaries

Full types retain input/output systems, all premises and constants.

-/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.normalized_marginal_score_mem_convexHull

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.normalized_marginal_score_mem_convexHull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteKrausInstrument.normalized_marginal_score_mem_convexHull

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_preserving_compression

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_preserving_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_preserving_compression

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.completelyPositive_iff_exists_kraus

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_iff_exists_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_iff_exists_kraus

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.completelyPositive_iff_choiMatrix_posSemidef

/-- info: 'NLQCLean.ClassicalCommunication.completelyPositive_iff_choiMatrix_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.completelyPositive_iff_choiMatrix_posSemidef

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_instrument_iff_completelyPositive_trace_preserving

/-- info: 'NLQCLean.ClassicalCommunication.exists_instrument_iff_completelyPositive_trace_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_instrument_iff_completelyPositive_trace_preserving

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_ofPureProtocol

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_ofPureProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.operationalChannel_ofPureProtocol

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.quantumFootprint_ofPureProtocol

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.quantumFootprint_ofPureProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.quantumFootprint_ofPureProtocol

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint_iff

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint_iff

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_hasFootprint

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_operationalChannel

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_operationalChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.coherentProtocol_operationalChannel

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.tensorChannels_adConj

/-- info: 'NLQCLean.ClassicalCommunication.tensorChannels_adConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.tensorChannels_adConj

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.tensorChannels_krausMap

/-- info: 'NLQCLean.ClassicalCommunication.tensorChannels_krausMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.tensorChannels_krausMap

#check @NLQCLean.ClassicalCommunication.exists_pruned_weights

/-- info: 'NLQCLean.ClassicalCommunication.exists_pruned_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_pruned_weights

#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_nondecreasing_compression

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_nondecreasing_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteKrausInstrument.exists_score_nondecreasing_compression

#check @NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_nondecreasing_linearScore

/-- info: 'NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_nondecreasing_linearScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteClassicalProtocol.exists_finiteOutcome_compression_nondecreasing_linearScore
