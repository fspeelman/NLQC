import NLQCLean.Models.NearBellResourceFloors
import NLQCLean.Approx.NearBellFreezing

/-!
# Near-Bell physical reference and witness audit

Full types distinguish the actual PVM reference probe from a unitary target
message statement. The normalized local pair, retained-reference encoder,
controlled correction and reference projection are checked before the floors.
-/

set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.nearBellLocalReferencePair_isUnitVector
#print axioms NLQCLean.nearBellLocalReferencePair_isUnitVector

set_option pp.universes true in
#check @NLQCLean.nearBellCorrectedReferenceDecoder_isometry
#print axioms NLQCLean.nearBellCorrectedReferenceDecoder_isometry

set_option pp.universes true in
#check @NLQCLean.nearBellReferenceEncoder_isometry
#print axioms NLQCLean.nearBellReferenceEncoder_isometry

set_option pp.universes true in
#check @NLQCLean.nearBellReferenceResource_isUnitVector
#print axioms NLQCLean.nearBellReferenceResource_isUnitVector

set_option pp.universes true in
#check @NLQCLean.nearBellReferenceProjection_norm_sq_le
#print axioms NLQCLean.nearBellReferenceProjection_norm_sq_le

set_option pp.universes true in
#check @NLQCLean.nearBellReference_crossedAmplitude_eq_projection
#print axioms NLQCLean.nearBellReference_crossedAmplitude_eq_projection

set_option pp.universes true in
#check @NLQCLean.nearBellReferenceProjection_messageA_upper
#print axioms NLQCLean.nearBellReferenceProjection_messageA_upper
