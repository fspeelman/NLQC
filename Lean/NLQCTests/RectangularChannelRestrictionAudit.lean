import NLQCLean.Models.ClassicalCommunication.RectangularDiagonalRestriction

/-! # Corrected rectangular channels and original normalized error -/

set_option pp.universes false
set_option pp.deepTerms true
set_option format.width 120

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderStinespring_isometry

/-- info: 'NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderStinespring_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderStinespring_isometry

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderChannel_trace

/-- info: 'NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderChannel_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.correctedTwoLevelDecoderChannel_trace

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_eq_local_tensor

/-- info: 'NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_eq_local_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_eq_local_tensor

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_trace

/-- info: 'NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.rectangularDiagonalDecoderChannel_trace

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.rectangularDiagonalRestrictedChannel_ideal

/-- info: 'NLQCLean.ClassicalCommunication.rectangularDiagonalRestrictedChannel_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.rectangularDiagonalRestrictedChannel_ideal

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_le

/-- info: 'NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_le

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_target_le

/-- info: 'NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_target_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.diamondError_rectangularDiagonalRestrictedChannel_target_le

open NLQCLean NLQCLean.ClassicalCommunication

-- Unequal local dimensions and arbitrary linear maps are retained.
example (θ : Fin 2 × Fin 3 → ℝ)
    (Φ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    diamondError (rectangularDiagonalRestrictedChannel (by decide : 2 ≤ 2)
      (by decide : 2 ≤ 3) θ Φ)
        (adConj (controlledPhase (rectangularAlternatingAngle
          (by decide : 2 ≤ 2) (by decide : 2 ≤ 3) θ))) ≤
      diamondError Φ (adConj (rectangularDiagonalPhase θ)) :=
  diamondError_rectangularDiagonalRestrictedChannel_target_le _ _ θ Φ
