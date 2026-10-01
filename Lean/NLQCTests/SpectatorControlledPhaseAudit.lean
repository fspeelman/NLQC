import NLQCLean.Exact.SpectatorControlledPhase

/-! Full statements and standard-axiom checks for actual spectator controlled-phase restriction. -/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase
set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_apply
set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_unitary
set_option pp.universes true in
#check @NLQCLean.spectatorInputIsometry_isometry
set_option pp.universes true in
#check @NLQCLean.spectatorOutputStinespring_isometry
set_option pp.universes true in
#check @NLQCLean.spectatorEnvironment_unit
set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_intertwines
set_option pp.universes true in
#check @NLQCLean.spectatorOutputRegrouped_mul_input
set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_frozen_restriction
set_option pp.universes true in
#check @NLQCLean.spectatorControlledPhase_restrictedChannel_eq

/-- info: 'NLQCLean.spectatorControlledPhase_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.spectatorControlledPhase_unitary

/-- info: 'NLQCLean.spectatorInputIsometry_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.spectatorInputIsometry_isometry

/-- info: 'NLQCLean.spectatorControlledPhase_restrictedChannel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.spectatorControlledPhase_restrictedChannel_eq

open Matrix NLQCLean NLQCLean.ClassicalCommunication
open scoped Kronecker

universe u v

example {σA : Type u} {σB : Type v} [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (a0 : σA) (b0 : σB) (θ : ℝ) :
    (tensorChannels (channelOf (spectatorOutputStinespring σA))
      (channelOf (spectatorOutputStinespring σB))).comp
        ((adConj (spectatorControlledPhase θ)).comp
          (adConj (spectatorInputIsometry a0 ⊗ₖ spectatorInputIsometry b0))) =
      adConj (controlledPhase θ) :=
  spectatorControlledPhase_restrictedChannel_eq θ a0 b0

example {σA : Type u} {σB : Type v} [Fintype σA] [Fintype σB]
    [DecidableEq σA] [DecidableEq σB] (θ : ℝ) :
    (spectatorControlledPhase (σA := σA) (σB := σB) θ)ᴴ * spectatorControlledPhase θ = 1 ∧
      spectatorControlledPhase (σA := σA) (σB := σB) θ * (spectatorControlledPhase θ)ᴴ = 1 :=
  spectatorControlledPhase_unitary θ
