import NLQCLean.Results.Unitary
import NLQCLean.Exact.OrbitInvariantAlgebraicity

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

set_option pp.universes true in
#check @NLQCLean.exactWitnessInvariantMap_image
set_option pp.universes true in
#check @NLQCLean.rationalSemialgebraic_shapeInvariantValues
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_of_mem_shapeInvariantValues
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_of_mem_exactInvariantValues
set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_rationalInvariant_of_performsUnitary
set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_rationalInvariant_of_mixedChannel_eq

/-- info: 'NLQCLean.exactWitnessInvariantMap_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exactWitnessInvariantMap_image

/-- info: 'NLQCLean.rationalSemialgebraic_shapeInvariantValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.rationalSemialgebraic_shapeInvariantValues

/-- info: 'NLQCLean.isAlgebraic_of_mem_shapeInvariantValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isAlgebraic_of_mem_shapeInvariantValues

/-- info: 'NLQCLean.isAlgebraic_of_mem_exactInvariantValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isAlgebraic_of_mem_exactInvariantValues

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_rationalInvariant_of_performsUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_rationalInvariant_of_performsUnitary

/-- info: 'NLQCLean.MixedResource.isAlgebraic_rationalInvariant_of_mixedChannel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_rationalInvariant_of_mixedChannel_eq

set_option pp.universes true in
#check @NLQCLean.PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary

/-- info: 'NLQCLean.PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary

set_option pp.universes true in
#check @NLQCLean.MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq

/-- info: 'NLQCLean.MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_orbit_invariant_algebraic

/-- info: 'NLQCLean.Results.Unitary.pure_orbit_invariant_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.pure_orbit_invariant_algebraic

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_orbit_invariant_algebraic

/-- info: 'NLQCLean.Results.Unitary.mixed_orbit_invariant_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.mixed_orbit_invariant_algebraic

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.pure_rational_orbit_invariant_algebraic

/-- info: 'NLQCLean.Results.Unitary.pure_rational_orbit_invariant_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.pure_rational_orbit_invariant_algebraic

set_option pp.universes true in
#check @NLQCLean.Results.Unitary.mixed_rational_orbit_invariant_algebraic

/-- info: 'NLQCLean.Results.Unitary.mixed_rational_orbit_invariant_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.Results.Unitary.mixed_rational_orbit_invariant_algebraic
