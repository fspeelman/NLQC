import NLQCLean.Exact.PVMPathFactorization
import NLQCLean.Exact.PaperFoundations
import NLQCLean.Semialgebraic.PiecewiseC1
import NLQCLean.Semialgebraic.Paths
import NLQCLean.Exact.FiniteUnion
import NLQCLean.Exact.CompressionFiniteOrbits
import NLQCLean.Exact.UnequalDimensions
import NLQCLean.Exact.RigidityStatements
import NLQCLean.Exact.BitstringExactExclusion
import NLQCLean.Exact.OrbitInvariantAlgebraicity
import NLQCLean.Bounds.AlmostEveryExact
import NLQCLean.Bounds.FiniteLocalization
import NLQCLean.Invariants.SpectatorControlledPhasePurity

/-!
# The exact paper, by source label

Reader-facing names for the results of the exact paper (finite-resource
one-round non-local quantum computation). Each alias is named after the
source label it formalizes. All are proved without external premises.

The orbit-finiteness results are proved with a finite family of separating
polynomial invariants instead of the source's connected-component and
semialgebraic-path route. The source's `lem:finiteunion` and the cited
textbook facts `fact:components`, `fact:paths` and `fact:piecewise` are also
proved (by a cylindrical decomposition into semialgebraically path-connected
pieces), but the other results do not depend on them.
-/

namespace NLQCLean.Results.ExactPaper

/-! ### Preliminaries -/

/-- `lem:compression_state`. -/
alias lem_compression_state := NLQCLean.compression_state
/-- `def:orbit` is `NLQCLean.unitaryDoubleOrbit`; `lem:orbitHaarNull`, for all
local dimensions at least two. -/
alias lem_orbitHaarNull := NLQCLean.unitaryHaar_unitaryDoubleOrbit_eq_zero
/-- The source Haar measure. -/
alias def_haar_measure := NLQCLean.unitaryHaar_isHaar_characterization
/-- `fact:stinespring`. -/
alias fact_stinespring := NLQCLean.exists_stinespring
/-- `fact:TS`, projection and coordinate functions. -/
alias fact_TS := NLQCLean.fact_TS_projection
alias fact_TS_coordinates := NLQCLean.SemialgebraicMapOn.coordinate
/-- `fact:linear-ode`. -/
alias fact_linear_ode := NLQCLean.linearODE_existsUnique
alias fact_linear_ode_matrix := NLQCLean.linearODE_existsUnique_matrix
/-- `fact:components`. -/
alias fact_components := NLQCLean.fact_components
/-- `fact:paths`. -/
alias fact_paths := NLQCLean.fact_paths
/-- `fact:piecewise`, scalar and coordinatewise vector forms. -/
alias fact_piecewise := NLQCLean.fact_piecewise
alias fact_piecewise_vector := NLQCLean.fact_piecewise_vector

/-! ### The unitary task -/

/-- `thm:badHaarNull`, by orbit counting. -/
alias thm_badHaarNull := NLQCLean.unitaryHaar_exactUnitaryBad_eq_zero
/-- `thm:badHaarNull`, almost-every form with arbitrary finite registers and
common-map mixed resources. -/
alias thm_badHaarNull_ae := NLQCLean.ae_unitary_no_finite_exact_implementation
/-- `rem:qudits`. -/
alias rem_qudits := NLQCLean.ae_unitary_no_exact_protocol_gen
/-- `lem:rigidity`. -/
alias lem_rigidity := NLQCLean.rigidity_of_pure_states
/-- `cor:reformulation`. -/
alias cor_reformulation := NLQCLean.PureProtocol.performsUnitary_iff_frozen
/-- `lem:frozendilation`. -/
alias lem_frozendilation := NLQCLean.mem_exactUnitaryBad_iff_frozen
/-- `def:strategy` is `NLQCLean.targetExactWitnessSet`; `lem:algebraic`. -/
alias lem_algebraic := NLQCLean.exactUnitaryBad_eq_iUnion_exactTargets
alias lem_algebraic_arbitrary_registers := NLQCLean.PureProtocol.mem_exactUnitaryBad
/-- `rem:compression`. -/
alias rem_compression := NLQCLean.exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits
/-- `app:compression`. -/
alias app_compression := NLQCLean.PureProtocol.exists_compressed_forward_bounds
/-- `prop:derivative`. -/
alias prop_derivative := NLQCLean.exists_localSkew_target_velocity
/-- `lem:smoothsameorbit` (for every continuous path). -/
alias lem_smoothsameorbit := NLQCLean.mem_unitaryDoubleOrbit_of_continuousOn_path
/-- `prop:component`. -/
alias prop_component := NLQCLean.mem_unitaryDoubleOrbit_of_mem_connectedComponentIn
/-- `cor:archOnlyFiniteOrbits`. -/
alias cor_archOnlyFiniteOrbits := NLQCLean.exists_finset_exactTargets_eq_iUnion_orbits
/-- `lem:finiteunion`: `Bad` is the union over architectures and the finitely
many connected components of each strategy set. -/
alias lem_finiteunion := NLQCLean.exactUnitaryBad_eq_iUnion_strategyComponents
alias lem_finiteunion_components := NLQCLean.exactUnitaryBad_eq_iUnion_components
/-- `lem:finiteunionoforbits`. -/
alias lem_finiteunionoforbits := NLQCLean.exists_exactUnitaryBad_eq_iUnion_orbits

/-! ### The explicit target -/

/-- `lem:algebraic-values`. -/
alias lem_algebraic_values := NLQCLean.PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary
alias lem_algebraic_values_mixed := NLQCLean.MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq
/-- `lem:purity`. -/
alias lem_purity := NLQCLean.purity_bitstringControlledPhase
/-- `lem:purity`, first assertion: the operator purity is a rational polynomial in the
real and imaginary parts of the entries and is constant on every local-unitary orbit,
the hypotheses of `lem:algebraic-values`. -/
alias lem_purity_invariant := NLQCLean.purity_isRationalOrbitInvariant
/-- `thm:explicit-gate`: exact implementation of `C_θ` forces `exp(iθ)` to be
algebraic; `C_1` and its full local orbit are not exactly implementable. -/
alias thm_explicit_gate := NLQCLean.PureProtocol.isAlgebraic_exp_angle_of_performsUnitary_bitstringControlledPhase
alias thm_explicit_gate_mixed :=
  NLQCLean.MixedResource.isAlgebraic_exp_angle_of_mixedChannel_eq_bitstringControlledPhase
alias thm_explicit_gate_one := NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one
alias thm_explicit_gate_one_orbit :=
  NLQCLean.PureProtocol.not_performsUnitary_bitstringControlledPhase_one_orbit

/-! ### Measurements -/

/-- `thm:measHaarNull` (i). -/
alias thm_measHaarNull_i := NLQCLean.exists_finset_pvmExactTargets_eq_iUnion_orbits
/-- `thm:measHaarNull` (ii). -/
alias thm_measHaarNull_ii := NLQCLean.unitaryHaar_exactPVMBad_eq_zero
alias thm_measHaarNull_ii_ae := NLQCLean.ae_pvm_no_finite_exact_implementation
/-- `lem:rigidity-pvm`. -/
alias lem_rigidity_pvm := NLQCLean.twoSidedExact_iff_flag
/-- `lem:labels`. -/
alias lem_labels := NLQCLean.duplicated_labels
/-- `lem:algebraic-pvm`: the strategy locus is a polynomial zero set, and the
fixed-architecture targets are the implementable basis matrices. -/
alias lem_algebraic_pvm_i := NLQCLean.isPolyZeroSet_isExactPVMWitness
alias lem_algebraic_pvm_ii := NLQCLean.pvmExactTargets_eq_protocols
alias lem_algebraic_pvm_union := NLQCLean.exactPVMBad_eq_iUnion_pvmExactTargets
/-- `prop:derivative-pvm`. -/
alias prop_derivative_pvm := NLQCLean.exists_continuous_pvm_generators
/-- `lem:smoothsameorbit-pvm`. -/
alias lem_smoothsameorbit_pvm := NLQCLean.pvm_path_factorization
/-- `prop:component-pvm`. -/
alias prop_component_pvm := NLQCLean.mem_pvmBasisOrbit_of_mem_connectedComponentIn
/-- `lem:orbitHaarNull-pvm`. -/
alias lem_orbitHaarNull_pvm := NLQCLean.unitaryHaar_pvmBasisOrbit_eq_zero
/-- `cor:localizable`. -/
alias cor_localizable := NLQCLean.ClassicalCommunication.finite_exact_localization_haar_null

end NLQCLean.Results.ExactPaper
