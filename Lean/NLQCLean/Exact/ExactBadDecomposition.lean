import NLQCLean.Exact.FiniteOrbits
import NLQCLean.Geometry.LocalOrbitHaarNull

/-!
# The exactly implementable unitaries: architecture decomposition

`exactUnitaryBad d` is the set of unitaries on `ℂ^d ⊗ ℂ^d` with an exact
one-round protocol on finite registers. It is exactly the countable union
over dimension vectors of the fixed-architecture exact target sets
(`lem:algebraic`), hence contained in a countable union of local-unitary
orbits (`lem:finiteunionoforbits`), and Haar-null (`thm:badHaarNull`) by the
source's orbit-counting route.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

section Witnesses

variable {d : ℕ}
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- An exact witness on arbitrary finite registers is transported to the
dimension vector of its register cardinalities, with the same target. -/
theorem exists_shape_mem_exactTargets_of_isExactWitness
    {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactWitness x) :
    ∃ s : ForwardShape, forwardOverlapOn x ∈ exactTargets d s := by
  let rA := (Fintype.equivFin ρA).symm
  let rB := (Fintype.equivFin ρB).symm
  let kA := (Fintype.equivFin κA).symm
  let kB := (Fintype.equivFin κB).symm
  let mA := (Fintype.equivFin μA).symm
  let mB := (Fintype.equivFin μB).symm
  let eA := (Fintype.equivFin εA).symm
  let eB := (Fintype.equivFin εB).symm
  let s : ForwardShape := ![Fintype.card ρA, Fintype.card ρB,
    Fintype.card κA, Fintype.card κB, Fintype.card μA, Fintype.card μB,
    Fintype.card εA, Fintype.card εB]
  let y : ShapeBlocks d s := reindexForwardBlocks rA rB kA kB mA mB eA eB x
  have hH : forwardOverlapOn y = forwardOverlapOn x :=
    forwardOverlapOn_reindex rA rB kA kB mA mB eA eB x
  have hy : IsExactWitness y := by
    refine ⟨hx.resource_unit.comp_equiv (rA.prodCongr rB),
      hx.witness_unit.comp_equiv (eA.prodCongr eB),
      hx.encA_isometry.submatrix_equiv _ _, hx.encB_isometry.submatrix_equiv _ _,
      hx.decA_isometry.submatrix_equiv _ _, hx.decB_isometry.submatrix_equiv _ _,
      ?_, ?_, ?_⟩
    · exact (isIsometry_decoder
        (hx.decA_isometry.submatrix_equiv _ _)
        (hx.decB_isometry.submatrix_equiv _ _)).submatrix_equiv
          (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _)
    · rw [hH]
      exact hx.overlap_coisometry
    · rw [← globalIsometryRegrouped_eq]
      have hreg : globalIsometryRegrouped y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 =
          (globalIsometryRegrouped x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2).submatrix
            ((Equiv.refl (Fin d × Fin d)).prodCongr (eA.prodCongr eB)) id :=
        globalIsometryRegrouped_reindex rA rB kA kB mA mB eA eB x
      rw [hreg, globalIsometryRegrouped_eq, hx.exact, hH]
      exact (Matrix.submatrix_mul _ _ _ id id Function.bijective_id).trans (by
        rw [Matrix.submatrix_id_id]
        rfl)
  exact ⟨s, (forwardOverlapOn y, y), (mem_targetExactWitnessSet_iff d s _).mpr ⟨hy, rfl⟩, hH⟩

/-- A protocol performing a unitary on arbitrary finite registers places it in
the exact targets of the dimension vector of its register cardinalities. -/
theorem PureProtocol.exists_shape_mem_exactTargets [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) :
    ∃ s : ForwardShape, U ∈ exactTargets d s := by
  have hscore : scoreU U P.operationalChannel = 1 := by
    rw [show P.operationalChannel = adConj U from htask]
    exact scoreU_adConj_self hU.isIsometry
  let F := globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB
  have hF : IsIsometry F :=
    P.isIsometry_globalIsometry.submatrix_equiv
      (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
  let g := scoreVector U F
  have hg : IsUnitVector g := (isUnitVector_scoreVector_iff U F).mpr hscore
  have hFr : F = insertVector (Fin d × Fin d) g * U :=
    (scoreU_eq_one_iff hU.isIsometry hF).mp hscore
  let x : BalancedBlocks d ρA ρB κA κB μA μB εA εB :=
    (P.resource, g, P.encA, P.encB, P.decA, P.decB)
  have hH : forwardOverlapOn x = U := by
    change (insertVector (Fin d × Fin d) g)ᴴ * F = U
    rw [hFr, ← Matrix.mul_assoc, (isIsometry_insertVector g hg).conjTranspose_mul_self,
      Matrix.one_mul]
  have hx : IsExactWitness x := by
    refine ⟨P.resource_unit, hg, P.encA_isometry, P.encB_isometry,
      P.decA_isometry, P.decB_isometry, ?_, ?_, ?_⟩
    · exact (isIsometry_decoder P.decA_isometry P.decB_isometry).submatrix_equiv
        (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
    · rw [hH]
      exact hU.self_mul_conjTranspose
    · rw [← globalIsometryRegrouped_eq, hH]
      exact hFr
  simpa only [hH] using exists_shape_mem_exactTargets_of_isExactWitness hx

end Witnesses

section Bad

variable {d : ℕ}

/-- The protocol encoded by a point of the fixed-architecture exact set. -/
def targetExactWitnessProtocol (s : ForwardShape)
    {z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    (hz : z ∈ targetExactWitnessSet d s) :
    PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)) where
  resource := z.2.1
  resource_unit := hz.1.1
  encA := z.2.2.2.1
  encB := z.2.2.2.2.1
  encA_isometry := hz.1.2.1
  encB_isometry := hz.1.2.2.1
  decA := z.2.2.2.2.2.1
  decB := z.2.2.2.2.2.2
  decA_isometry := hz.1.2.2.2.1
  decB_isometry := hz.1.2.2.2.2

/-- A point of the fixed-architecture exact set gives a protocol performing
its target exactly. -/
theorem targetExactWitnessProtocol_performsUnitary (s : ForwardShape)
    {z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    (hz : z ∈ targetExactWitnessSet d s) :
    (targetExactWitnessProtocol s hz).PerformsUnitary z.1 := by
  change channelOf (globalIsometryRegrouped z.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1
    z.2.2.2.2.2.2) = adConj z.1
  rw [hz.2.2.2]
  exact channelOf_insertVector_mul hz.2.1 z.1

/-- **The exactly implementable unitaries** (`thm:badHaarNull`): unitaries on
`ℂ^d ⊗ ℂ^d` performed exactly by some one-round protocol with finite
registers. Arbitrary finite register types reduce to this presentation by
`PureProtocol.mem_exactUnitaryBad`. -/
def exactUnitaryBad (d : ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {U | UnitaryTarget U ∧ ∃ s : ForwardShape,
    ∃ P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)), P.PerformsUnitary U}

theorem unitaryTarget_of_mem_exactTargets {s : ForwardShape}
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : U ∈ exactTargets d s) :
    UnitaryTarget U := by
  obtain ⟨z, hz, rfl⟩ := hU
  exact ⟨mul_eq_one_comm.mp hz.2.2.1, hz.2.2.1⟩

/-- **`lem:algebraic`.** The exactly implementable unitaries are the countable
union, over all dimension vectors, of the fixed-architecture target sets. -/
theorem exactUnitaryBad_eq_iUnion_exactTargets [NeZero d] :
    exactUnitaryBad d = ⋃ s : ForwardShape, exactTargets d s := by
  ext U
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hU, s, P, hP⟩
    exact P.exists_shape_mem_exactTargets hU hP
  · rintro ⟨s, hs⟩
    refine ⟨unitaryTarget_of_mem_exactTargets hs, s, ?_⟩
    obtain ⟨z, hz, rfl⟩ := hs
    exact ⟨_, targetExactWitnessProtocol_performsUnitary s hz⟩

/-- A protocol on arbitrary finite registers, in arbitrary universes,
performing a unitary exactly places it in `exactUnitaryBad`. -/
theorem PureProtocol.mem_exactUnitaryBad [NeZero d]
    {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
    {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) : U ∈ exactUnitaryBad d := by
  rw [exactUnitaryBad_eq_iUnion_exactTargets]
  exact Set.mem_iUnion.mpr (P.exists_shape_mem_exactTargets hU htask)

/-- **`lem:finiteunionoforbits` and `cor:archOnlyFiniteOrbits` combined.** The
exactly implementable unitaries are a countable union, over dimension vectors,
of finite unions of full local-unitary orbits of implementable unitaries. -/
theorem exists_exactUnitaryBad_eq_iUnion_orbits [NeZero d] :
    ∃ R : ForwardShape → Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ s, ∀ U ∈ R s, U ∈ exactUnitaryBad d) ∧
        exactUnitaryBad d = ⋃ s : ForwardShape, ⋃ U ∈ R s, unitaryDoubleOrbit (Fin d) (Fin d) U := by
  choose R hR hReq using fun s => exists_finset_exactTargets_eq_iUnion_orbits d s
  refine ⟨R, fun s U hU => ?_, ?_⟩
  · rw [exactUnitaryBad_eq_iUnion_exactTargets]
    exact Set.mem_iUnion.mpr ⟨s, hR s U hU⟩
  · rw [exactUnitaryBad_eq_iUnion_exactTargets]
    exact Set.iUnion_congr hReq

/-- **`thm:badHaarNull`, by orbit counting.** For `d ≥ 2`, the exactly
implementable unitaries form a Haar-null set: a countable union of finitely
many Haar-null local orbits per architecture. -/
theorem unitaryHaar_exactUnitaryBad_eq_zero (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d)
      {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
        (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ exactUnitaryBad d} = 0 := by
  have : NeZero d := ⟨by omega⟩
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨R, -, hR⟩ := exists_exactUnitaryBad_eq_iUnion_orbits (d := d)
  have hset : {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
      (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ exactUnitaryBad d} =
      ⋃ s : ForwardShape, ⋃ U ∈ R s, {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
        (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ unitaryDoubleOrbit (Fin d) (Fin d) U} := by
    ext V
    simp only [Set.mem_ofPred_eq, hR, Set.mem_iUnion]
  rw [hset]
  refine measure_iUnion_null fun s => ?_
  refine (measure_biUnion_null_iff (R s).countable_toSet).mpr fun U _ => ?_
  exact unitaryHaar_unitaryDoubleOrbit_eq_zero U

/-- **`lem:finiteunion`, without the component count.** `Bad` is the union,
over architectures and connected components of each strategy set, of the
targets implemented by the component. That each strategy set has finitely
many components is proved separately by `fact_components` in
`NLQCLean.Semialgebraic.Components`; this decomposition does not use that count. -/
theorem exactUnitaryBad_eq_iUnion_components [NeZero d] :
    exactUnitaryBad d = ⋃ s : ForwardShape, ⋃ z ∈ targetExactWitnessSet d s,
      Prod.fst '' connectedComponentIn (targetExactWitnessSet d s) z := by
  rw [exactUnitaryBad_eq_iUnion_exactTargets]
  refine Set.iUnion_congr fun s => ?_
  ext U
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, z, mem_connectedComponentIn hz, rfl⟩
  · rintro ⟨z, -, y, hy, rfl⟩
    exact ⟨y, connectedComponentIn_subset _ _ hy, rfl⟩

end Bad

end NLQCLean
