import NLQCLean.Exact.PVMFiniteOrbits
import NLQCLean.Geometry.LocalOrbitHaarNull
import NLQCLean.Models.ProjectiveProtocolScore
import NLQCLean.Models.ProjectiveExactness

/-!
# Exactly implementable rank-one PVMs: architecture decomposition

`exactPVMBad d` is the set of basis matrices `M ∈ U(d²)` whose ordered
rank-one PVM has an exact two-sided one-round protocol on finite registers.
It is the countable union of the fixed-architecture measurement target sets
(`lem:algebraic-pvm`), a countable union of finitely many measurement orbits
per architecture, and Haar-null (`thm:measHaarNull` (ii)) by orbit counting.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

section Protocols

variable {d : ℕ}
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- A protocol on arbitrary finite registers performing a two-sided PVM task
exactly places its basis matrix in the targets of the dimension vector of its
register cardinalities. -/
theorem PureProtocol.exists_shape_mem_pvmExactTargets [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (htask : P.PerformsPVM M) :
    ∃ s : Fin 8 → ℕ, M ∈ pvmExactTargets d s := by
  let s : Fin 8 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card εA, Fintype.card εB]
  let Q := P.reindex (Fintype.equivFin ρA).symm (Fintype.equivFin ρB).symm
    (Fintype.equivFin κA).symm (Fintype.equivFin κB).symm (Fintype.equivFin μA).symm
    (Fintype.equivFin μB).symm (Fintype.equivFin εA).symm (Fintype.equivFin εB).symm
  have hscore : scorePVM M P.operationalChannel = 1 :=
    (P.scorePVM_eq_one_iff_performsPVM hM).mpr htask
  have hQscore : scorePVM M Q.operationalChannel = 1 := by
    rw [P.operationalChannel_reindex]; exact hscore
  have hQ : Q.PerformsPVM M := (Q.scorePVM_eq_one_iff_performsPVM hM).mp hQscore
  have hM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hM
  obtain ⟨ω, hω, hF, -⟩ := Q.exists_frozen_pvm hM hM' hQ
  let x : PVMShapeBlocks d s := (Q.resource, ω, Q.encA, Q.encB, Q.decA, Q.decB)
  have hCC : (flagIsometry ω)ᴴ * flagIsometry ω = 1 := isIsometry_flagIsometry ω hω
  have hT : pvmOverlapOn x = Mᴴ := by
    change (flagIsometry ω)ᴴ * Q.globalIsometry = Mᴴ
    rw [hF, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have hx : IsExactPVMWitness x := by
    refine ⟨Q.resource_unit, hω, Q.encA_isometry, Q.encB_isometry, Q.decA_isometry,
      Q.decB_isometry, ?_, ?_⟩
    · rw [hT, Matrix.conjTranspose_conjTranspose]; exact hM
    · rw [hT]; exact hF
  exact ⟨s, (M, x), ⟨hx, by rw [hT, Matrix.conjTranspose_conjTranspose]⟩, rfl⟩

end Protocols

section Bad

variable {d : ℕ}

/-- The protocol encoded by a point of the fixed-architecture measurement
strategy set. -/
def pvmTargetWitnessProtocol (s : Fin 8 → ℕ)
    {z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hz : z ∈ pvmTargetWitnessSet d s) :
    PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d × Fin d) (Fin d × Fin d) (Fin (s 6)) (Fin (s 7)) where
  resource := z.2.1
  resource_unit := hz.1.resource_unit
  encA := z.2.2.2.1
  encB := z.2.2.2.2.1
  encA_isometry := hz.1.encA_isometry
  encB_isometry := hz.1.encB_isometry
  decA := z.2.2.2.2.2.1
  decB := z.2.2.2.2.2.2
  decA_isometry := hz.1.decA_isometry
  decB_isometry := hz.1.decB_isometry

theorem pvmTargetWitnessProtocol_performsPVM (s : Fin 8 → ℕ)
    {z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hz : z ∈ pvmTargetWitnessSet d s) :
    (pvmTargetWitnessProtocol s hz).PerformsPVM z.1 := by
  change TwoSidedExact (globalIsometry z.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2) z.1
  rw [hz.1.exact, ← hz.2]
  have h := twoSidedExact_flag_mul_adjoint _ hz.1.flag_unit (pvmOverlapOn z.2)ᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

theorem mem_unitaryGroup_of_mem_pvmExactTargets {s : Fin 8 → ℕ}
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : M ∈ pvmExactTargets d s) :
    M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ := by
  obtain ⟨z, hz, rfl⟩ := hM
  rw [Matrix.mem_unitaryGroup_iff', ← hz.2]
  change (pvmOverlapOn z.2)ᴴᴴ * (pvmOverlapOn z.2)ᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact hz.1.overlap_coisometry

/-- **`lem:algebraic-pvm` (ii), one architecture.** The fixed-architecture
measurement targets are exactly the unitary basis matrices with an exact
two-sided protocol of that dimension vector. -/
theorem pvmExactTargets_eq_protocols [NeZero d] (s : Fin 8 → ℕ) :
    pvmExactTargets d s = {M | M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
      ∃ P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
        (Fin (s 4)) (Fin (s 5)) (Fin d × Fin d) (Fin d × Fin d) (Fin (s 6)) (Fin (s 7)),
        P.PerformsPVM M} := by
  ext M
  constructor
  · intro hM
    refine ⟨mem_unitaryGroup_of_mem_pvmExactTargets hM, ?_⟩
    obtain ⟨z, hz, rfl⟩ := hM
    exact ⟨_, pvmTargetWitnessProtocol_performsPVM s hz⟩
  · rintro ⟨hMu, P, hP⟩
    have hM : IsIsometry M := Matrix.mem_unitaryGroup_iff'.mp hMu
    have hM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hM
    obtain ⟨ω, hω, hF, -⟩ := P.exists_frozen_pvm hM hM' hP
    let x : PVMShapeBlocks d s := (P.resource, ω, P.encA, P.encB, P.decA, P.decB)
    have hCC : (flagIsometry ω)ᴴ * flagIsometry ω = 1 := isIsometry_flagIsometry ω hω
    have hT : pvmOverlapOn x = Mᴴ := by
      change (flagIsometry ω)ᴴ * P.globalIsometry = Mᴴ
      rw [hF, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    refine ⟨(M, x), ⟨⟨P.resource_unit, hω, P.encA_isometry, P.encB_isometry, P.decA_isometry,
      P.decB_isometry, ?_, ?_⟩, ?_⟩, rfl⟩
    · rw [hT, Matrix.conjTranspose_conjTranspose]; exact hM
    · rw [hT]; exact hF
    · rw [hT, Matrix.conjTranspose_conjTranspose]

/-- **The exactly implementable rank-one PVM basis matrices**
(`thm:measHaarNull`): unitaries whose ordered PVM has an exact two-sided
protocol with finite registers. Arbitrary finite register types reduce to
this presentation by `PureProtocol.mem_exactPVMBad`. -/
def exactPVMBad (d : ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {M | M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧ ∃ s : Fin 8 → ℕ,
    ∃ P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d × Fin d) (Fin d × Fin d) (Fin (s 6)) (Fin (s 7)),
      P.PerformsPVM M}

/-- **`lem:algebraic-pvm` (ii).** -/
theorem exactPVMBad_eq_iUnion_pvmExactTargets [NeZero d] :
    exactPVMBad d = ⋃ s : Fin 8 → ℕ, pvmExactTargets d s := by
  ext M
  simp only [Set.mem_iUnion, pvmExactTargets_eq_protocols, exactPVMBad, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hM, s, P, hP⟩
    exact ⟨s, hM, P, hP⟩
  · rintro ⟨s, hM, P, hP⟩
    exact ⟨hM, s, P, hP⟩

/-- Arbitrary finite registers in arbitrary universes reduce to `exactPVMBad`. -/
theorem PureProtocol.mem_exactPVMBad [NeZero d]
    {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
    {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) (htask : P.PerformsPVM M) :
    M ∈ exactPVMBad d := by
  rw [exactPVMBad_eq_iUnion_pvmExactTargets]
  exact Set.mem_iUnion.mpr
    (P.exists_shape_mem_pvmExactTargets (Matrix.mem_unitaryGroup_iff'.mp hM) htask)

/-- The exactly implementable basis matrices are a countable union of finite
unions of full measurement orbits. -/
theorem exists_exactPVMBad_eq_iUnion_orbits [NeZero d] :
    ∃ R : (Fin 8 → ℕ) → Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ s, ∀ M ∈ R s, M ∈ exactPVMBad d) ∧
        exactPVMBad d = ⋃ s : Fin 8 → ℕ, ⋃ M ∈ R s, pvmBasisOrbit (Fin d) (Fin d) M := by
  choose R hR hReq using fun s => exists_finset_pvmExactTargets_eq_iUnion_orbits d s
  refine ⟨R, fun s M hM => ?_, ?_⟩
  · rw [exactPVMBad_eq_iUnion_pvmExactTargets]
    exact Set.mem_iUnion.mpr ⟨s, hR s M hM⟩
  · rw [exactPVMBad_eq_iUnion_pvmExactTargets]
    exact Set.iUnion_congr hReq

/-- **`thm:measHaarNull` (ii), by orbit counting.** -/
theorem unitaryHaar_exactPVMBad_eq_zero (hd : 2 ≤ d) :
    unitaryHaar (Fin d × Fin d)
      {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
        (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ exactPVMBad d} = 0 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨R, -, hR⟩ := exists_exactPVMBad_eq_iUnion_orbits (d := d)
  have hset : {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
      (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ exactPVMBad d} =
      ⋃ s : Fin 8 → ℕ, ⋃ M ∈ R s, {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ |
        (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ pvmBasisOrbit (Fin d) (Fin d) M} := by
    ext V
    simp only [Set.mem_ofPred_eq, hR, Set.mem_iUnion]
  rw [hset]
  refine measure_iUnion_null fun s => ?_
  refine (measure_biUnion_null_iff (R s).countable_toSet).mpr fun M _ => ?_
  exact unitaryHaar_pvmBasisOrbit_eq_zero hd M

end Bad

end NLQCLean
