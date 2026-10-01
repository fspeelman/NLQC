import NLQCLean.Exact.ExactPurityAlgebraicity
import NLQCLean.Exact.InvariantCriticalValues
import NLQCLean.Exact.RationalInvariantPolynomial

/-!
# Orbit invariants take algebraic values

For each actual finite exact architecture, the rational polynomial invariant
image is rational semialgebraic and null. Its points are therefore algebraic.
Orbit invariance is required only at unitary targets. No finite-orbit structure
or additional geometry premise is used.
-/

noncomputable section
namespace NLQCLean
open Matrix MeasureTheory ExactWitnessCoordinates ExactWitnessPolynomial
open scoped Matrix.Norms.Frobenius

/-- Target-witness values agree with the cubic scalar critical image. -/
theorem invariant_image_targetExactWitnessSet (d : ℕ) (s : ForwardShape)
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) :
    (fun z => f z.1) '' targetExactWitnessSet d s =
      invariantScalarPhi f '' {x : ShapeBlocks d s | IsExactWitness x} := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hx, hH⟩ := (mem_targetExactWitnessSet_iff d s z).mp hz
    refine ⟨z.2, hx, ?_⟩
    rw [invariantScalarPhi, cubicBlocks_of_isExactWitness hx, hH]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(forwardOverlapOn x, x), ?_, ?_⟩
    · exact (mem_targetExactWitnessSet_iff d s _).mpr ⟨hx, rfl⟩
    · rw [invariantScalarPhi, cubicBlocks_of_isExactWitness hx]

/-- The one-coordinate target-invariant polynomial map. -/
def exactWitnessInvariantMap (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ) :
    RealEuclidean (coordinateCount d s) → RealEuclidean 1 :=
  PolynomialSignDNF.polynomialMap
    (fun _ => MvPolynomial.map (algebraMap ℚ ℝ) (targetInvariantPolynomial d s p))

theorem exactWitnessInvariantMap_apply (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (x : RealEuclidean (coordinateCount d s)) (i : Fin 1) :
    exactWitnessInvariantMap d s p x i =
      rationalMatrixInvariant p ((coordinatesEquiv d s).symm (fun j => x j)).1 := by
  change MvPolynomial.eval (fun j => x j)
    (MvPolynomial.map (algebraMap ℚ ℝ) (targetInvariantPolynomial d s p)) = _
  rw [MvPolynomial.eval_map]
  exact targetInvariantPolynomial_evaluate d s p (fun j => x j)

/-- The rational polynomial image agrees with the original critical image. -/
theorem exactWitnessInvariantMap_image (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ) :
    exactWitnessInvariantMap d s p '' exactWitnessCoordinateSet d s =
      {y : RealEuclidean 1 | y 0 ∈
        invariantScalarPhi (rationalMatrixInvariant p) '' {x : ShapeBlocks d s | IsExactWitness x}} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_ofPred_eq, exactWitnessInvariantMap_apply]
    rw [← invariant_image_targetExactWitnessSet d s (rationalMatrixInvariant p)]
    exact ⟨(coordinatesEquiv d s).symm (fun j => x j), hx, rfl⟩
  · intro hy
    rw [Set.mem_ofPred_eq, ← invariant_image_targetExactWitnessSet d s (rationalMatrixInvariant p)] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨WithLp.toLp 2 (coordinatesEquiv d s z), ?_, ?_⟩
    · change (coordinatesEquiv d s).symm (coordinatesEquiv d s z) ∈ targetExactWitnessSet d s
      simpa only [LinearEquiv.symm_apply_apply] using hz
    · ext i
      rw [exactWitnessInvariantMap_apply]
      change rationalMatrixInvariant p
        ((coordinatesEquiv d s).symm (coordinatesEquiv d s z)).1 = y i
      simpa only [LinearEquiv.symm_apply_apply,
        show i = (0 : Fin 1) from Subsingleton.elim _ _] using hzy

/-- Rationality is proved for each actual finite-shape image. -/
theorem rationalSemialgebraic_shapeInvariantValues (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ) :
    RationalSemialgebraic {y : RealEuclidean 1 | y 0 ∈
      invariantScalarPhi (rationalMatrixInvariant p) '' {x : ShapeBlocks d s | IsExactWitness x}} := by
  rw [← exactWitnessInvariantMap_image]
  exact (rationalSemialgebraic_exactWitnessCoordinateSet d s).polynomial_image_rat
    (fun _ : Fin 1 => targetInvariantPolynomial d s p)

/-- Every exact invariant value of a fixed architecture is algebraic over ℚ. -/
theorem isAlgebraic_of_mem_shapeInvariantValues (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U,
        rationalMatrixInvariant p V = rationalMatrixInvariant p U)
    {t : ℝ}
    (ht : t ∈ invariantScalarPhi (rationalMatrixInvariant p) '' {x : ShapeBlocks d s | IsExactWitness x}) :
    IsAlgebraic ℚ t := by
  have h := rationalSemialgebraic_shapeInvariantValues d s p
  apply h.isAlgebraic_of_scalar_measure_eq_zero
  · change volume (invariantScalarPhi (rationalMatrixInvariant p) '' {x : ShapeBlocks d s | IsExactWitness x}) = 0
    exact volume_invariantScalarPhi_image_eq_zero (rationalMatrixInvariant p)
      (contDiff_rationalMatrixInvariant p) hinv
      {x : ShapeBlocks d s | IsExactWitness x} (fun _ hx => hx)
  · exact ht

/-- All finite architectures are covered without a rationality claim for
 their countable union. -/
theorem isAlgebraic_of_mem_exactInvariantValues (d : ℕ)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U,
        rationalMatrixInvariant p V = rationalMatrixInvariant p U) {t : ℝ}
    (ht : t ∈ exactInvariantValues d (rationalMatrixInvariant p)) : IsAlgebraic ℚ t := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
  exact isAlgebraic_of_mem_shapeInvariantValues d s p hinv hs


/-- Every member of a local unitary orbit of a unitary matrix is unitary. -/
theorem mem_unitaryGroup_of_mem_unitaryDoubleOrbit {d : ℕ}
    {U V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hV : V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U) :
    V ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ := by
  rcases hV with ⟨L, hL, R, hR, rfl⟩
  exact (Matrix.unitaryGroup (Fin d × Fin d) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin d × Fin d) ℂ).mul_mem
      (localUnitaries_subset_unitary hL) hU)
    (localUnitaries_subset_unitary hR)

/-- Only the polynomial presentation on unitary matrices is needed. The
ambient scalar function can be arbitrary away from unitary matrices. -/
theorem rationalMatrixInvariant_invariant_of_eq_on_unitaries {d : ℕ}
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hpoly : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ, f U = rationalMatrixInvariant p U)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U) :
    ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U,
        rationalMatrixInvariant p V = rationalMatrixInvariant p U := by
  intro U hU V hV
  rw [← hpoly V (mem_unitaryGroup_of_mem_unitaryDoubleOrbit hU hV), ← hpoly U hU]
  exact hinv U hU V hV

section PhysicalProtocols

variable {d : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- A rational polynomial constant on unitary local orbits takes an algebraic
value at every target exactly implemented by an arbitrary finite pure protocol. -/
theorem PureProtocol.isAlgebraic_rationalInvariant_of_performsUnitary
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U,
        rationalMatrixInvariant p V = rationalMatrixInvariant p U)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hP : P.PerformsUnitary U) :
    IsAlgebraic ℚ (rationalMatrixInvariant p U) := by
  have hscore : scoreU U P.operationalChannel = 1 := by
    change P.operationalChannel = adConj U at hP
    rw [hP, scoreU_adConj_self hU.isIsometry]
  exact isAlgebraic_of_mem_exactInvariantValues d p hinv
    (P.invariant_mem_exactInvariantValues_of_score_eq_one (rationalMatrixInvariant p) hU hscore)

/-- The same algebraicity holds for arbitrary finite common-map mixed
resources. The score-one pure component retains all original physical maps. -/
theorem MixedResource.isAlgebraic_rationalInvariant_of_mixedChannel_eq
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U,
        rationalMatrixInvariant p V = rationalMatrixInvariant p U)
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix (Fin d × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hm : m.mixedChannel VA VB DA DB = adConj U) :
    IsAlgebraic ℚ (rationalMatrixInvariant p U) := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB U
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hge : 1 ≤ scoreU U P.operationalChannel := by
    rw [hm, scoreU_adConj_self hU.isIsometry] at hk
    exact hk
  have hF := P.isIsometry_globalIsometry.submatrix_equiv
    (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
  have hle : scoreU U P.operationalChannel ≤ 1 := scoreU_le_one hU.isIsometry hF
  exact isAlgebraic_of_mem_exactInvariantValues d p hinv
    (P.invariant_mem_exactInvariantValues_of_score_eq_one (rationalMatrixInvariant p)
      hU (le_antisymm hle hge))

/-- Source `lem:algebraic-values` for pure exact implementation. Rational
polynomiality and orbit invariance are required only on the unitary group. -/
theorem PureProtocol.isAlgebraic_orbitInvariant_of_performsUnitary
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hpoly : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ, f U = rationalMatrixInvariant p U)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hP : P.PerformsUnitary U) : IsAlgebraic ℚ (f U) := by
  rw [hpoly U (Matrix.mem_unitaryGroup_iff.mpr hU.self_mul_conjTranspose)]
  exact P.isAlgebraic_rationalInvariant_of_performsUnitary p
    (rationalMatrixInvariant_invariant_of_eq_on_unitaries f p hpoly hinv) hU hP

/-- Source `lem:algebraic-values` for actual finite common-map mixed channels.
No regularity of the ambient extension or support bound is assumed. -/
theorem MixedResource.isAlgebraic_orbitInvariant_of_mixedChannel_eq
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℚ)
    (hpoly : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ, f U = rationalMatrixInvariant p U)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
    {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix (Fin d × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hm : m.mixedChannel VA VB DA DB = adConj U) :
    IsAlgebraic ℚ (f U) := by
  rw [hpoly U (Matrix.mem_unitaryGroup_iff.mpr hU.self_mul_conjTranspose)]
  exact m.isAlgebraic_rationalInvariant_of_mixedChannel_eq p
    (rationalMatrixInvariant_invariant_of_eq_on_unitaries f p hpoly hinv) hVA hVB hDA hDB hU hm

end PhysicalProtocols

end NLQCLean
