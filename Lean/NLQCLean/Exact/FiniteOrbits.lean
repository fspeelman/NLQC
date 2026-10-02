import NLQCLean.Exact.LocalOrbitSaturation
import NLQCLean.Exact.OrbitInvariantAlgebraicity
import NLQCLean.Semialgebraic.ScalarNullFinite
import NLQCLean.Semialgebraic.ProjectionTheorem

/-!
# Finitely many local orbits per architecture

For each fixed dimension vector, every real polynomial local-orbit invariant
takes finitely many values on the exact targets: its value set is
semialgebraic (proved projection) and Lebesgue-null (scalar Sard at exact
witnesses), hence finite. A finite separating family of invariants then shows

* the exact targets of one architecture form a finite union of full
  local-unitary orbits;
* two exact strategies in the same connected component of the strategy set
  implement locally equivalent unitaries;
* along every continuous path of exact strategies the implemented unitary
  stays in one local-unitary orbit.

No component-count, path or stratification premise is used.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory ExactWitnessCoordinates
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section RealInvariants

variable {d : ℕ}

/-- `matrixPolyEval` agrees with the existing raw target coordinates. -/
theorem matrixRealCoords_eq_rationalMatrixCoordinates
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    matrixRealCoords (Fin d × Fin d) (Fin d × Fin d) U = rationalMatrixCoordinates U := rfl

/-- A real polynomial in matrix entries is smooth on matrices. -/
theorem contDiff_matrixPolyEval {m n : Type*} [Fintype m] [Fintype n]
    (p : MvPolynomial ((m × n) × Fin 2) ℝ) : ContDiff ℝ ∞ (matrixPolyEval p) := by
  unfold matrixPolyEval
  refine contDiff_mvPolynomial_eval_comp (fun v => ?_) p
  have hentry : ContDiff ℝ ∞ (fun U : Matrix m n ℂ => U v.1.1 v.1.2) :=
    ContDiff.matrixEntry contDiff_id v.1.1 v.1.2
  by_cases hv : v.2 = 0
  · simpa only [matrixRealCoords_apply, hv, ite_true] using ContDiff.complexRe hentry
  · simpa only [matrixRealCoords_apply, hv, ite_false] using ContDiff.complexIm hentry

theorem continuous_matrixPolyEval {m n : Type*} (p : MvPolynomial ((m × n) × Fin 2) ℝ) :
    Continuous (matrixPolyEval (m := m) (n := n) p) :=
  (MvPolynomial.continuous_eval p).comp continuous_matrixRealCoords

/-- A real target polynomial renamed into the seven-block coordinates. -/
def targetRealPolynomial (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℝ) :
    MvPolynomial (Fin (coordinateCount d s)) ℝ :=
  MvPolynomial.rename (targetCoordinates d s) p

theorem targetRealPolynomial_eval (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℝ) (z : Fin (coordinateCount d s) → ℝ) :
    MvPolynomial.eval z (targetRealPolynomial d s p) =
      matrixPolyEval p ((coordinatesEquiv d s).symm z).1 := by
  rw [targetRealPolynomial, MvPolynomial.eval_rename, matrixPolyEval,
    matrixRealCoords_eq_rationalMatrixCoordinates, rationalMatrixCoordinates_targetCoordinates]

/-- The values of a real polynomial on the exact targets of one architecture. -/
theorem image_exactTargets_eq (d : ℕ) (s : ForwardShape)
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) :
    f '' exactTargets d s = invariantScalarPhi f '' {x : ShapeBlocks d s | IsExactWitness x} := by
  rw [exactTargets, Set.image_image]
  exact invariant_image_targetExactWitnessSet d s f

/-- The value set is semialgebraic. -/
theorem semialgebraic_exactTargets_values (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℝ) :
    Semialgebraic {y : RealEuclidean 1 | y 0 ∈ matrixPolyEval p '' exactTargets d s} := by
  have h := ((rationalSemialgebraic_exactWitnessCoordinateSet d s).semialgebraic).polynomial_image
    semialgebraicProjectionTheorem (fun _ : Fin 1 => targetRealPolynomial d s p)
  convert h using 1
  ext y
  constructor
  · rintro ⟨U, ⟨z, hz, rfl⟩, hzy⟩
    refine ⟨WithLp.toLp 2 (coordinatesEquiv d s z), ?_, ?_⟩
    · change (coordinatesEquiv d s).symm (coordinatesEquiv d s z) ∈ targetExactWitnessSet d s
      simpa only [LinearEquiv.symm_apply_apply] using hz
    · ext i
      change MvPolynomial.eval (fun j => coordinatesEquiv d s z j)
        (targetRealPolynomial d s p) = y i
      rw [targetRealPolynomial_eval, show i = (0 : Fin 1) from Subsingleton.elim _ _]
      simpa only [LinearEquiv.symm_apply_apply] using hzy
  · rintro ⟨x, hx, rfl⟩
    refine ⟨_, ⟨_, hx, rfl⟩, ?_⟩
    change matrixPolyEval p ((coordinatesEquiv d s).symm (fun j => x j)).1 =
      MvPolynomial.eval (fun j => x j) (targetRealPolynomial d s p)
    rw [targetRealPolynomial_eval]

/-- **Finitely many invariant values per architecture.** -/
theorem finite_exactTargets_values (d : ℕ) (s : ForwardShape)
    (p : MvPolynomial (RationalMatrixEntryIndex d) ℝ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, matrixPolyEval p V = matrixPolyEval p U) :
    (matrixPolyEval p '' exactTargets d s).Finite := by
  refine finite_of_semialgebraic_scalar_null (semialgebraic_exactTargets_values d s p) ?_
  rw [image_exactTargets_eq]
  exact volume_invariantScalarPhi_image_eq_zero (matrixPolyEval p) (contDiff_matrixPolyEval p)
    hinv _ fun _ hx => hx

end RealInvariants

section Orbits

variable {d : ℕ}

/-- A preconnected finite set of reals has at most one point. -/
theorem finite_subsingleton_of_isPreconnected {T : Set ℝ} (hT : T.Finite)
    (hc : IsPreconnected T) : T.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with h | h
  · exact Set.Icc_infinite h (hT.subset (hc.ordConnected.out hx hy))
  · exact Set.Icc_infinite h (hT.subset (hc.ordConnected.out hy hx))

/-- **Finite orbit decomposition.** For every architecture the exactly
implementable unitaries form a finite union of full local-unitary orbits,
each with an exactly implementable representative. -/
theorem exists_finset_exactTargets_eq_iUnion_orbits (d : ℕ) (s : ForwardShape) :
    ∃ R : Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ U ∈ R, U ∈ exactTargets d s) ∧
        exactTargets d s = ⋃ U ∈ R, unitaryDoubleOrbit (Fin d) (Fin d) U := by
  classical
  obtain ⟨S, hinv, hsep⟩ := exists_finite_unitaryDoubleOrbit_separating (ιA := Fin d) (ιB := Fin d)
  let F : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → (S → ℝ) := fun U p => matrixPolyEval p.1 U
  have hfin : (F '' exactTargets d s).Finite := by
    refine (Set.Finite.pi (t := fun p : S => matrixPolyEval p.1 '' exactTargets d s)
      fun p => finite_exactTargets_values d s p.1 fun U _ V hV => hinv p.1 p.2 U V hV).subset ?_
    rintro _ ⟨U, hU, rfl⟩ p -
    exact ⟨U, hU, rfl⟩
  have hrep : ∀ v ∈ F '' exactTargets d s, ∃ U ∈ exactTargets d s, F U = v := fun v hv => hv
  let rep : (S → ℝ) → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun v =>
    if hv : v ∈ F '' exactTargets d s then Classical.choose (hrep v hv) else 0
  have hrep_mem : ∀ v ∈ F '' exactTargets d s, rep v ∈ exactTargets d s ∧ F (rep v) = v := by
    intro v hv
    simp only [rep, dite_eq_left hv]
    exact Classical.choose_spec (hrep v hv)
  refine ⟨hfin.toFinset.image rep, ?_, ?_⟩
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    exact (hrep_mem v (hfin.mem_toFinset.mp hv)).1
  · apply le_antisymm
    · intro U hU
      have hv : F U ∈ F '' exactTargets d s := ⟨U, hU, rfl⟩
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      refine ⟨rep (F U), ⟨F U, hfin.mem_toFinset.mpr hv, rfl⟩, ?_⟩
      apply hsep
      intro p hp
      exact congrFun (hrep_mem (F U) hv).2 ⟨p, hp⟩
    · simp only [Set.iUnion_subset_iff, Finset.mem_image]
      rintro _ ⟨v, hv, rfl⟩
      exact unitaryDoubleOrbit_subset_exactTargets s (hrep_mem v (hfin.mem_toFinset.mp hv)).1

/-- **Same component, same orbit.** Two exact strategies of one architecture
in the same connected component of the strategy set implement locally
equivalent unitaries. -/
theorem mem_unitaryDoubleOrbit_of_mem_connectedComponentIn (s : ForwardShape)
    {z y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    (hy : y ∈ connectedComponentIn (targetExactWitnessSet d s) z) :
    y.1 ∈ unitaryDoubleOrbit (Fin d) (Fin d) z.1 := by
  classical
  obtain ⟨S, hinv, hsep⟩ := exists_finite_unitaryDoubleOrbit_separating (ιA := Fin d) (ιB := Fin d)
  have hz : z ∈ targetExactWitnessSet d s := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hy
    exact hy
  set C := connectedComponentIn (targetExactWitnessSet d s) z
  have hCsub : C ⊆ targetExactWitnessSet d s := connectedComponentIn_subset _ _
  apply hsep
  intro p hp
  let h : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s → ℝ :=
    fun w => matrixPolyEval p w.1
  have hcont : Continuous h := (continuous_matrixPolyEval p).comp continuous_fst
  have hfin : (h '' C).Finite := by
    refine (finite_exactTargets_values d s p fun U _ V hV => hinv p hp U V hV).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.1, ⟨w, hCsub hw, rfl⟩, rfl⟩
  have hconn : IsPreconnected (h '' C) :=
    (isPreconnected_connectedComponentIn).image h hcont.continuousOn
  exact finite_subsingleton_of_isPreconnected hfin hconn
    ⟨z, mem_connectedComponentIn hz, rfl⟩ ⟨y, hy, rfl⟩

/-- **Paths stay in one orbit.** Along any continuous path of exact
strategies of one architecture on a preconnected parameter set (for example
an open interval), the implemented unitary stays in the local-unitary orbit
of its value at any fixed parameter. -/
theorem mem_unitaryDoubleOrbit_of_continuousOn_path (s : ForwardShape)
    {J : Set ℝ} (hJ : IsPreconnected J)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    (hγ : ContinuousOn γ J) (hmem : ∀ t ∈ J, γ t ∈ targetExactWitnessSet d s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    (γ t).1 ∈ unitaryDoubleOrbit (Fin d) (Fin d) (γ t₀).1 := by
  apply mem_unitaryDoubleOrbit_of_mem_connectedComponentIn s
  have hsub : γ '' J ⊆ connectedComponentIn (targetExactWitnessSet d s) (γ t₀) :=
    (hJ.image γ hγ).subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩
      (by rintro _ ⟨u, hu, rfl⟩; exact hmem u hu)
  exact hsub ⟨t, ht, rfl⟩

end Orbits

end NLQCLean
