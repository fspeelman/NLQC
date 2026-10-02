import NLQCLean.Exact.PolynomialWitnessMaps
import NLQCLean.Exact.FiniteOrbits

/-!
# Finitely many measurement orbits per architecture

For a fixed dimension vector, the exact two-sided rank-one PVM targets are
saturated by the measurement action `M ↦ (L_A ⊗ L_B) M Δ`: local unitaries
are absorbed into the encoders and diagonal phases into the outcome flags.
Every real polynomial measurement-orbit invariant takes finitely many values
on them (polynomial witness locus, proved projection and scalar Sard). A
finite separating family gives a finite union of measurement orbits
(`thm:measHaarNull` (i)), constancy of the orbit on connected components
(`prop:component-pvm`) and along continuous paths.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory
open scoped Kronecker

section Absorption

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

/-- Input local operators absorbed into the encoders multiply the global
isometry from the right. -/
theorem globalIsometry_input_local (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (SA : Matrix ιA ιA ℂ) (SB : Matrix ιB ιB ℂ) :
    globalIsometry η (VA * (SA ⊗ₖ (1 : Matrix ρA ρA ℂ))) (VB * (SB ⊗ₖ (1 : Matrix ρB ρB ℂ)))
        DA DB = globalIsometry η VA VB DA DB * (SA ⊗ₖ SB) := by
  rw [globalIsometry_eq, globalIsometry_eq, Matrix.mul_kronecker_mul,
    Matrix.mul_assoc (VA ⊗ₖ VB), localKronecker_mul_insertResource]
  simp only [Matrix.mul_assoc]

/-- Diagonal phases on the outcome labels are absorbed into the flags. -/
theorem flagIsometry_mul_diagonal {δ : Type*} [Fintype δ] [DecidableEq δ]
    (ω : δ → εA × εB → ℂ) (φ : δ → ℂ) :
    flagIsometry ω * Matrix.diagonal φ = flagIsometry (fun i => φ i • ω i) := by
  ext p i
  rw [Matrix.mul_diagonal, flagIsometry_apply, flagIsometry_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Absorption

section Saturation

variable {d : ℕ}

/-- The fixed-architecture measurement strategy set, with the basis matrix
as an explicit block. -/
def pvmTargetWitnessSet (d : ℕ) (s : Fin 8 → ℕ) :
    Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s) :=
  {z | IsExactPVMWitness z.2 ∧ (pvmOverlapOn z.2)ᴴ = z.1}

/-- The exactly implementable basis matrices of one architecture. -/
def pvmExactTargets (d : ℕ) (s : Fin 8 → ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  Prod.fst '' pvmTargetWitnessSet d s

theorem isUnitVector_smul_of_norm_eq_one {ε : Type*} [Fintype ε] {v : ε → ℂ}
    (hv : IsUnitVector v) {c : ℂ} (hc : ‖c‖ = 1) : IsUnitVector (c • v) := by
  unfold IsUnitVector at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, hv, mul_one, Complex.normSq_eq_norm_sq, hc, one_pow]

/-- **Saturation of measurement targets.** Each fixed-architecture target
set contains the full measurement orbit of each member. -/
theorem pvmBasisOrbit_subset_pvmExactTargets (s : Fin 8 → ℕ)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : M ∈ pvmExactTargets d s) :
    pvmBasisOrbit (Fin d) (Fin d) M ⊆ pvmExactTargets d s := by
  obtain ⟨z, ⟨hx, hzM⟩, rfl⟩ := hM
  rintro N ⟨_, ⟨LA, hLA, LB, hLB, rfl⟩, _, ⟨φ, hφ, rfl⟩, rfl⟩
  set x := z.2
  have hT : pvmOverlapOn x = z.1ᴴ := by
    rw [← hzM, Matrix.conjTranspose_conjTranspose]
  set M := z.1
  let ω' : Fin d × Fin d → Fin (s 6) × Fin (s 7) → ℂ := fun i => φ i • x.2.1 i
  let x' : PVMShapeBlocks d s := (x.1, ω', x.2.2.1 * (LAᴴ ⊗ₖ 1), x.2.2.2.1 * (LBᴴ ⊗ₖ 1),
    x.2.2.2.2.1, x.2.2.2.2.2)
  have hLAc : LAᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := conjTranspose_mem_unitaryGroup hLA
  have hLBc : LBᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := conjTranspose_mem_unitaryGroup hLB
  have hω' : ∀ i, IsUnitVector (ω' i) := fun i =>
    isUnitVector_smul_of_norm_eq_one (hx.flag_unit i) (hφ i)
  have hΔ : Matrix.diagonal φ * (Matrix.diagonal φ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (phaseUnitaries_subset_unitary ⟨φ, hφ, rfl⟩)
  have hflag : flagIsometry ω' = flagIsometry x.2.1 * Matrix.diagonal φ :=
    (flagIsometry_mul_diagonal x.2.1 φ).symm
  set N := (LA ⊗ₖ LB) * M * Matrix.diagonal φ
  have hglobal : globalIsometry x'.1 x'.2.2.1 x'.2.2.2.1 x'.2.2.2.2.1 x'.2.2.2.2.2 =
      flagIsometry ω' * Nᴴ := by
    change globalIsometry x.1 (x.2.2.1 * (LAᴴ ⊗ₖ 1)) (x.2.2.2.1 * (LBᴴ ⊗ₖ 1))
      x.2.2.2.2.1 x.2.2.2.2.2 = _
    rw [globalIsometry_input_local, hx.exact, hT, hflag]
    simp only [N, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal φ) (Matrix.diagonal φ)ᴴ, hΔ, Matrix.one_mul]
  have hiso := isIsometry_flagIsometry ω' hω'
  have hT' : pvmOverlapOn x' = Nᴴ := by
    change (flagIsometry ω')ᴴ * globalIsometry x'.1 x'.2.2.1 x'.2.2.2.1 x'.2.2.2.2.1
      x'.2.2.2.2.2 = Nᴴ
    rw [hglobal, ← Matrix.mul_assoc, hiso.conjTranspose_mul_self, Matrix.one_mul]
  have hMu : M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := hx.overlap_coisometry
    rw [hT, Matrix.conjTranspose_conjTranspose] at h
    exact h
  have hNu : N ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Matrix.kronecker_mem_unitary hLA hLB) hMu)
      (phaseUnitaries_subset_unitary ⟨φ, hφ, rfl⟩)
  refine ⟨(N, x'), ⟨⟨hx.resource_unit, hω', hx.encA_isometry.mul (kronecker_one_isIsometry hLAc),
    hx.encB_isometry.mul (kronecker_one_isIsometry hLBc), hx.decA_isometry, hx.decB_isometry,
    ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [hT', Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hNu
  · rw [hglobal, hT']
  · rw [hT', Matrix.conjTranspose_conjTranspose]

end Saturation

section Values

variable {d : ℕ}

theorem image_pvmExactTargets_eq (s : Fin 8 → ℕ)
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) :
    f '' pvmExactTargets d s =
      (fun x : PVMShapeBlocks d s => f (pvmOverlapOn x)ᴴ) '' {x | IsExactPVMWitness x} := by
  ext t
  constructor
  · rintro ⟨_, ⟨z, ⟨hx, hM⟩, rfl⟩, rfl⟩
    exact ⟨z.2, hx, by simp only [hM]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨((pvmOverlapOn x)ᴴ, x), ⟨hx, rfl⟩, rfl⟩, rfl⟩

/-- **Finitely many invariant values per measurement architecture.** -/
theorem finite_pvmExactTargets_values (s : Fin 8 → ℕ)
    (p : MvPolynomial (((Fin d × Fin d) × (Fin d × Fin d)) × Fin 2) ℝ)
    (hinv : ∀ M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ N ∈ pvmBasisOrbit (Fin d) (Fin d) M, matrixPolyEval p N = matrixPolyEval p M) :
    (matrixPolyEval p '' pvmExactTargets d s).Finite := by
  rw [image_pvmExactTargets_eq]
  refine finite_of_semialgebraic_scalar_null ?_ ?_
  · exact isPolyZeroSet_isExactPVMWitness.semialgebraic_image
      (isPolyMatrix_pvmOverlapOn.conjTranspose.matrixPolyEval p)
  · have h := volume_pvmInvariantScalarPhi_image_eq_zero (matrixPolyEval p)
      (contDiff_matrixPolyEval p) hinv {x : PVMShapeBlocks d s | IsExactPVMWitness x}
      (fun _ hx => hx)
    convert h using 2
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [pvmInvariantScalarPhi, cubicPVMBlocks_of_isExactPVMWitness hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [pvmInvariantScalarPhi, cubicPVMBlocks_of_isExactPVMWitness hx]⟩

end Values

section Orbits

variable {d : ℕ}

/-- **`thm:measHaarNull` (i).** For every architecture the exactly
implementable basis matrices form a finite union of full measurement orbits,
each with an implementable representative. -/
theorem exists_finset_pvmExactTargets_eq_iUnion_orbits (d : ℕ) (s : Fin 8 → ℕ) :
    ∃ R : Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ M ∈ R, M ∈ pvmExactTargets d s) ∧
        pvmExactTargets d s = ⋃ M ∈ R, pvmBasisOrbit (Fin d) (Fin d) M := by
  classical
  obtain ⟨S, hinv, hsep⟩ := exists_finite_pvmBasisOrbit_separating (ιA := Fin d) (ιB := Fin d)
  let F : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → (S → ℝ) := fun M p => matrixPolyEval p.1 M
  have hfin : (F '' pvmExactTargets d s).Finite := by
    refine (Set.Finite.pi (t := fun p : S => matrixPolyEval p.1 '' pvmExactTargets d s)
      fun p => finite_pvmExactTargets_values s p.1
        fun M _ N hN => hinv p.1 p.2 M N hN).subset ?_
    rintro _ ⟨M, hM, rfl⟩ p -
    exact ⟨M, hM, rfl⟩
  have hrep : ∀ v ∈ F '' pvmExactTargets d s, ∃ M ∈ pvmExactTargets d s, F M = v :=
    fun v hv => hv
  let rep : (S → ℝ) → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun v =>
    if hv : v ∈ F '' pvmExactTargets d s then Classical.choose (hrep v hv) else 0
  have hrep_mem : ∀ v ∈ F '' pvmExactTargets d s,
      rep v ∈ pvmExactTargets d s ∧ F (rep v) = v := by
    intro v hv
    simp only [rep, dite_eq_left hv]
    exact Classical.choose_spec (hrep v hv)
  refine ⟨hfin.toFinset.image rep, ?_, ?_⟩
  · intro M hM
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hM
    exact (hrep_mem v (hfin.mem_toFinset.mp hv)).1
  · apply le_antisymm
    · intro M hM
      have hv : F M ∈ F '' pvmExactTargets d s := ⟨M, hM, rfl⟩
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      refine ⟨rep (F M), ⟨F M, hfin.mem_toFinset.mpr hv, rfl⟩, ?_⟩
      apply hsep
      intro p hp
      exact congrFun (hrep_mem (F M) hv).2 ⟨p, hp⟩
    · simp only [Set.iUnion_subset_iff, Finset.mem_image]
      rintro _ ⟨v, hv, rfl⟩
      exact pvmBasisOrbit_subset_pvmExactTargets s (hrep_mem v (hfin.mem_toFinset.mp hv)).1

/-- **`prop:component-pvm`.** Measurement strategies of one architecture in the
same connected component have basis matrices in the same measurement orbit. -/
theorem mem_pvmBasisOrbit_of_mem_connectedComponentIn (s : Fin 8 → ℕ)
    {z y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hy : y ∈ connectedComponentIn (pvmTargetWitnessSet d s) z) :
    y.1 ∈ pvmBasisOrbit (Fin d) (Fin d) z.1 := by
  classical
  obtain ⟨S, hinv, hsep⟩ := exists_finite_pvmBasisOrbit_separating (ιA := Fin d) (ιB := Fin d)
  have hz : z ∈ pvmTargetWitnessSet d s := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hy
    exact hy
  set C := connectedComponentIn (pvmTargetWitnessSet d s) z
  have hCsub : C ⊆ pvmTargetWitnessSet d s := connectedComponentIn_subset _ _
  apply hsep
  intro p hp
  let h : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s → ℝ :=
    fun w => matrixPolyEval p w.1
  have hcont : Continuous h := (continuous_matrixPolyEval p).comp continuous_fst
  have hfin : (h '' C).Finite := by
    refine (finite_pvmExactTargets_values s p fun M _ N hN => hinv p hp M N hN).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.1, ⟨w, hCsub hw, rfl⟩, rfl⟩
  have hconn : IsPreconnected (h '' C) :=
    (isPreconnected_connectedComponentIn).image h hcont.continuousOn
  exact finite_subsingleton_of_isPreconnected hfin hconn
    ⟨z, mem_connectedComponentIn hz, rfl⟩ ⟨y, hy, rfl⟩

/-- Along any continuous path of measurement strategies on a preconnected
parameter set, the basis matrix stays in one measurement orbit. -/
theorem mem_pvmBasisOrbit_of_continuousOn_path (s : Fin 8 → ℕ)
    {J : Set ℝ} (hJ : IsPreconnected J)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hγ : ContinuousOn γ J) (hmem : ∀ t ∈ J, γ t ∈ pvmTargetWitnessSet d s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    (γ t).1 ∈ pvmBasisOrbit (Fin d) (Fin d) (γ t₀).1 := by
  apply mem_pvmBasisOrbit_of_mem_connectedComponentIn s
  have hsub : γ '' J ⊆ connectedComponentIn (pvmTargetWitnessSet d s) (γ t₀) :=
    (hJ.image γ hγ).subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩
      (by rintro _ ⟨u, hu, rfl⟩; exact hmem u hu)
  exact hsub ⟨t, ht, rfl⟩

end Orbits

end NLQCLean
