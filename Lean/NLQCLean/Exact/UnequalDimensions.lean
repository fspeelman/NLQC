import NLQCLean.Exact.GeneralExactWitness
import NLQCLean.Exact.FiniteOrbits
import NLQCLean.Geometry.LocalOrbitHaarNull

/-!
# Exact impossibility for arbitrary local dimensions (`rem:qudits`)

For inputs `ℂ^{d_A} ⊗ ℂ^{d_B}` with `d_A, d_B ≥ 2`, the source's argument runs
unchanged: every architecture's exact targets form a finite union of full
local-unitary orbits, so the exactly implementable unitaries are a countable
union of Haar-null orbits. Hence Haar-almost every unitary on
`ℂ^{d_A} ⊗ ℂ^{d_B}` has no exact one-round protocol with finite registers.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

section Polynomial

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

local notation "GB" => GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyVec_gen_resource : IsPolyVec (fun x : GB => x.1) :=
  IsPolyVec.of_linear (LinearMap.fst ℝ (ρA × ρB → ℂ) _ : GB →ₗ[ℝ] (ρA × ρB → ℂ))

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyVec_gen_witness : IsPolyVec (fun x : GB => x.2.1) :=
  IsPolyVec.of_linear ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ (ρA × ρB → ℂ) _) :
    GB →ₗ[ℝ] (εA × εB → ℂ))

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_encA : IsPolyMatrix (fun x : GB => x.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    (LinearMap.snd ℝ _ _)) : GB →ₗ[ℝ] Matrix (κA × μA) (ιA × ρA) ℂ)

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_encB : IsPolyMatrix (fun x : GB => x.2.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))) : GB →ₗ[ℝ] Matrix (κB × μB) (ιB × ρB) ℂ)

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_decA : IsPolyMatrix (fun x : GB => x.2.2.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))) :
      GB →ₗ[ℝ] Matrix (ιA × εA) (κA × μB) ℂ)

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_decB : IsPolyMatrix (fun x : GB => x.2.2.2.2.2) :=
  IsPolyMatrix.linear ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))) :
      GB →ₗ[ℝ] Matrix (ιB × εB) (κB × μA) ℂ)

omit [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA]
  [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_regroupedDecoder :
    IsPolyMatrix (fun x : GB =>
      (decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix (outputRegroup ιA ιB εA εB) id) :=
  (isPolyMatrix_gen_decA.kronecker isPolyMatrix_gen_decB).submatrix _ _

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_encodedState :
    IsPolyMatrix (fun x : GB => encodedState (ιA := ιA) (ιB := ιB) x.1 x.2.2.1 x.2.2.2.1) :=
  (IsPolyMatrix.const _).mul ((isPolyMatrix_gen_encA.kronecker isPolyMatrix_gen_encB).mul
    (IsPolyMatrix.insertResource isPolyVec_gen_resource))

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_gen_forwardOverlapOn :
    IsPolyMatrix (fun x : GB => forwardOverlapOn x) := by
  have h := (IsPolyMatrix.insertVector (ιA × ιB) (isPolyVec_gen_witness (ιA := ιA) (ιB := ιB)
    (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA)
    (εB := εB))).conjTranspose.mul (isPolyMatrix_gen_regroupedDecoder.mul
      isPolyMatrix_gen_encodedState)
  have hfun : (fun x : GB => forwardOverlapOn x) = fun x : GB =>
      (insertVector (ιA × ιB) x.2.1)ᴴ * ((decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix
        (outputRegroup ιA ιB εA εB) id * encodedState x.1 x.2.2.1 x.2.2.2.1) := by
    funext x
    change forwardOverlap x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 = _
    rw [forwardOverlap, globalIsometryRegrouped_eq]
  rw [hfun]
  exact h

omit [DecidableEq εA] [DecidableEq εB] in
/-- The exact-witness locus is a polynomial zero set. -/
theorem isPolyZeroSet_isExactWitnessGen : IsPolyZeroSet {x : GB | IsExactWitnessGen x} := by
  have hO := isPolyMatrix_gen_forwardOverlapOn (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have hW := isPolyMatrix_gen_regroupedDecoder (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have hY := isPolyMatrix_gen_encodedState (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have hg := isPolyVec_gen_witness (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have h9 := (hW.mul hY).isPolyZeroSet_eq ((IsPolyMatrix.insertVector (ιA × ιB) hg).mul hO)
  have h8 := (hO.mul hO.conjTranspose).isPolyZeroSet_eq
    (IsPolyMatrix.const (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ))
  have h7 := hW.isPolyZeroSet_isIsometry
  have h6 := (isPolyMatrix_gen_decB (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h5 := (isPolyMatrix_gen_decA (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h4 := (isPolyMatrix_gen_encB (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h3 := (isPolyMatrix_gen_encA (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
    (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h2 := isPolyZeroSet_isUnitVector hg
  have h1 := isPolyZeroSet_isUnitVector (isPolyVec_gen_resource (ιA := ιA) (ιB := ιB)
    (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB))
  have h := h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter
    (h8.inter h9)))))))
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨hx.resource_unit, hx.witness_unit, hx.encA_isometry, hx.encB_isometry,
      hx.decA_isometry, hx.decB_isometry, hx.decoder_isometry, hx.overlap_coisometry, hx.exact⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Polynomial

section Targets

variable (dA dB : ℕ)

/-- Strategy blocks of one architecture with local dimensions `d_A, d_B`. -/
abbrev GenShapeBlocks (s : ForwardShape) :=
  GenBlocks (Fin dA) (Fin dB) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7))

/-- The exact targets of one architecture. -/
def genExactTargets (s : ForwardShape) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {U | ∃ x : GenShapeBlocks dA dB s, IsExactWitnessGen x ∧ forwardOverlapOn x = U}

variable {dA dB}

theorem image_genExactTargets_eq (s : ForwardShape)
    (f : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ → ℝ) :
    f '' genExactTargets dA dB s =
      invariantScalarPhiGen f '' {x : GenShapeBlocks dA dB s | IsExactWitnessGen x} := by
  ext t
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [invariantScalarPhiGen, cubicBlocksGen_of_isExactWitnessGen hx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by rw [invariantScalarPhiGen, cubicBlocksGen_of_isExactWitnessGen hx]⟩

/-- Finitely many invariant values per architecture. -/
theorem finite_genExactTargets_values (s : ForwardShape)
    (p : MvPolynomial (((Fin dA × Fin dB) × (Fin dA × Fin dB)) × Fin 2) ℝ)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin dA × Fin dB) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin dA) (Fin dB) U, matrixPolyEval p V = matrixPolyEval p U) :
    (matrixPolyEval p '' genExactTargets dA dB s).Finite := by
  refine finite_of_semialgebraic_scalar_null ?_ ?_
  · have h := (isPolyZeroSet_isExactWitnessGen (ιA := Fin dA) (ιB := Fin dB)
      (ρA := Fin (s 0)) (ρB := Fin (s 1)) (κA := Fin (s 2)) (κB := Fin (s 3))
      (μA := Fin (s 4)) (μB := Fin (s 5)) (εA := Fin (s 6)) (εB := Fin (s 7))).semialgebraic_image
      (isPolyMatrix_gen_forwardOverlapOn.matrixPolyEval p)
    have hEq : matrixPolyEval p '' genExactTargets dA dB s =
        (fun x : GenShapeBlocks dA dB s => matrixPolyEval p (forwardOverlapOn x)) ''
          {x | IsExactWitnessGen x} := by
      ext t
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hEq]
    exact h
  · rw [image_genExactTargets_eq]
    exact volume_invariantScalarPhiGen_image_eq_zero (matrixPolyEval p)
      (contDiff_matrixPolyEval p) hinv _ fun _ hx => hx

/-- Fixed-architecture saturation for arbitrary local dimensions. -/
theorem unitaryDoubleOrbit_subset_genExactTargets (s : ForwardShape)
    {U : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hU : U ∈ genExactTargets dA dB s) :
    unitaryDoubleOrbit (Fin dA) (Fin dB) U ⊆ genExactTargets dA dB s := by
  obtain ⟨x, hx, rfl⟩ := hU
  rintro V ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩, S, ⟨SA, hSA, SB, hSB, rfl⟩, rfl⟩
  set U := forwardOverlapOn x
  let x' : GenShapeBlocks dA dB s := (x.1, x.2.1, x.2.2.1 * (SA ⊗ₖ 1), x.2.2.2.1 * (SB ⊗ₖ 1),
    (LA ⊗ₖ 1) * x.2.2.2.2.1, (LB ⊗ₖ 1) * x.2.2.2.2.2)
  have hF : globalIsometryRegrouped x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 =
      insertVector (Fin dA × Fin dB) x.2.1 * U := by
    rw [globalIsometryRegrouped_eq]
    exact hx.exact
  have hF' : globalIsometryRegrouped x'.1 x'.2.2.1 x'.2.2.2.1 x'.2.2.2.2.1 x'.2.2.2.2.2 =
      insertVector (Fin dA × Fin dB) x.2.1 * ((LA ⊗ₖ LB) * U * (SA ⊗ₖ SB)) := by
    change globalIsometryRegrouped x.1 (x.2.2.1 * (SA ⊗ₖ 1)) (x.2.2.2.1 * (SB ⊗ₖ 1))
      ((LA ⊗ₖ 1) * x.2.2.2.2.1) ((LB ⊗ₖ 1) * x.2.2.2.2.2) = _
    rw [globalIsometryRegrouped_local, hF, ← Matrix.mul_assoc, kronecker_one_mul_insertVector]
    simp only [Matrix.mul_assoc]
  have hO : forwardOverlapOn x' = (LA ⊗ₖ LB) * U * (SA ⊗ₖ SB) := by
    change (insertVector (Fin dA × Fin dB) x.2.1)ᴴ * globalIsometryRegrouped x'.1 x'.2.2.1
      x'.2.2.2.1 x'.2.2.2.2.1 x'.2.2.2.2.2 = _
    rw [hF', ← Matrix.mul_assoc, (isIsometry_insertVector _ hx.witness_unit).conjTranspose_mul_self,
      Matrix.one_mul]
  have hDA' := (kronecker_one_isIsometry (ρ := Fin (s 6)) hLA).mul hx.decA_isometry
  have hDB' := (kronecker_one_isIsometry (ρ := Fin (s 7)) hLB).mul hx.decB_isometry
  refine ⟨x', ⟨hx.resource_unit, hx.witness_unit,
    hx.encA_isometry.mul (kronecker_one_isIsometry hSA),
    hx.encB_isometry.mul (kronecker_one_isIsometry hSB), hDA', hDB',
    (isIsometry_decoder hDA' hDB').submatrix_equiv _ (Equiv.refl _), ?_, ?_⟩, hO⟩
  · have hLU := Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hLA hLB)
    have hSU := Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hSA hSB)
    rw [hO, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (LA ⊗ₖ LB) * U * (SA ⊗ₖ SB) * ((SA ⊗ₖ SB)ᴴ * (Uᴴ * (LA ⊗ₖ LB)ᴴ))
        = (LA ⊗ₖ LB) * (U * ((SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ) * Uᴴ) * (LA ⊗ₖ LB)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [show (SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ = 1 from hSU, Matrix.mul_one,
            hx.overlap_coisometry, Matrix.mul_one]
          exact hLU
  · rw [← globalIsometryRegrouped_eq, hF', hO]

/-- **Finite orbit decomposition** for arbitrary local dimensions. -/
theorem exists_finset_genExactTargets_eq_iUnion_orbits (s : ForwardShape) :
    ∃ R : Finset (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      (∀ U ∈ R, U ∈ genExactTargets dA dB s) ∧
        genExactTargets dA dB s = ⋃ U ∈ R, unitaryDoubleOrbit (Fin dA) (Fin dB) U := by
  classical
  obtain ⟨S, hinv, hsep⟩ := exists_finite_unitaryDoubleOrbit_separating (ιA := Fin dA)
    (ιB := Fin dB)
  let F : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ → (S → ℝ) :=
    fun U p => matrixPolyEval p.1 U
  have hfin : (F '' genExactTargets dA dB s).Finite := by
    refine (Set.Finite.pi (t := fun p : S => matrixPolyEval p.1 '' genExactTargets dA dB s)
      fun p => finite_genExactTargets_values s p.1
        fun U _ V hV => hinv p.1 p.2 U V hV).subset ?_
    rintro _ ⟨U, hU, rfl⟩ p -
    exact ⟨U, hU, rfl⟩
  have hrep : ∀ v ∈ F '' genExactTargets dA dB s, ∃ U ∈ genExactTargets dA dB s, F U = v :=
    fun v hv => hv
  let rep : (S → ℝ) → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := fun v =>
    if hv : v ∈ F '' genExactTargets dA dB s then Classical.choose (hrep v hv) else 0
  have hrep_mem : ∀ v ∈ F '' genExactTargets dA dB s,
      rep v ∈ genExactTargets dA dB s ∧ F (rep v) = v := by
    intro v hv
    simp only [rep, dite_eq_left hv]
    exact Classical.choose_spec (hrep v hv)
  refine ⟨hfin.toFinset.image rep, ?_, ?_⟩
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    exact (hrep_mem v (hfin.mem_toFinset.mp hv)).1
  · apply le_antisymm
    · intro U hU
      have hv : F U ∈ F '' genExactTargets dA dB s := ⟨U, hU, rfl⟩
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      refine ⟨rep (F U), ⟨F U, hfin.mem_toFinset.mpr hv, rfl⟩, ?_⟩
      apply hsep
      intro p hp
      exact congrFun (hrep_mem (F U) hv).2 ⟨p, hp⟩
    · simp only [Set.iUnion_subset_iff, Finset.mem_image]
      rintro _ ⟨v, hv, rfl⟩
      exact unitaryDoubleOrbit_subset_genExactTargets s (hrep_mem v (hfin.mem_toFinset.mp hv)).1

end Targets

section Protocols

variable {dA dB : ℕ}
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- A protocol on arbitrary finite registers performing a unitary on
`ℂ^{d_A} ⊗ ℂ^{d_B}` places it in the exact targets of the dimension vector of
its register cardinalities. -/
theorem PureProtocol.exists_shape_mem_genExactTargets [NeZero dA] [NeZero dB]
    (P : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB (Fin dA) (Fin dB) εA εB)
    {U : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) :
    ∃ s : ForwardShape, U ∈ genExactTargets dA dB s := by
  have hscore : scoreU U P.operationalChannel = 1 := by
    rw [show P.operationalChannel = adConj U from htask]
    exact scoreU_adConj_self hU.isIsometry
  let F := globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB
  have hFi : IsIsometry F :=
    P.isIsometry_globalIsometry.submatrix_equiv (outputRegroup (Fin dA) (Fin dB) εA εB)
      (Equiv.refl _)
  let g := scoreVector U F
  have hg : IsUnitVector g := (isUnitVector_scoreVector_iff U F).mpr hscore
  have hFr : F = insertVector (Fin dA × Fin dB) g * U :=
    (scoreU_eq_one_iff hU.isIsometry hFi).mp hscore
  let x : GenBlocks (Fin dA) (Fin dB) ρA ρB κA κB μA μB εA εB :=
    (P.resource, g, P.encA, P.encB, P.decA, P.decB)
  have hH : forwardOverlapOn x = U := by
    change (insertVector (Fin dA × Fin dB) g)ᴴ * F = U
    rw [hFr, ← Matrix.mul_assoc, (isIsometry_insertVector g hg).conjTranspose_mul_self,
      Matrix.one_mul]
  have hx : IsExactWitnessGen x := by
    refine ⟨P.resource_unit, hg, P.encA_isometry, P.encB_isometry,
      P.decA_isometry, P.decB_isometry, ?_, ?_, ?_⟩
    · exact (isIsometry_decoder P.decA_isometry P.decB_isometry).submatrix_equiv
        (outputRegroup (Fin dA) (Fin dB) εA εB) (Equiv.refl _)
    · rw [hH]
      exact hU.self_mul_conjTranspose
    · rw [← globalIsometryRegrouped_eq, hH]
      exact hFr
  -- Transport to the cardinality shape.
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
  let y : GenShapeBlocks dA dB s := reindexForwardBlocks rA rB kA kB mA mB eA eB x
  have hyH : forwardOverlapOn y = forwardOverlapOn x :=
    forwardOverlapOn_reindex rA rB kA kB mA mB eA eB x
  have hy : IsExactWitnessGen y := by
    refine ⟨hx.resource_unit.comp_equiv (rA.prodCongr rB),
      hx.witness_unit.comp_equiv (eA.prodCongr eB),
      hx.encA_isometry.submatrix_equiv _ _, hx.encB_isometry.submatrix_equiv _ _,
      hx.decA_isometry.submatrix_equiv _ _, hx.decB_isometry.submatrix_equiv _ _,
      ?_, ?_, ?_⟩
    · exact (isIsometry_decoder
        (hx.decA_isometry.submatrix_equiv _ _)
        (hx.decB_isometry.submatrix_equiv _ _)).submatrix_equiv
          (outputRegroup (Fin dA) (Fin dB) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _)
    · rw [hyH]
      exact hx.overlap_coisometry
    · rw [← globalIsometryRegrouped_eq]
      have hreg : globalIsometryRegrouped y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 =
          (globalIsometryRegrouped x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2).submatrix
            ((Equiv.refl (Fin dA × Fin dB)).prodCongr (eA.prodCongr eB)) id :=
        globalIsometryRegrouped_reindex rA rB kA kB mA mB eA eB x
      rw [hreg, globalIsometryRegrouped_eq, hx.exact, hyH]
      exact (Matrix.submatrix_mul _ _ _ id id Function.bijective_id).trans (by
        rw [Matrix.submatrix_id_id]
        rfl)
  exact ⟨s, y, hy, hyH.trans hH⟩

end Protocols

section Bad

variable {dA dB : ℕ}

/-- The exactly implementable unitaries on `ℂ^{d_A} ⊗ ℂ^{d_B}`. -/
def exactUnitaryBadGen (dA dB : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {U | UnitaryTarget U ∧ ∃ s : ForwardShape,
    ∃ P : PureProtocol (Fin dA) (Fin dB) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin dA) (Fin dB) (Fin (s 6)) (Fin (s 7)), P.PerformsUnitary U}

theorem exactUnitaryBadGen_subset_iUnion [NeZero dA] [NeZero dB] :
    exactUnitaryBadGen dA dB ⊆ ⋃ s : ForwardShape, genExactTargets dA dB s := by
  rintro U ⟨hU, s, P, hP⟩
  exact Set.mem_iUnion.mpr (P.exists_shape_mem_genExactTargets hU hP)

/-- Arbitrary finite registers in arbitrary universes reduce to
`exactUnitaryBadGen`. -/
theorem PureProtocol.mem_iUnion_genExactTargets [NeZero dA] [NeZero dB]
    {ρA : Type u₁} {ρB : Type u₂} {κA : Type u₃} {κB : Type u₄}
    {μA : Type u₅} {μB : Type u₆} {εA : Type u₇} {εB : Type u₈}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin dA) (Fin dB) ρA ρB κA κB μA μB (Fin dA) (Fin dB) εA εB)
    {U : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) : U ∈ ⋃ s : ForwardShape, genExactTargets dA dB s :=
  Set.mem_iUnion.mpr (P.exists_shape_mem_genExactTargets hU htask)

/-- **`rem:qudits`.** For local dimensions `d_A, d_B ≥ 2`, the unitaries on
`ℂ^{d_A} ⊗ ℂ^{d_B}` with an exact one-round protocol on finite registers form a
Haar-null set: they lie in the countable union of fixed-architecture target
sets, each a finite union of Haar-null local-unitary orbits. -/
theorem unitaryHaar_iUnion_genExactTargets_eq_zero (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    unitaryHaar (Fin dA × Fin dB)
      {V : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ |
        (V : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ∈
          ⋃ s : ForwardShape, genExactTargets dA dB s} = 0 := by
  have : Nontrivial (Fin dA) := Fin.nontrivial_iff_two_le.mpr hA
  have : Nontrivial (Fin dB) := Fin.nontrivial_iff_two_le.mpr hB
  choose R hR hReq using fun s => exists_finset_genExactTargets_eq_iUnion_orbits (dA := dA)
    (dB := dB) s
  have hset : {V : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ |
      (V : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ∈
        ⋃ s : ForwardShape, genExactTargets dA dB s} =
      ⋃ s : ForwardShape, ⋃ U ∈ R s, {V : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ |
        (V : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ∈
          unitaryDoubleOrbit (Fin dA) (Fin dB) U} := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hReq]
  rw [hset]
  refine measure_iUnion_null fun s => ?_
  refine (measure_biUnion_null_iff (R s).countable_toSet).mpr fun U _ => ?_
  exact unitaryHaar_unitaryDoubleOrbit_eq_zero U

/-- **`rem:qudits`, almost-every form.** Haar-almost every unitary on
`ℂ^{d_A} ⊗ ℂ^{d_B}` (`d_A, d_B ≥ 2`) is not performed exactly by any one-round
protocol on finite registers. -/
theorem ae_unitary_no_exact_protocol_gen (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    ∀ᵐ (V : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ) ∂unitaryHaar (Fin dA × Fin dB),
      (V : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ∉ exactUnitaryBadGen dA dB := by
  have : NeZero dA := ⟨by omega⟩
  have : NeZero dB := ⟨by omega⟩
  have h0 : unitaryHaar (Fin dA × Fin dB) {V : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ |
      (V : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ∈ exactUnitaryBadGen dA dB} = 0 :=
    measure_mono_null (fun V hV => exactUnitaryBadGen_subset_iUnion hV)
      (unitaryHaar_iUnion_genExactTargets_eq_zero hA hB)
  exact measure_eq_zero_iff_ae_notMem.mp h0

end Bad

end NLQCLean
