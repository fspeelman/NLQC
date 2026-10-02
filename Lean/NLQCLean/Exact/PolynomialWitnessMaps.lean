import NLQCLean.Semialgebraic.PolynomialFunctions
import NLQCLean.Exact.PVMInvariantCriticalValues
import NLQCLean.Invariants.LocalOrbitSeparation

/-!
# Protocol maps are polynomial in the strategy blocks

Resource and environment insertion, flag isometries, the exchange, the
global isometry and both forward overlaps have polynomial real and imaginary
entries in the blocks of a strategy. The exact unitary and two-sided PVM
witness conditions are therefore polynomial zero sets.
-/

noncomputable section

namespace NLQCLean

open Matrix
open scoped Kronecker

section Maps

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyVec.of_linear {ι : Type*} (L : E →ₗ[ℝ] (ι → ℂ)) : IsPolyVec L := fun i =>
  IsComplexPoly.linear ((LinearMap.proj i).comp L)

theorem IsPolyVec.apply {δ ι : Type*} {ω : E → δ → ι → ℂ} (hω : ∀ i, IsPolyVec fun x => ω x i)
    (i : δ) : IsPolyVec (fun x => ω x i) := hω i

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB δ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq δ] [DecidableEq ιA'] [DecidableEq ιB']

omit [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] in
theorem IsPolyMatrix.insertResource {η : E → ρA × ρB → ℂ} (hη : IsPolyVec η) :
    IsPolyMatrix (fun x => insertResource ιA ιB (η x)) := fun p _ =>
  (IsComplexPoly.const _).mul (hη (p.1.2, p.2.2))

omit [DecidableEq δ] in
theorem IsPolyMatrix.insertVector (κ : Type*) [DecidableEq κ] {g : E → εA × εB → ℂ}
    (hg : IsPolyVec g) : IsPolyMatrix (fun x => NLQCLean.insertVector κ (g x)) := fun p _ =>
  (IsComplexPoly.const _).mul (hg p.2)

theorem IsPolyMatrix.flagIsometry {ω : E → δ → εA × εB → ℂ}
    (hω : ∀ i, IsPolyVec fun x => ω x i) :
    IsPolyMatrix (fun x => NLQCLean.flagIsometry (ω x)) := fun p i =>
  (IsComplexPoly.const _).mul (hω i (p.1.2, p.2.2))

variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ιA'] [DecidableEq ιB'] [Fintype ιA']
  [Fintype ιB'] [Fintype εA] [Fintype εB] in
theorem IsPolyMatrix.globalIsometry {η : E → ρA × ρB → ℂ}
    {VA : E → Matrix (κA × μA) (ιA × ρA) ℂ} {VB : E → Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : E → Matrix (ιA' × εA) (κA × μB) ℂ} {DB : E → Matrix (ιB' × εB) (κB × μA) ℂ}
    (hη : IsPolyVec η) (hVA : IsPolyMatrix VA) (hVB : IsPolyMatrix VB)
    (hDA : IsPolyMatrix DA) (hDB : IsPolyMatrix DB) :
    IsPolyMatrix (fun x => NLQCLean.globalIsometry (η x) (VA x) (VB x) (DA x) (DB x)) := by
  simp only [globalIsometry_eq]
  exact (hDA.kronecker hDB).mul ((IsPolyMatrix.const _).mul
    ((hVA.kronecker hVB).mul (IsPolyMatrix.insertResource hη)))

end Maps

section PVMWitness

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

local notation "PB" => PVMForwardBlocks d ρA ρB κA κB μA μB εA εB

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
/-- Block projections of the PVM strategy space. -/
theorem isPolyVec_pvm_resource : IsPolyVec (fun x : PB => x.1) :=
  IsPolyVec.of_linear (LinearMap.fst ℝ (ρA × ρB → ℂ) _ : PB →ₗ[ℝ] (ρA × ρB → ℂ))

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyVec_pvm_flag (i : Fin d × Fin d) : IsPolyVec (fun x : PB => x.2.1 i) :=
  IsPolyVec.of_linear ((LinearMap.proj i).comp ((LinearMap.fst ℝ _ _).comp
    (LinearMap.snd ℝ (ρA × ρB → ℂ) _)) : PB →ₗ[ℝ] (εA × εB → ℂ))

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvm_encA : IsPolyMatrix (fun x : PB => x.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    (LinearMap.snd ℝ _ _)) : PB →ₗ[ℝ] Matrix (κA × μA) (Fin d × ρA) ℂ)

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvm_encB : IsPolyMatrix (fun x : PB => x.2.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))) : PB →ₗ[ℝ] Matrix (κB × μB) (Fin d × ρB) ℂ)

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvm_decA : IsPolyMatrix (fun x : PB => x.2.2.2.2.1) :=
  IsPolyMatrix.linear ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))) :
      PB →ₗ[ℝ] Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ)

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
  [DecidableEq μB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvm_decB : IsPolyMatrix (fun x : PB => x.2.2.2.2.2) :=
  IsPolyMatrix.linear ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))) :
      PB →ₗ[ℝ] Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ)

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvm_global :
    IsPolyMatrix (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB =>
      globalIsometry x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) :=
  IsPolyMatrix.globalIsometry isPolyVec_pvm_resource isPolyMatrix_pvm_encA isPolyMatrix_pvm_encB
    isPolyMatrix_pvm_decA isPolyMatrix_pvm_decB

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
theorem isPolyMatrix_pvmOverlapOn :
    IsPolyMatrix (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => pvmOverlapOn x) :=
  (IsPolyMatrix.flagIsometry isPolyVec_pvm_flag).conjTranspose.mul isPolyMatrix_pvm_global

/-- The isometry condition as a polynomial zero set. -/
theorem IsPolyMatrix.isPolyZeroSet_isIsometry {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F) : IsPolyZeroSet {x | IsIsometry (F x)} :=
  hF.conjTranspose.mul hF |>.isPolyZeroSet_eq (IsPolyMatrix.const 1)

omit [DecidableEq εA] [DecidableEq εB] in
/-- The exact two-sided PVM witness locus is a polynomial zero set. -/
theorem isPolyZeroSet_isExactPVMWitness :
    IsPolyZeroSet {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB | IsExactPVMWitness x} := by
  have hO := isPolyMatrix_pvmOverlapOn (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have h8 := (isPolyMatrix_pvm_global (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_eq
    ((IsPolyMatrix.flagIsometry isPolyVec_pvm_flag).mul hO)
  have h7 := (hO.mul hO.conjTranspose).isPolyZeroSet_eq
    (IsPolyMatrix.const (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
  have h6 := (isPolyMatrix_pvm_decB (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h5 := (isPolyMatrix_pvm_decA (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h4 := (isPolyMatrix_pvm_encB (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h3 := (isPolyMatrix_pvm_encA (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)).isPolyZeroSet_isIsometry
  have h2 := IsPolyZeroSet.iInter fun i => isPolyZeroSet_isUnitVector
    (isPolyVec_pvm_flag (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
      (μA := μA) (μB := μB) (εA := εA) (εB := εB) i)
  have h1 := isPolyZeroSet_isUnitVector (isPolyVec_pvm_resource (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB))
  have h := h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter h8))))))
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro hx
    exact ⟨hx.resource_unit, hx.flag_unit, hx.encA_isometry, hx.encB_isometry,
      hx.decA_isometry, hx.decB_isometry, hx.overlap_coisometry, hx.exact⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end PVMWitness

section Composition

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A real polynomial evaluated at polynomial coordinate functions. -/
theorem IsRealPoly.eval_comp {σ : Type*} {c : σ → E → ℝ} (hc : ∀ i, IsRealPoly (c i))
    (p : MvPolynomial σ ℝ) : IsRealPoly (fun x => MvPolynomial.eval (fun i => c i x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using IsRealPoly.const (E := E) a
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hc i)

/-- A real polynomial in the entries of a polynomial matrix. -/
theorem IsPolyMatrix.matrixPolyEval {m n : Type*} {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F)
    (p : MvPolynomial ((m × n) × Fin 2) ℝ) :
    IsRealPoly (fun x => matrixPolyEval p (F x)) := by
  refine IsRealPoly.eval_comp (c := fun v x => matrixRealCoords m n (F x) v) (fun v => ?_) p
  by_cases hv : v.2 = 0
  · simpa [hv] using (hF v.1.1 v.1.2).1
  · simpa [hv] using (hF v.1.1 v.1.2).2

end Composition

section LinearComposition

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup E'] [Module ℝ E'] [FiniteDimensional ℝ E']

theorem IsRealPoly.comp_linear {f : E → ℝ} (hf : IsRealPoly f) (L : E' →ₗ[ℝ] E) :
    IsRealPoly (fun x => f (L x)) := by
  obtain ⟨p, hp⟩ := hf
  simp only [hp]
  exact IsRealPoly.eval_comp (c := fun i x => polyCoords E (L x) i)
    (fun i => IsRealPoly.linear ((LinearMap.proj i).comp ((polyCoords E).toLinearMap.comp L))) p

theorem IsPolyMatrix.comp_linear {m n : Type*} {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F)
    (L : E' →ₗ[ℝ] E) : IsPolyMatrix (fun x => F (L x)) := fun i j =>
  ⟨(hF i j).1.comp_linear L, (hF i j).2.comp_linear L⟩

theorem IsPolyVec.comp_linear {ι : Type*} {v : E → ι → ℂ} (hv : IsPolyVec v)
    (L : E' →ₗ[ℝ] E) : IsPolyVec (fun x => v (L x)) := fun i =>
  ⟨(hv i).1.comp_linear L, (hv i).2.comp_linear L⟩

theorem IsPolyMatrix.neg {m n : Type*} {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F) :
    IsPolyMatrix (fun x => -F x) := fun i j => (hF i j).neg

end LinearComposition

end NLQCLean
