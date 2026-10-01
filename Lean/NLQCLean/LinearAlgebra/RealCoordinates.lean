/-
Real coordinates and multivariate polynomial calculus.
-/
import NLQCLean.LinearAlgebra.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Multivariate smoothness for the qualitative Sard argument

`NLQCLean.LinearAlgebra.Calculus` supplies *one-parameter* differentiation
rules (`HasDerivAt`) for the matrix operations of the exact-velocity
argument.  The scalar
Sard input `NLQCLean.scalarCriticalImage_volume_eq_zero` consumes a
`ContDiff ℝ ∞` map `f : E → ℝ` on a finite-dimensional *real* normed space,
together with its full Fréchet derivative `fderiv ℝ f`.  A one-parameter
`HasDerivAt` rule cannot establish either.  This module supplies the
multivariate layer.

## Real coordinates and norm conventions

Every space in the protocol model — `Matrix m n ℂ` and the resource/witness
Pi types `ρ → ℂ` — is already a finite-dimensional real normed space, so
`ContDiff ℝ` and `fderiv ℝ` are available on it *without* choosing
coordinates.  No identification with `EuclideanSpace ℝ (Fin N)` is needed
for smoothness, and none is made: the Sard wrapper quantifies over an
arbitrary finite-dimensional real `E`, and the source measure never enters
(the conclusion is Lebesgue nullity in the `ℝ` target).

Two norm conventions are fixed here:

* `Matrix m n ℂ` carries the **Frobenius** norm, the scoped instance fixed by
  the conventions in `NLQCLean.LinearAlgebra.Basic`.  This is the `l²` norm of
  the entries, so `NLQCLean.realCoordEquiv` below is an isometric
  statement about the entry coordinates.
* A **product** `E × F` and a **Pi type** `ι → ℝ` carry Lean's `sup` norm,
  *not* the `l²` norm.  So the six-block parameter space assembled in
  `NLQCLean.Models.ForwardWitness` is not an inner-product space on the
  nose. Smoothness and `fderiv` depend only on the
  topology, and on a finite-dimensional space all norms are equivalent.
  Euclidean volume estimates require an explicit `EuclideanSpace`
  identification; the product's default norm does not supply one.

## The three composition rules

The smoothness rules use three composition facts:

* `NLQCLean.ContDiff.clmComp` — post-composition with a continuous linear map;
* `NLQCLean.ContDiff.clmBilinear` — a continuous bilinear map of two smooth
  arguments, which covers matrix multiplication and the Kronecker product;
* `NLQCLean.ContDiff.linearMapFD` — post-composition with *any* linear map out
  of a finite-dimensional real space.  Continuity is automatic there, so
  reindexings, traces, realignment and vector insertion need no norm estimate
  at all.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius
open scoped Kronecker ContDiff

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {N : WithTop ℕ∞}

/-- Post-composition with a continuous linear map preserves smoothness.  The
lambda form is what the matrix rules below need; `ContinuousLinearMap.contDiff`
alone produces a `Function.comp`. -/
theorem ContDiff.clmComp {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => L (f x)) := by
  have h := L.contDiff.comp hf
  simp only [Function.comp_def] at h
  exact h

/-- A continuous bilinear map applied to two smooth arguments. -/
theorem ContDiff.clmBilinear {F G H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) :
    ContDiff ℝ N (fun x => B (f x) (g x)) :=
  _root_.ContDiff.clm_apply (ContDiff.clmComp B hf) hg

/-- Post-composition with an arbitrary linear map out of a finite-dimensional
real space.  Continuity is automatic, so a reindexing, a trace or a vector
insertion needs no norm estimate. -/
theorem ContDiff.linearMapFD {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →ₗ[ℝ] G) {f : E → F} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => L (f x)) := by
  have h := (LinearMap.toContinuousLinearMap L).contDiff.comp hf
  simp only [Function.comp_def] at h
  exact h

end General

section MatrixRules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {N : WithTop ℕ∞}
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- Matrix multiplication of two smooth families. -/
theorem ContDiff.matrixMul {f : E → Matrix a b ℂ} {g : E → Matrix b c ℂ}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) :
    ContDiff ℝ N (fun x => f x * g x) :=
  ContDiff.clmBilinear (mulCLM (𝕜 := ℂ) (l := a) (m := b) (n := c)) hf hg

omit [DecidableEq a] [DecidableEq b] in
/-- Conjugate transpose of a smooth family.  It is only `ℝ`-linear. -/
theorem ContDiff.matrixConjTranspose {f : E → Matrix a b ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x)ᴴ) :=
  ContDiff.clmComp (conjTransposeCLM (𝕜 := ℂ) (m := a) (n := b)) hf

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- Kronecker product of two smooth families. -/
theorem ContDiff.matrixKronecker {d : Type*} [Fintype d] [DecidableEq d]
    {f : E → Matrix a b ℂ} {g : E → Matrix c d ℂ}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) :
    ContDiff ℝ N (fun x => f x ⊗ₖ g x) :=
  ContDiff.clmBilinear
    (kroneckerCLM (𝕜 := ℂ) (l := a) (m := b) (n := c) (p := d)) hf hg

/-- Reindexing by fixed index functions, as a `ℂ`-linear map.  This covers the
fixed exchange permutation and the output regrouping of the architecture. -/
def submatrixLM (r : a → b) (c' : c → a) :
    Matrix b a ℂ →ₗ[ℂ] Matrix a c ℂ where
  toFun := fun M => M.submatrix r c'
  map_add' := by intros; ext i j; simp
  map_smul' := by intros; ext i j; simp

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
@[simp] theorem submatrixLM_apply (r : a → b) (c' : c → a) (M : Matrix b a ℂ) :
    submatrixLM r c' M = M.submatrix r c' := rfl

omit [DecidableEq a] [DecidableEq b] in
/-- A fixed reindexing of a smooth family is smooth. -/
theorem ContDiff.matrixSubmatrix {a' b' : Type*} [Fintype a'] [Fintype b']
    {f : E → Matrix a b ℂ} (hf : ContDiff ℝ N f) (r : a' → a) (c' : b' → b) :
    ContDiff ℝ N (fun x => (f x).submatrix r c') :=
  ContDiff.linearMapFD
    ({ toFun := fun M => M.submatrix r c'
       map_add' := by intros; ext i j; simp
       map_smul' := by intros; ext i j; simp } :
      Matrix a b ℂ →ₗ[ℝ] Matrix a' b' ℂ) hf

omit [DecidableEq a] in
/-- The trace of a smooth square family. -/
theorem ContDiff.matrixTrace {f : E → Matrix a a ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => Matrix.trace (f x)) :=
  ContDiff.linearMapFD
    ((Matrix.traceLinearMap a ℂ ℂ).restrictScalars ℝ) hf

/-- The real part of a smooth complex-valued family. -/
theorem ContDiff.complexRe {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x).re) :=
  ContDiff.clmComp Complex.reCLM hf

/-- The imaginary part of a smooth complex-valued family. -/
theorem ContDiff.complexIm {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x).im) :=
  ContDiff.clmComp Complex.imCLM hf

/-- The squared modulus of a smooth complex-valued family.  It is the real
polynomial `re² + im²`, so no complex differentiability is involved; this is
the form the unitary score is built from. -/
theorem ContDiff.complexNormSq {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => Complex.normSq (f x)) := by
  have h : (fun x => Complex.normSq (f x))
      = fun x => (f x).re * (f x).re + (f x).im * (f x).im := by
    funext x; rw [Complex.normSq_apply]
  rw [h]
  exact ((ContDiff.complexRe hf).mul (ContDiff.complexRe hf)).add
    ((ContDiff.complexIm hf).mul (ContDiff.complexIm hf))

omit [DecidableEq a] [DecidableEq b] in
/-- A single entry of a smooth matrix family. -/
theorem ContDiff.matrixEntry {f : E → Matrix a b ℂ} (hf : ContDiff ℝ N f) (i : a) (j : b) :
    ContDiff ℝ N (fun x => f x i j) :=
  ContDiff.clmComp (entryCLM (𝕜 := ℂ) i j) hf

end MatrixRules

section RealCoordinates

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- The real coordinates of a complex matrix: its entrywise real and imaginary
parts. Their `l²` norm is the Frobenius norm, as expressed by
`NLQCLean.frobNorm_sq_realCoord`. -/
def realPart (M : Matrix a b ℂ) : Matrix a b ℝ := Matrix.of fun i j => (M i j).re

/-- The imaginary coordinates of a complex matrix. -/
def imagPart (M : Matrix a b ℂ) : Matrix a b ℝ := Matrix.of fun i j => (M i j).im

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
@[simp] theorem realPart_apply (M : Matrix a b ℂ) (i : a) (j : b) :
    realPart M i j = (M i j).re := rfl

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
@[simp] theorem imagPart_apply (M : Matrix a b ℂ) (i : a) (j : b) :
    imagPart M i j = (M i j).im := rfl

omit [DecidableEq a] [DecidableEq b] in
/-- The Frobenius norm is the Euclidean norm of the real coordinates. -/
theorem frobNorm_sq_realCoord (M : Matrix a b ℂ) :
    ‖M‖ ^ 2 = ∑ i : a, ∑ j : b, ((realPart M i j) ^ 2 + (imagPart M i j) ^ 2) := by
  rw [frobNorm_sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [realPart_apply, imagPart_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

end RealCoordinates

section Realignment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Realignment**: `R(H)_{(i,k),(j,l)} = H_{(i,j),(k,l)}`.

This is *not* a `Matrix.submatrix`: the row index of `H` draws its first
component from the row of `R H` and its second from the column, so the
reindexing crosses the row/column split.  It is nevertheless entrywise, hence
`ℂ`-linear, which is all that the smoothness argument needs. -/
def realign (H : Matrix (ι × ι) (ι × ι) ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun p q => H (p.1, q.1) (p.2, q.2)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realign_apply (H : Matrix (ι × ι) (ι × ι) ℂ) (p q : ι × ι) :
    realign H p q = H (p.1, q.1) (p.2, q.2) := rfl

/-- Realignment as a `ℂ`-linear map. -/
def realignLM : Matrix (ι × ι) (ι × ι) ℂ →ₗ[ℂ] Matrix (ι × ι) (ι × ι) ℂ where
  toFun := realign
  map_add' := by intros; ext p q; simp
  map_smul' := by intros; ext p q; simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realignLM_apply (H : Matrix (ι × ι) (ι × ι) ℂ) :
    realignLM H = realign H := rfl

/-- **The realignment-purity polynomial**, with explicit real normalization:
`p(H) = c · Re Tr[(R(H) R(H)†)²]`. The normalized purity takes `c = D⁻²`.

The trace is already real and nonnegative because `R(H) R(H)†` is Hermitian;
`Re` is taken so that the expression is a real polynomial in the real
coordinates for *every* complex `H`, with no denominator depending on `H`. -/
def purity (c : ℝ) (H : Matrix (ι × ι) (ι × ι) ℂ) : ℝ :=
  c * (Matrix.trace ((realign H * (realign H)ᴴ) * (realign H * (realign H)ᴴ))).re

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {N : WithTop ℕ∞}

omit [DecidableEq ι] in
/-- Realignment of a smooth family is smooth. -/
theorem ContDiff.realign {f : E → Matrix (ι × ι) (ι × ι) ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.realign (f x)) :=
  ContDiff.linearMapFD (realignLM.restrictScalars ℝ) hf

omit [DecidableEq ι] in
/-- The realignment-purity expression is smooth by composition. -/
theorem ContDiff.purity (c : ℝ) {f : E → Matrix (ι × ι) (ι × ι) ℂ}
    (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.purity c (f x)) := by
  have hR : ContDiff ℝ N (fun x => NLQCLean.realign (f x)) := ContDiff.realign hf
  have hRR : ContDiff ℝ N (fun x => NLQCLean.realign (f x) * (NLQCLean.realign (f x))ᴴ) :=
    ContDiff.matrixMul hR (ContDiff.matrixConjTranspose hR)
  exact (ContDiff.complexRe (ContDiff.matrixTrace (ContDiff.matrixMul hRR hRR))).const_smul c

end Realignment

end NLQCLean
