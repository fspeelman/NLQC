/-
Isometries and the differentiation facts the cross-Gram lemma needs.
-/
import NLQCLean.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiable paths of matrices and of isometries

`lem:cross-gram-rigidity` (snapshot L697-735) differentiates `H = B†A` along a
path of isometries.  Two operations therefore have to be known differentiable:
conjugate transpose and matrix multiplication.  Neither is a `NormedRing`
operation here, because the paper's `A` and `B` are *rectangular*, so
Mathlib's `HasDerivAt.mul` does not apply.  Both are bundled below as
continuous `ℝ`-linear (resp. bilinear) maps for the Frobenius norm, which is
the instance fixed in `NLQCLean.LinearAlgebra.Basic`.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius
open scoped Kronecker

variable {𝕜 : Type*} [RCLike 𝕜]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- Conjugate transpose as a continuous `ℝ`-linear map.  It is only
`ℝ`-linear, not `𝕜`-linear: it is conjugate-linear over `𝕜`. -/
noncomputable def conjTransposeCLM : Matrix m n 𝕜 →L[ℝ] Matrix n m 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by ext i j; simp }
    1 (fun A => by simp)

omit [DecidableEq m] [DecidableEq n] in
@[simp]
theorem conjTransposeCLM_apply (A : Matrix m n 𝕜) :
    conjTransposeCLM (𝕜 := 𝕜) A = Aᴴ := rfl

omit [DecidableEq m] [DecidableEq n] in
theorem HasDerivAt.matrixConjTranspose {A : ℝ → Matrix m n 𝕜} {A' : Matrix m n 𝕜}
    {t : ℝ} (h : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s)ᴴ) (A'ᴴ) t := by
  have h2 := (conjTransposeCLM (𝕜 := 𝕜)).hasFDerivAt.comp_hasDerivAt t h
  simp only [Function.comp_def, conjTransposeCLM_apply] at h2
  exact h2

/-- Matrix multiplication as a continuous `ℝ`-bilinear map.  The paper's `A`
and `B` are rectangular, so `Matrix` is not a `NormedRing` here and
`HasDerivAt.mul` does not apply; this supplies the product rule instead.  The
bound is `Matrix.frobenius_norm_mul`. -/
noncomputable def mulCLM : Matrix l m 𝕜 →L[ℝ] Matrix m n 𝕜 →L[ℝ] Matrix l n 𝕜 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) => A * B)
      (fun A₁ A₂ B => Matrix.add_mul A₁ A₂ B)
      (fun r A B => by ext i j; simp [Matrix.mul_apply, ← Finset.smul_sum])
      (fun A B₁ B₂ => Matrix.mul_add A B₁ B₂)
      (fun r A B => by ext i j; simp [Matrix.mul_apply, ← Finset.smul_sum]))
    1 (fun A B => by simpa using Matrix.frobenius_norm_mul A B)

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] in
@[simp]
theorem mulCLM_apply (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    mulCLM (𝕜 := 𝕜) A B = A * B := rfl

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] in
/-- Product rule for rectangular matrix multiplication. -/
theorem HasDerivAt.matrixMul {f : ℝ → Matrix l m 𝕜} {g : ℝ → Matrix m n 𝕜}
    {f' : Matrix l m 𝕜} {g' : Matrix m n 𝕜} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s * g s) (f t * g' + f' * g t) t := by
  have h := ContinuousLinearMap.hasDerivAt_of_bilinear (B := mulCLM (𝕜 := 𝕜))
    (fun _ => hf) (fun _ => hg)
  exact h

/-- `A` is an isometry, i.e. `A† A = 1`.  The paper's `A(t), B(t) : ℂ^D → 𝒦`
of `lem:cross-gram-rigidity` (snapshot L697-703) are isometries in this
sense. -/
def IsIsometry (A : Matrix m n 𝕜) : Prop := Aᴴ * A = 1

omit [Fintype n] [DecidableEq m] in
theorem IsIsometry.conjTranspose_mul_self {A : Matrix m n 𝕜} (h : IsIsometry A) :
    Aᴴ * A = 1 := h

/-- The identity is an isometry. -/
theorem isIsometry_one : IsIsometry (1 : Matrix n n 𝕜) := by
  show (1 : Matrix n n 𝕜)ᴴ * 1 = 1
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

omit [Fintype n] [DecidableEq l] in
/-- A composition of isometries is an isometry: `(AB)†(AB) = B†(A†A)B = B†B`.

This is what makes the global Stinespring isometry of eq:global-isometry
(snapshot L456-460) an isometry: it is a product of four of them. -/
theorem IsIsometry.mul {A : Matrix l m 𝕜} {B : Matrix m n 𝕜}
    (hA : IsIsometry A) (hB : IsIsometry B) : IsIsometry (A * B) := by
  show (A * B)ᴴ * (A * B) = 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ,
    hA.conjTranspose_mul_self, Matrix.one_mul, hB.conjTranspose_mul_self]

omit [Fintype m] [DecidableEq l] in
/-- A tensor product of isometries is an isometry.  This is the form used for
`V_A ⊗ V_B` and `D_A ⊗ D_B` in eq:global-isometry (snapshot L456-460). -/
theorem IsIsometry.kronecker {l' m' : Type*} [Fintype l'] [Fintype m']
    [DecidableEq l'] [DecidableEq m'] {A : Matrix l m 𝕜} {B : Matrix l' m' 𝕜}
    (hA : IsIsometry A) (hB : IsIsometry B) :
    IsIsometry (A ⊗ₖ B) := by
  show (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hA.conjTranspose_mul_self, hB.conjTranspose_mul_self]
  exact Matrix.one_kronecker_one

omit [DecidableEq m] in
/-- The range projection `A A†` of an isometry is idempotent. -/
theorem IsIsometry.rangeProj_idem {A : Matrix m n 𝕜} (h : IsIsometry A) :
    (A * Aᴴ) * (A * Aᴴ) = A * Aᴴ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h.conjTranspose_mul_self,
    Matrix.one_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The range projection is self-adjoint. -/
theorem rangeProj_conjTranspose (A : Matrix m n 𝕜) : (A * Aᴴ)ᴴ = A * Aᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [DecidableEq m] in
/-- Differentiating the isometry constraint `A†A = 1`, **locally**.

This is the identity that makes the cross-Gram velocity decomposition close:
in the proof of `lem:cross-gram-rigidity` (snapshot L737-750) the terms
`-ℓ_out H` and the normal parts only recombine into `Ḃ†A + B†Ȧ` because
`Ḃ†B + B†Ḃ = 0`.

The isometry hypothesis is `∀ᶠ s in 𝓝 t` rather than `∀ s : ℝ` for two
reasons.  First, `thm:finite-orbit` (snapshot L906-913) applies
`prop:exact-velocity` on the *open subintervals* between the finitely many
parameter values where the semialgebraic path fails to be analytic, where a
global-in-`ℝ` hypothesis is unavailable.  Second, the paper hypothesizes a
differentiable family of protocols, and `∀ s : ℝ, IsIsometry (A s)` is
strictly stronger than what that gives at a point, so assuming it would
weaken every theorem downstream. -/
theorem isometry_hasDerivAt_skew_of_eventually {A : ℝ → Matrix m n 𝕜}
    {A' : Matrix m n 𝕜} {t : ℝ} (hiso : ∀ᶠ s in nhds t, IsIsometry (A s))
    (h : HasDerivAt A A' t) :
    (A t)ᴴ * A' + A'ᴴ * A t = 0 := by
  have hd : HasDerivAt (fun s => (A s)ᴴ * A s) ((A t)ᴴ * A' + A'ᴴ * A t) t :=
    HasDerivAt.matrixMul (HasDerivAt.matrixConjTranspose h) h
  have hconst : HasDerivAt (fun s => (A s)ᴴ * A s) 0 t := by
    refine (hasDerivAt_const t (1 : Matrix n n 𝕜)).congr_of_eventuallyEq ?_
    filter_upwards [hiso] with s hs using hs
  exact hd.unique hconst

omit [DecidableEq m] in
/-- The global form of `NLQCLean.isometry_hasDerivAt_skew_of_eventually`. -/
theorem isometry_hasDerivAt_skew {A : ℝ → Matrix m n 𝕜} {A' : Matrix m n 𝕜}
    {t : ℝ} (hiso : ∀ s, IsIsometry (A s)) (h : HasDerivAt A A' t) :
    (A t)ᴴ * A' + A'ᴴ * A t = 0 :=
  isometry_hasDerivAt_skew_of_eventually (Filter.Eventually.of_forall hiso) h

section UnitColumns

/-!
## Unit vectors and the unit-column criterion

Three different matrices in this development — the shared-state insertion
`J_η` of snapshot L449-454, the flag isometry `C_ω` of eq:flag-isometry
(L605-611), and the minimal environment insertion `J_γ` used for
eq:frozen-unitary (L649-653) — are isometries for one and the same reason:
their columns are supported on pairwise disjoint blocks of rows, and each
column is a unit vector inside its block.  That criterion is proved once here
and instantiated three times.
-/

variable {ε : Type*} [Fintype ε]

/-- `v` is a unit vector of `ℂ^ε`, i.e. `‖v‖² = Σ_e |v_e|² = 1`. -/
def IsUnitVector (v : ε → ℂ) : Prop := ∑ e, Complex.normSq (v e) = 1

theorem sum_mul_star_eq_normSq (v : ε → ℂ) :
    ∑ e, v e * star (v e) = ((∑ e, Complex.normSq (v e) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [← starRingEnd_apply, Complex.mul_conj]

/-- The unit-vector condition in its Hermitian-form guise. -/
theorem isUnitVector_iff_sum (v : ε → ℂ) :
    IsUnitVector v ↔ ∑ e, v e * star (v e) = 1 := by
  rw [sum_mul_star_eq_normSq, IsUnitVector]
  constructor
  · intro h; rw [h]; norm_num
  · intro h; exact_mod_cast h

/-- **Unit-column criterion.**  Let `row : μ ≃ κ × ε` split the row index into
a *block label* and a *within-block* label, let `φ : ι → κ` assign to each
column its block injectively, and let each column carry the unit vector
`v i` inside its block.  Then the matrix is an isometry.

The two `if`-factors of `NLQCLean.insertResource` and of
`NLQCLean.flagIsometry` combine into the single block-label delta
`if (row p).1 = φ i then 1 else 0`, so both are instances, as is
`NLQCLean.insertVector`. -/
theorem isIsometry_of_unit_columns {ι κ μ : Type*}
    [Fintype ι] [Fintype μ] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (row : μ ≃ κ × ε) (φ : ι → κ) (hφ : Function.Injective φ)
    (v : ι → ε → ℂ) (hv : ∀ i, IsUnitVector (v i))
    {C : Matrix μ ι ℂ}
    (hC : ∀ p i, C p i = (if (row p).1 = φ i then 1 else 0) * v i (row p).2) :
    IsIsometry C := by
  show Cᴴ * C = 1
  ext i j
  rw [Matrix.mul_apply]
  have key : (∑ p : μ, Cᴴ i p * C p j)
      = ∑ q : κ × ε, star ((if q.1 = φ i then (1 : ℂ) else 0) * v i q.2)
          * ((if q.1 = φ j then (1 : ℂ) else 0) * v j q.2) :=
    Fintype.sum_equiv row _ _ (fun p => by
      rw [Matrix.conjTranspose_apply, hC p i, hC p j])
  rw [key, Fintype.sum_prod_type]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq]
    rw [Finset.sum_eq_single_of_mem (φ i) (Finset.mem_univ _)
      (fun k _ hk => by simp [hk])]
    refine Eq.trans ?_ ((isUnitVector_iff_sum (v i)).1 (hv i))
    exact Finset.sum_congr rfl fun e _ => by simp [mul_comm]
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun e _ => ?_
    rcases eq_or_ne k (φ i) with rfl | hk
    · have hne : φ i ≠ φ j := fun h => hij (hφ h)
      simp [hne]
    · simp [hk]

end UnitColumns

end NLQCLean
