/-
Analytic plumbing for differentiable families of matrices.
-/
import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Differentiating the constructions that `prop:exact-velocity` needs

`NLQCLean.LinearAlgebra.Isometry` already supplies the two differentiation
rules that `lem:cross-gram-rigidity` uses: conjugate transpose and rectangular
matrix multiplication.  `prop:exact-velocity` (snapshot L786-873) needs three
more operations to be known differentiable, because the objects it
differentiates are built out of the protocol data rather than out of the
cross-Gram matrices themselves:

* the Kronecker product, for `V_A ⊗ V_B` and `D_A ⊗ D_B` of eq:global-isometry
  (L456-460);
* extraction of a single matrix entry, and of a *family* of entries indexed by
  a further finite type, for the frozen witnesses `γ` and `ω`
  (`NLQCLean.frozen_unitary_witness_eq`, `NLQCLean.frozen_pvm_witness_eq`);
* an arbitrary linear map out of a finite-dimensional real normed space, which
  covers `η ↦ J_η` and `ω ↦ C_ω` without any bespoke norm estimate.

The last analytic ingredient is the scalar `⟨η|η̇⟩` of eq:input-compression
(L845-852) and `⟨γ|γ̇⟩` of eq:output-compression (L853-860): differentiating a
unit-norm family makes them purely imaginary, which is what puts them into the
scalar direction `iℝI ⊆ 𝔤_{A:B}` (L578-579).

Every norm here is the Frobenius norm, which is the `NormedAddCommGroup`
instance fixed in `NLQCLean.LinearAlgebra.Basic`. Mathlib's `@[simp]` Frobenius
lemmas are stated against a *local* instance and do not fire under the scoped
one, so `NLQCLean.frobNorm_kronecker` is proved entrywise from
`NLQCLean.frobNorm_sq`; Mathlib supplies the bilinearity of
`Matrix.kroneckerBilinear` but no Frobenius bound for it.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius
open scoped Kronecker

section DirectionalToFrechet

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The line through `x` in direction `v`. -/
theorem hasDerivAt_line (x v : E) : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  simp only [one_smul, id_eq] at h
  exact h

/-- A directional derivative identifies the ambient Fréchet derivative applied
to that direction. -/
theorem fderiv_apply_eq_of_hasDerivAt_line {f : E → F} {x v : E} {w : F}
    (hf : DifferentiableAt ℝ f x)
    (hw : HasDerivAt (fun t : ℝ => f (x + t • v)) w 0) : fderiv ℝ f x v = w := by
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt 0 (hasDerivAt_line x v)).unique hw

/-- The scalar specialization as a derivative statement along a line. -/
theorem fderiv_apply_eq_line_deriv {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : E) : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hx : x + (0 : ℝ) • v = x := by simp
  have hfd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    rw [hx]
    exact hf.hasFDerivAt
  exact hfd.comp_hasDerivAt 0 (hasDerivAt_line x v)

/-- Vanishing directional derivatives along every line imply that the full
Fréchet derivative vanishes. -/
theorem fderiv_eq_zero_of_hasDerivAt_lines {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v : E, HasDerivAt (fun t : ℝ => f (x + t • v)) 0 0) :
    fderiv ℝ f x = 0 := by
  ext v
  exact (fderiv_apply_eq_line_deriv hf v).unique (h v)

end DirectionalToFrechet

variable {𝕜 : Type*} [RCLike 𝕜]
variable {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

section EntryBound

omit [DecidableEq m] [DecidableEq n] in
/-- Every entry is dominated by the Frobenius norm.  Mathlib has no such
lemma for the `Matrix.Norms.Frobenius` scoped instance. -/
theorem frobNorm_entry_le (M : Matrix m n 𝕜) (i : m) (j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h : ‖M i j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    rw [frobNorm_sq]
    calc ‖M i j‖ ^ 2
        ≤ ∑ j' : n, ‖M i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' : n => ‖M i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i' : m, ∑ j' : n, ‖M i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' : m => ∑ j' : n, ‖M i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h1 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

end EntryBound

section Kronecker

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- The Frobenius norm is multiplicative on Kronecker products. -/
theorem frobNorm_sq_kronecker (A : Matrix l m 𝕜) (B : Matrix n p 𝕜) :
    ‖A ⊗ₖ B‖ ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  have hL : ‖A ⊗ₖ B‖ ^ 2
      = ∑ i : l, ∑ k : n, ∑ j : m, ∑ r : p, ‖A i j‖ ^ 2 * ‖B k r‖ ^ 2 := by
    rw [frobNorm_sq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.kronecker_apply, norm_mul, mul_pow]
  have hInner : ∀ (i : l) (k : n),
      (∑ j : m, ∑ r : p, ‖A i j‖ ^ 2 * ‖B k r‖ ^ 2)
        = (∑ j : m, ‖A i j‖ ^ 2) * (∑ r : p, ‖B k r‖ ^ 2) := by
    intro i k
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hL]
  simp_rw [hInner]
  rw [frobNorm_sq, frobNorm_sq]
  conv_rhs => rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- `‖A ⊗ₖ B‖_F = ‖A‖_F ‖B‖_F`.  This is the bound that makes the Kronecker
product a *continuous* bilinear map for the Frobenius norm; Mathlib supplies
`Matrix.kroneckerBilinear` but no norm estimate for it. -/
theorem frobNorm_kronecker (A : Matrix l m 𝕜) (B : Matrix n p 𝕜) :
    ‖A ⊗ₖ B‖ = ‖A‖ * ‖B‖ := by
  have h : ‖A ⊗ₖ B‖ ^ 2 = (‖A‖ * ‖B‖) ^ 2 := by
    rw [frobNorm_sq_kronecker, mul_pow]
  have h1 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h1

/-- The Kronecker product as a continuous `ℝ`-bilinear map, the analogue of
`NLQCLean.mulCLM` for the tensor factorizations of eq:global-isometry
(snapshot L456-460). -/
noncomputable def kroneckerCLM :
    Matrix l m 𝕜 →L[ℝ] Matrix n p 𝕜 →L[ℝ] Matrix (l × n) (m × p) 𝕜 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (A : Matrix l m 𝕜) (B : Matrix n p 𝕜) => A ⊗ₖ B)
      (fun A₁ A₂ B => Matrix.add_kronecker A₁ A₂ B)
      (fun r A B => Matrix.smul_kronecker r A B)
      (fun A B₁ B₂ => Matrix.kronecker_add A B₁ B₂)
      (fun r A B => Matrix.kronecker_smul r A B))
    1 (fun A B => by simpa using (frobNorm_kronecker A B).le)

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
@[simp]
theorem kroneckerCLM_apply (A : Matrix l m 𝕜) (B : Matrix n p 𝕜) :
    kroneckerCLM (𝕜 := 𝕜) A B = A ⊗ₖ B := rfl

omit [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- Product rule for the Kronecker product,
`d/dt (f ⊗ₖ g) = f ⊗ₖ ġ + ḟ ⊗ₖ g`.  The summand order is Mathlib's
convention for `ContinuousLinearMap.hasDerivAt_of_bilinear`, matching
`NLQCLean.HasDerivAt.matrixMul`. -/
theorem HasDerivAt.matrixKronecker {f : ℝ → Matrix l m 𝕜} {g : ℝ → Matrix n p 𝕜}
    {f' : Matrix l m 𝕜} {g' : Matrix n p 𝕜} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⊗ₖ g s) (f t ⊗ₖ g' + f' ⊗ₖ g t) t :=
  ContinuousLinearMap.hasDerivAt_of_bilinear (B := kroneckerCLM (𝕜 := 𝕜))
    (fun _ => hf) (fun _ => hg)

end Kronecker

section Entries

/-- Extraction of a single matrix entry as a continuous `ℝ`-linear map. -/
noncomputable def entryCLM (i : m) (j : n) : Matrix m n 𝕜 →L[ℝ] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun M => by rw [one_mul]; exact frobNorm_entry_le M i j)

omit [DecidableEq m] [DecidableEq n] in
@[simp]
theorem entryCLM_apply (i : m) (j : n) (M : Matrix m n 𝕜) :
    entryCLM (𝕜 := 𝕜) i j M = M i j := rfl

omit [DecidableEq m] [DecidableEq n] in
/-- Differentiating a single entry of a differentiable matrix family. -/
theorem HasDerivAt.matrixEntry {f : ℝ → Matrix m n 𝕜} {f' : Matrix m n 𝕜} {t : ℝ}
    (h : HasDerivAt f f' t) (i : m) (j : n) :
    HasDerivAt (fun s => f s i j) (f' i j) t := by
  have h2 := (entryCLM (𝕜 := 𝕜) i j).hasFDerivAt.comp_hasDerivAt t h
  simp only [Function.comp_def, entryCLM_apply] at h2
  exact h2

variable {ε : Type*} [Fintype ε]

/-- Extraction of a *family* of entries: `M ↦ (e ↦ M (r e) (c e))`.

This is the shape of both frozen witnesses.  For the unitary branch,
`NLQCLean.frozen_unitary_witness_eq` reads
`γ e = (F U^†) ((k_A, e.1), (k_B, e.2)) (k_A, k_B)`, so `r` and `c` are the two
displayed index functions and `M = F U^†`; for the projective branch,
`NLQCLean.frozen_pvm_witness_eq` reads
`ω i e = (F *ᵥ pvmColumn M i) ((i, e.1), (i, e.2))`, and since
`pvmColumn M i = fun k => M k i` this is the entry
`(F * M) ((i, e.1), (i, e.2)) i` of a matrix product.  No separate `mulVec`
rule is therefore needed. -/
noncomputable def sliceCLM (r : ε → m) (c : ε → n) : Matrix m n 𝕜 →L[ℝ] (ε → 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun M e => M (r e) (c e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun M => by
      rw [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg M)).2 fun e => frobNorm_entry_le M _ _)

omit [DecidableEq m] [DecidableEq n] in
@[simp]
theorem sliceCLM_apply (r : ε → m) (c : ε → n) (M : Matrix m n 𝕜) (e : ε) :
    sliceCLM (𝕜 := 𝕜) r c M e = M (r e) (c e) := rfl

omit [DecidableEq m] [DecidableEq n] in
/-- Differentiating a family of entries of a differentiable matrix family. -/
theorem HasDerivAt.matrixSlice {f : ℝ → Matrix m n 𝕜} {f' : Matrix m n 𝕜} {t : ℝ}
    (h : HasDerivAt f f' t) (r : ε → m) (c : ε → n) :
    HasDerivAt (fun s => fun e => f s (r e) (c e)) (fun e => f' (r e) (c e)) t := by
  have h2 := (sliceCLM (𝕜 := 𝕜) r c).hasFDerivAt.comp_hasDerivAt t h
  simp only [Function.comp_def] at h2
  exact h2

end Entries

section LinearMaps

/-- Any linear map out of a finite-dimensional real normed space is
differentiable, with itself as derivative.

This is what makes `η ↦ J_η` (`NLQCLean.insertResource_add`,
`NLQCLean.insertResource_smul`) and `ω ↦ C_ω`
(`NLQCLean.flagIsometry_add`, `NLQCLean.flagIsometry_smul`) differentiable in
the vector data, with no norm estimate to prove. -/
theorem HasDerivAt.ofLinearMap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) {f : ℝ → E} {f' : E} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => L (f s)) (L f') t := by
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def, LinearMap.coe_toContinuousLinearMap] using h2

end LinearMaps

section UnitFamily

variable {ε : Type*} [Fintype ε]

/-- Coordinates of a differentiable family of vectors are differentiable. -/
theorem HasDerivAt.piApply {η : ℝ → ε → ℂ} {η' : ε → ℂ} {t : ℝ}
    (h : HasDerivAt η η' t) (e : ε) : HasDerivAt (fun s => η s e) (η' e) t := by
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ε => ℂ) e).hasFDerivAt (x := η t)
  have h2 := hproj.comp_hasDerivAt t h
  simp only [Function.comp_def] at h2
  exact h2

/-- **The scalar of eq:input-compression and eq:output-compression is purely
imaginary.**  Differentiating `‖η(t)‖ = 1` gives `⟨η|η̇⟩ + ⟨η̇|η⟩ = 0`, i.e.
`Re⟨η|η̇⟩ = 0` (snapshot L845-852 and L853-860).

The unit-norm hypothesis is only needed *near* `t`, which is what
`thm:finite-orbit` can supply on a smooth piece between breakpoints
(L906-910). -/
theorem sum_star_mul_deriv_re_eq_zero {η : ℝ → ε → ℂ} {η' : ε → ℂ} {t : ℝ}
    (hunit : ∀ᶠ s in nhds t, IsUnitVector (η s)) (h : HasDerivAt η η' t) :
    (∑ e, star (η t e) * η' e).re = 0 := by
  have hcoord : ∀ e, HasDerivAt (fun s => η s e) (η' e) t := fun e => HasDerivAt.piApply h e
  have hG : HasDerivAt (fun s => ∑ e, star (η s e) * η s e)
      (∑ e, (star (η' e) * η t e + star (η t e) * η' e)) t :=
    _root_.HasDerivAt.fun_sum fun e _ => ((hcoord e).star.mul (hcoord e))
  have hconst : HasDerivAt (fun s => ∑ e, star (η s e) * η s e) 0 t := by
    refine (hasDerivAt_const t (1 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hunit] with s hs
    have hcomm : (∑ e, star (η s e) * η s e) = ∑ e, η s e * star (η s e) :=
      Finset.sum_congr rfl fun e _ => mul_comm _ _
    rw [hcomm]
    exact (isUnitVector_iff_sum (η s)).1 hs
  have hzero : (∑ e, (star (η' e) * η t e + star (η t e) * η' e)) = 0 :=
    hG.unique hconst
  rw [Finset.sum_add_distrib] at hzero
  have hstar : (∑ e, star (η' e) * η t e) = star (∑ e, star (η t e) * η' e) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [star_mul, star_star, mul_comm]
  rw [hstar] at hzero
  have hre := congrArg Complex.re hzero
  rw [Complex.add_re, Complex.zero_re] at hre
  have hs : (star (∑ e, star (η t e) * η' e) : ℂ).re = (∑ e, star (η t e) * η' e).re :=
    Complex.conj_re _
  rw [hs] at hre
  linarith

end UnitFamily

end NLQCLean
