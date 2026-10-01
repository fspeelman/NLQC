/-
Bipartite index structure: amplifications, local algebras, partial traces.
-/
import NLQCLean.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Bipartite matrices

The paper's joint space is `H_A ⊗ H_B` with fixed local dimensions
(snapshot L429-430). It is represented by the product index type, so a joint operator is a
`Matrix (ιA × ιB) (ιA × ιB) ℂ` and the tensor product of local operators is
the Kronecker product `X ⊗ₖ Y`.

This module provides:

* the two amplifications `X_A ↦ X_A ⊗ₖ 1` and `X_B ↦ 1 ⊗ₖ X_B` as
  `ℝ`-linear maps (`NLQCLean.ampLeft`, `NLQCLean.ampRight`);
* the local anti-Hermitian Lie algebra `𝔤_{A:B}` of eq:local-lie-algebra
  (snapshot L573-579), as a real submodule (`NLQCLean.localSkew`), together
  with the scalar direction `iℝI ⊆ 𝔤_{A:B}` (L578-579);
* the diagonal anti-Hermitian algebra `𝔱^D` of eq:pvm-velocity
  (snapshot L807-809), as a real submodule (`NLQCLean.diagSkew`);
* the partial traces over either factor (`NLQCLean.ptraceB`,
  `NLQCLean.ptraceA`), which `lem:shared-state-compression` is stated with.

Anti-Hermitian spaces are real, not complex, submodules: multiplying an
anti-Hermitian matrix by `i` gives a Hermitian one.  This is why the
amplifications are bundled over `ℝ` although they are also `ℂ`-linear.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

section SkewHermitian

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The anti-Hermitian (skew-adjoint) matrices as a real submodule. -/
noncomputable def skewHermitian : Submodule ℝ (Matrix n n ℂ) :=
  skewAdjoint.submodule ℝ (Matrix n n ℂ)

variable {n}

omit [Fintype n] [DecidableEq n] in
theorem mem_skewHermitian_iff {X : Matrix n n ℂ} :
    X ∈ skewHermitian n ↔ Xᴴ = -X := skewAdjoint.mem_iff

end SkewHermitian

section Amplification

variable (ιA ιB)

/-- Alice's amplification `X_A ↦ X_A ⊗ₖ 1`. -/
def ampLeft : Matrix ιA ιA ℂ →ₗ[ℝ] Matrix (ιA × ιB) (ιA × ιB) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix ιB ιB ℂ)
  map_add' X Y := Matrix.add_kronecker X Y 1
  map_smul' r X := Matrix.smul_kronecker r X 1

/-- Bob's amplification `X_B ↦ 1 ⊗ₖ X_B`. -/
def ampRight : Matrix ιB ιB ℂ →ₗ[ℝ] Matrix (ιA × ιB) (ιA × ιB) ℂ where
  toFun X := (1 : Matrix ιA ιA ℂ) ⊗ₖ X
  map_add' X Y := Matrix.kronecker_add 1 X Y
  map_smul' r X := Matrix.kronecker_smul r 1 X

variable {ιA ιB}

omit [Fintype ιA] [Fintype ιB] [DecidableEq ιA] in
@[simp] theorem ampLeft_apply (X : Matrix ιA ιA ℂ) :
    ampLeft ιA ιB X = X ⊗ₖ (1 : Matrix ιB ιB ℂ) := rfl

omit [Fintype ιA] [Fintype ιB] [DecidableEq ιB] in
@[simp] theorem ampRight_apply (X : Matrix ιB ιB ℂ) :
    ampRight ιA ιB X = (1 : Matrix ιA ιA ℂ) ⊗ₖ X := rfl

end Amplification

section LocalSkew

variable (ιA ιB)

/-- **eq:local-lie-algebra** (snapshot L573-579): the local anti-Hermitian Lie
algebra `𝔤_{A:B} = {X_A ⊗ I + I ⊗ X_B : X_X† = -X_X}` as a real submodule. -/
noncomputable def localSkew : Submodule ℝ (Matrix (ιA × ιB) (ιA × ιB) ℂ) :=
  (skewHermitian ιA).map (ampLeft ιA ιB) ⊔ (skewHermitian ιB).map (ampRight ιA ιB)

variable {ιA ιB}

/-- Membership in the paper's form. -/
theorem mem_localSkew_iff {Z : Matrix (ιA × ιB) (ιA × ιB) ℂ} :
    Z ∈ localSkew ιA ιB
      ↔ ∃ XA, XAᴴ = -XA ∧ ∃ XB, XBᴴ = -XB
          ∧ Z = XA ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ XB := by
  constructor
  · intro hZ
    rw [localSkew, Submodule.mem_sup] at hZ
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hZ
    obtain ⟨XA, hXA, rfl⟩ := hy₁
    obtain ⟨XB, hXB, rfl⟩ := hy₂
    exact ⟨XA, mem_skewHermitian_iff.mp hXA, XB, mem_skewHermitian_iff.mp hXB, rfl⟩
  · rintro ⟨XA, hXA, XB, hXB, rfl⟩
    rw [localSkew, Submodule.mem_sup]
    exact ⟨XA ⊗ₖ 1, ⟨XA, mem_skewHermitian_iff.mpr hXA, rfl⟩,
      1 ⊗ₖ XB, ⟨XB, mem_skewHermitian_iff.mpr hXB, rfl⟩, rfl⟩

/-- Members of `𝔤_{A:B}` are anti-Hermitian. -/
theorem localSkew_le_skewHermitian :
    localSkew ιA ιB ≤ skewHermitian (ιA × ιB) := by
  intro Z hZ
  obtain ⟨XA, hXA, XB, hXB, rfl⟩ := mem_localSkew_iff.mp hZ
  rw [mem_skewHermitian_iff, Matrix.conjTranspose_add,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.conjTranspose_one, hXA, hXB, neg_add]
  congr 1 <;> ext ⟨a, b⟩ ⟨a', b'⟩ <;> simp [Matrix.kroneckerMap_apply]

/-- The scalar direction: `𝔤_{A:B}` contains `iℝ·I` (snapshot L578-579).
This absorbs the `⟨η|η̇⟩I` and `⟨γ|γ̇⟩I` terms of `prop:exact-velocity`. -/
theorem smul_I_one_mem_localSkew (r : ℝ) :
    (r • Complex.I) • (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈ localSkew ιA ιB := by
  rw [mem_localSkew_iff]
  refine ⟨(r • Complex.I) • 1, ?_, 0, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  · simp
  · rw [Matrix.kronecker_zero, add_zero, Matrix.smul_kronecker, Matrix.one_kronecker_one]

end LocalSkew

section DiagSkew

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The diagonal matrices as a real submodule. -/
def diagonalSubmodule : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | ∀ i j, i ≠ j → X i j = 0}
  add_mem' hX hY i j hij := by simp [hX i j hij, hY i j hij]
  zero_mem' _ _ _ := rfl
  smul_mem' r X hX i j hij := by simp [hX i j hij]

/-- The diagonal anti-Hermitian algebra `𝔱^D` of eq:pvm-velocity
(snapshot L807-809). -/
noncomputable def diagSkew : Submodule ℝ (Matrix n n ℂ) :=
  diagonalSubmodule n ⊓ skewHermitian n

variable {n}

omit [Fintype n] [DecidableEq n] in
theorem mem_diagSkew_iff {X : Matrix n n ℂ} :
    X ∈ diagSkew n ↔ (∀ i j, i ≠ j → X i j = 0) ∧ Xᴴ = -X :=
  Iff.rfl.and mem_skewHermitian_iff

end DiagSkew

section PartialTrace

variable (ιA ιB)

/-- Partial trace over the second (Bob) factor:
`(Tr_B M) a a' = ∑ b, M (a,b) (a',b)`. -/
def ptraceB : Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix ιA ιA ℂ where
  toFun M := Matrix.of fun a a' => ∑ b, M (a, b) (a', b)
  map_add' M N := by ext a a'; simp [Finset.sum_add_distrib]
  map_smul' c M := by ext a a'; simp [Finset.mul_sum]

/-- Partial trace over the first (Alice) factor. -/
def ptraceA : Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix ιB ιB ℂ where
  toFun M := Matrix.of fun b b' => ∑ a, M (a, b) (a, b')
  map_add' M N := by ext b b'; simp [Finset.sum_add_distrib]
  map_smul' c M := by ext b b'; simp [Finset.mul_sum]

variable {ιA ιB}

omit [Fintype ιA] [DecidableEq ιA] [DecidableEq ιB] in
@[simp] theorem ptraceB_apply (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (a a' : ιA) :
    ptraceB ιA ιB M a a' = ∑ b, M (a, b) (a', b) := rfl

omit [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB] in
@[simp] theorem ptraceA_apply (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (b b' : ιB) :
    ptraceA ιA ιB M b b' = ∑ a, M (a, b) (a, b') := rfl

omit [Fintype ιA] [DecidableEq ιA] [DecidableEq ιB] in
/-- `Tr_B (X ⊗ Y) = (Tr Y) • X`. -/
theorem ptraceB_kronecker (X : Matrix ιA ιA ℂ) (Y : Matrix ιB ιB ℂ) :
    ptraceB ιA ιB (X ⊗ₖ Y) = Y.trace • X := by
  ext a a'
  simp [Matrix.trace, Matrix.diag, ← Finset.mul_sum, mul_comm]

omit [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB] in
/-- `Tr_A (X ⊗ Y) = (Tr X) • Y`. -/
theorem ptraceA_kronecker (X : Matrix ιA ιA ℂ) (Y : Matrix ιB ιB ℂ) :
    ptraceA ιA ιB (X ⊗ₖ Y) = X.trace • Y := by
  ext b b'
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.trace, Finset.sum_mul]
  simp [Matrix.diag]

omit [DecidableEq ιA] [DecidableEq ιB] in
/-- The partial trace of the whole is the trace:
`Tr (Tr_B M) = Tr M`. -/
theorem trace_ptraceB (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    (ptraceB ιA ιB M).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag, ← Finset.sum_product', Finset.univ_product_univ]

omit [Fintype ιA] [DecidableEq ιA] [DecidableEq ιB] in
/-- Partial trace commutes with conjugate transpose, so anti-Hermitian
compresses to anti-Hermitian (used by `lem:shared-state-compression` (i),
snapshot L611-613). -/
theorem ptraceB_conjTranspose (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    ptraceB ιA ιB Mᴴ = (ptraceB ιA ιB M)ᴴ := by
  ext a a'
  simp [Matrix.conjTranspose_apply]

end PartialTrace

end NLQCLean
