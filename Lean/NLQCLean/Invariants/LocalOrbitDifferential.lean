import NLQCLean.LinearAlgebra.Calculus
import NLQCLean.Models.Targets
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Differentiating scalar invariants of local-unitary orbits

Four local skew-Hermitian matrix exponentials give a curve in the existing
double local-unitary orbit. Its tangent is `b * U + U * a`. A differentiable
ambient scalar function constant on that orbit therefore has zero derivative
in every such direction. The middle matrix need not be unitary.
-/

namespace NLQCLean

attribute [local implicit_reducible] Matrix

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

universe u v

section MatrixExponential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real multiple of a skew-Hermitian matrix exponentiates to a unitary. -/
theorem matrixExp_smul_mem_unitary {X : Matrix ι ι ℂ}
    (hX : Xᴴ = -X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Matrix.unitaryGroup ι ℂ := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  change (t • X)ᴴ = -(t • X)
  simp only [Matrix.conjTranspose_smul, star_trivial, hX, smul_neg]

set_option backward.isDefEq.respectTransparency false in
/-- The local matrix exponential path has its generator as velocity at zero. -/
theorem hasDerivAt_matrixExp_smul_zero (X : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] using
    (hasDerivAt_exp_smul_const X (0 : ℝ))

end MatrixExponential

section LocalCurve

variable {ιA : Type u} {ιB : Type v}
variable [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- Four local exponentials acting on the original target matrix. -/
noncomputable def localUnitaryOrbitCurve
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA bA : Matrix ιA ιA ℂ) (aB bB : Matrix ιB ιB ℂ) (t : ℝ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ :=
  (NormedSpace.exp (t • bA) ⊗ₖ NormedSpace.exp (t • bB)) * U *
    (NormedSpace.exp (t • aA) ⊗ₖ NormedSpace.exp (t • aB))

@[simp] theorem localUnitaryOrbitCurve_zero
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA bA : Matrix ιA ιA ℂ) (aB bB : Matrix ιB ιB ℂ) :
    localUnitaryOrbitCurve U aA bA aB bB 0 = U := by
  simp only [localUnitaryOrbitCurve, zero_smul, NormedSpace.exp_zero,
    Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one]

/-- The exponential curve lies in the actual local double orbit. -/
theorem localUnitaryOrbitCurve_mem
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    {aA bA : Matrix ιA ιA ℂ} {aB bB : Matrix ιB ιB ℂ}
    (haA : aAᴴ = -aA) (haB : aBᴴ = -aB)
    (hbA : bAᴴ = -bA) (hbB : bBᴴ = -bB) (t : ℝ) :
    localUnitaryOrbitCurve U aA bA aB bB t ∈ unitaryDoubleOrbit ιA ιB U := by
  exact ⟨_, ⟨_, matrixExp_smul_mem_unitary hbA t,
      _, matrixExp_smul_mem_unitary hbB t, rfl⟩,
    _, ⟨_, matrixExp_smul_mem_unitary haA t,
      _, matrixExp_smul_mem_unitary haB t, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The four-exponential curve realizes the two local generator directions. -/
theorem hasDerivAt_localUnitaryOrbitCurve_zero
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA bA : Matrix ιA ιA ℂ) (aB bB : Matrix ιB ιB ℂ) :
    HasDerivAt (localUnitaryOrbitCurve U aA bA aB bB)
      ((bA ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ bB) * U +
        U * (aA ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ aB)) 0 := by
  unfold localUnitaryOrbitCurve
  have hL := HasDerivAt.matrixKronecker
    (hasDerivAt_matrixExp_smul_zero bA) (hasDerivAt_matrixExp_smul_zero bB)
  have hR := HasDerivAt.matrixKronecker
    (hasDerivAt_matrixExp_smul_zero aA) (hasDerivAt_matrixExp_smul_zero aB)
  have h := HasDerivAt.matrixMul
    (HasDerivAt.matrixMul hL (hasDerivAt_const (0 : ℝ) U)) hR
  simpa only [zero_smul, NormedSpace.exp_zero,
    Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, add_zero, add_comm] using h

/-- An ambient differentiable scalar invariant annihilates the exact local
generator direction. Invariance is on the existing orbit of the given matrix. -/
theorem fderiv_eq_zero_of_localSkew
    (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    {U : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (hdiff : DifferentiableAt ℝ f U)
    (hinv : ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    {a b : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (ha : a ∈ localSkew ιA ιB) (hb : b ∈ localSkew ιA ιB) :
    fderiv ℝ f U (b * U + U * a) = 0 := by
  obtain ⟨aA, haA, aB, haB, harep⟩ := mem_localSkew_iff.mp ha
  obtain ⟨bA, hbA, bB, hbB, hbrep⟩ := mem_localSkew_iff.mp hb
  let q := localUnitaryOrbitCurve U aA bA aB bB
  have hq : HasDerivAt q (b * U + U * a) 0 := by
    rw [harep, hbrep]
    exact hasDerivAt_localUnitaryOrbitCurve_zero U aA bA aB bB
  have hq0 : q 0 = U := localUnitaryOrbitCurve_zero U aA bA aB bB
  have hf : HasFDerivAt f (fderiv ℝ f U) (q 0) := by
    rw [hq0]
    exact hdiff.hasFDerivAt
  have hcomp := hf.comp_hasDerivAt 0 hq
  have hconst : HasDerivAt (fun t : ℝ => f (q t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f U)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t =>
        hinv _ (localUnitaryOrbitCurve_mem U haA haB hbA hbB t))
  exact hcomp.unique hconst

end LocalCurve

end NLQCLean
