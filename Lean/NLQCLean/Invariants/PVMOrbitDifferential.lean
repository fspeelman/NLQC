import NLQCLean.Invariants.LocalOrbitDifferential
import NLQCLean.LinearAlgebra.Bipartite
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Differentiating scalar invariants of measurement orbits

Two local skew-Hermitian exponentials on the left and one diagonal
skew-Hermitian exponential on the right give a curve in the measurement orbit
`{(L_A ⊗ L_B) M Δ}`. Its tangent is `(a_A ⊗ 1 + 1 ⊗ a_B) M + M b`. A
differentiable scalar function constant on that orbit has zero derivative in
every such direction.
-/

namespace NLQCLean

attribute [local implicit_reducible] Matrix

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section DiagonalExponential

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of a real multiple of a diagonal skew-Hermitian matrix
is a diagonal phase unitary. -/
theorem matrixExp_smul_mem_phaseUnitaries {b : Matrix n n ℂ} (hb : b ∈ diagSkew n) (t : ℝ) :
    NormedSpace.exp (t • b) ∈ phaseUnitaries n := by
  obtain ⟨hdiag, hskew⟩ := mem_diagSkew_iff.mp hb
  have hbd : b = Matrix.diagonal (fun i => b i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h, hdiag i j h]
  have hre : ∀ i, (b i i).re = 0 := by
    intro i
    have h := congrFun (congrFun hskew i) i
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h2
    linarith
  refine ⟨fun i => NormedSpace.exp ((t : ℂ) * b i i), fun i => ?_, ?_⟩
  · rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    simp [Complex.mul_re, hre i]
  · rw [hbd, show t • Matrix.diagonal (fun i => b i i) =
        Matrix.diagonal (fun i => (t : ℂ) * b i i) by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Complex.real_smul]
      · simp [h],
      Matrix.exp_diagonal, Pi.exp_def]
    simp

end DiagonalExponential

section MeasurementCurve

variable {ιA ιB : Type*}
variable [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- Local exponentials on the left and a diagonal exponential on the right. -/
noncomputable def pvmOrbitCurve (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA : Matrix ιA ιA ℂ) (aB : Matrix ιB ιB ℂ) (b : Matrix (ιA × ιB) (ιA × ιB) ℂ) (t : ℝ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ :=
  (NormedSpace.exp (t • aA) ⊗ₖ NormedSpace.exp (t • aB)) * M * NormedSpace.exp (t • b)

theorem pvmOrbitCurve_zero (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA : Matrix ιA ιA ℂ) (aB : Matrix ιB ιB ℂ) (b : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    pvmOrbitCurve M aA aB b 0 = M := by
  simp only [pvmOrbitCurve, zero_smul, NormedSpace.exp_zero, Matrix.one_kronecker_one,
    Matrix.one_mul, Matrix.mul_one]

theorem pvmOrbitCurve_mem (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    {aA : Matrix ιA ιA ℂ} {aB : Matrix ιB ιB ℂ} {b : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (haA : aAᴴ = -aA) (haB : aBᴴ = -aB) (hb : b ∈ diagSkew (ιA × ιB)) (t : ℝ) :
    pvmOrbitCurve M aA aB b t ∈ pvmBasisOrbit ιA ιB M :=
  ⟨_, ⟨_, matrixExp_smul_mem_unitary haA t, _, matrixExp_smul_mem_unitary haB t, rfl⟩,
    _, matrixExp_smul_mem_phaseUnitaries hb t, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_pvmOrbitCurve_zero (M : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (aA : Matrix ιA ιA ℂ) (aB : Matrix ιB ιB ℂ) (b : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    HasDerivAt (pvmOrbitCurve M aA aB b)
      ((aA ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ aB) * M + M * b) 0 := by
  unfold pvmOrbitCurve
  have hL := HasDerivAt.matrixKronecker
    (hasDerivAt_matrixExp_smul_zero aA) (hasDerivAt_matrixExp_smul_zero aB)
  have h := HasDerivAt.matrixMul
    (HasDerivAt.matrixMul hL (hasDerivAt_const (0 : ℝ) M)) (hasDerivAt_matrixExp_smul_zero b)
  simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_kronecker_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_zero, add_zero, add_comm] using h

/-- A differentiable scalar invariant of measurement orbits annihilates every
left-local, right-diagonal skew direction. -/
theorem fderiv_eq_zero_of_pvmMotion (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hdiff : DifferentiableAt ℝ f M)
    (hinv : ∀ N ∈ pvmBasisOrbit ιA ιB M, f N = f M)
    {aA : Matrix ιA ιA ℂ} {aB : Matrix ιB ιB ℂ} (haA : aAᴴ = -aA) (haB : aBᴴ = -aB)
    {b : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hb : b ∈ diagSkew (ιA × ιB)) :
    fderiv ℝ f M ((aA ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ aB) * M + M * b) =
      0 := by
  let q := pvmOrbitCurve M aA aB b
  have hq := hasDerivAt_pvmOrbitCurve_zero M aA aB b
  have hf : HasFDerivAt f (fderiv ℝ f M) (q 0) := by
    rw [show q 0 = M from pvmOrbitCurve_zero M aA aB b]
    exact hdiff.hasFDerivAt
  have hcomp := hf.comp_hasDerivAt 0 hq
  have hconst : HasDerivAt (fun t : ℝ => f (q t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f M)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hinv _ (pvmOrbitCurve_mem M haA haB hb t))
  exact hcomp.unique hconst

end MeasurementCurve

end NLQCLean
