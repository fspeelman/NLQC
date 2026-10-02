import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Strict derivatives of polynomial maps and Lagrange multipliers

The map `x ↦ eval x p` on `Fin n → ℝ` is strictly differentiable everywhere,
with derivative `v ↦ Σᵢ (∂ᵢp)(x) vᵢ` given by the formal partial derivatives
`pderiv`. With linearly independent constraint derivatives, Mathlib's
Fritz–John multipliers can be normalized to genuine Lagrange multipliers.
This is roadmap step B1, used by the direct image-volume route.
-/

namespace NLQCLean.PolynomialCalculus

open MvPolynomial

variable {n : ℕ}

/-- The derivative of `x ↦ eval x p` at `x`, built from formal partial derivatives. -/
noncomputable def gradL (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

theorem gradL_apply (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    gradL p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [gradL]

theorem gradL_apply_single (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin n) :
    gradL p x (Pi.single k 1) = eval x (pderiv k p) := by
  classical
  rw [gradL_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [hik]
  · simp

/-- **Strict derivative of polynomial evaluation.** -/
theorem hasStrictFDerivAt_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasStrictFDerivAt (fun y => eval y p) (gradL p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hfun : (fun y : Fin n → ℝ => eval y (C a)) = fun _ => a := by funext y; simp
    rw [hfun]
    refine (hasStrictFDerivAt_const a x).congr_fderiv ?_
    ext v
    simp [gradL]
  | add p q hp hq =>
    have hfun : (fun y : Fin n → ℝ => eval y (p + q)) = fun y => eval y p + eval y q := by
      funext y; simp
    rw [hfun]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp only [gradL_apply, FunLike.coe_add, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hX : HasStrictFDerivAt (fun y : Fin n → ℝ => y j)
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) x :=
      hasStrictFDerivAt_apply j x
    have hfun : (fun y : Fin n → ℝ => eval y (p * X j)) = fun y => eval y p * y j := by
      funext y; simp
    rw [hfun]
    refine (hp.mul hX).congr_fderiv ?_
    have key : ∀ i, eval x (pderiv i (p * X j)) =
        x j * eval x (pderiv i p) + (if i = j then eval x p else 0) := by
      intro i
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = j
      · subst h
        simp only [Pi.single_eq_same, smul_eq_mul, map_add, map_mul, mul_one, eval_X,
          ite_true]
        ring
      · simp [h, Ne.symm h]
    ext v
    rw [gradL_apply]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, gradL_apply, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **Strict derivative of a polynomial map.** -/
theorem hasStrictFDerivAt_eval_pi {k : ℕ} (f : Fin k → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    HasStrictFDerivAt (fun y j => eval y (f j))
      (ContinuousLinearMap.pi fun j => gradL (f j) x) x :=
  hasStrictFDerivAt_pi.mpr fun j => hasStrictFDerivAt_eval (f j) x

/-- **Lagrange multipliers with independent constraints.** If `φ` has a local
extremum at `x₀` on a level set of finitely many constraints with linearly
independent strict derivatives, then `φ'` is a combination of those
derivatives. -/
theorem IsLocalExtrOn.exists_lagrange_of_linearIndependent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι]
    {f : ι → E → ℝ} {f' : ι → StrongDual ℝ E} {φ : E → ℝ} {φ' : StrongDual ℝ E} {x₀ : E}
    (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀)
    (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀)
    (hind : LinearIndependent ℝ f') :
    ∃ μ : ι → ℝ, φ' = ∑ i, μ i • f' i := by
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ'
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hsum
    have hΛ := Fintype.linearIndependent_iff.mp hind Λ hsum
    exact hne (Prod.ext (funext hΛ) h0)
  refine ⟨fun i => -(Λ i / Λ₀), ?_⟩
  ext v
  have hv := congrArg (fun L : StrongDual ℝ E => L v) hsum
  simp only [_root_.zero_apply] at hv
  rw [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    _root_.sum_apply] at hv
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at hv
  rw [_root_.sum_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hsum' : ∑ i, -(Λ i / Λ₀) * f' i v = -(∑ i, Λ i * f' i v) / Λ₀ := by
    rw [div_eq_mul_inv, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum', eq_div_iff hΛ₀]
  linarith

end NLQCLean.PolynomialCalculus
