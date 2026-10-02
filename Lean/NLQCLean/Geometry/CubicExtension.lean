/-
Cubic polynomial extensions of the isometry and sphere constraints.
-/
import NLQCLean.LinearAlgebra.RealCoordinates
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Cubic extensions of the constraints

The qualitative Sard step needs a **globally defined real polynomial** map
that is the identity on the constraint set `C` and whose derivative, at points
of `C`, lands in the linearized constraint space for *every* ambient
direction. The construction in `paper/sard-qualitative-proof.md` uses one
factor per block:

  `Q_St(V) = (3V - V V† V)/2`,   `Q_sph(z) = ((3 - ‖z‖²)/2) z`.

This module defines both, proves they fix constrained blocks, computes their
derivatives along an arbitrary straight line, and proves that the derivative
satisfies the corresponding linearized constraint for **every** ambient
velocity — not merely for velocities tangent to `C`.

## What is deliberately not claimed

`Q` is **not** a retraction: no claim is made that it maps a neighborhood of
`C` into `C`. Only agreement on `C` and the first derivative at `C`
are used. The qualitative argument also does not need orthogonal-projection
or norm-contraction properties for these derivatives.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section Stiefel

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Cubic Stiefel extension** `Q_St(V) = (3V - V V† V)/2`. -/
noncomputable def cubicStiefel (V : Matrix m n ℂ) : Matrix m n ℂ :=
  (3 / 2 : ℂ) • V - (2 : ℂ)⁻¹ • (V * Vᴴ * V)

omit [DecidableEq m] in
/-- `Q_St` fixes every isometry: it is the identity on the constraint set. -/
theorem cubicStiefel_of_isometry {V : Matrix m n ℂ} (hV : IsIsometry V) :
    cubicStiefel V = V := by
  have h : V * Vᴴ * V = V := by
    rw [Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  rw [cubicStiefel, h, ← sub_smul]
  norm_num

/-- The derivative of `Q_St` at an isometry, in the direction `Z`:
`DQ_St,V[Z] = Z - ½ V (V†Z + Z†V)`. -/
noncomputable def dCubicStiefel (V Z : Matrix m n ℂ) : Matrix m n ℂ :=
  Z - (2 : ℂ)⁻¹ • (V * (Vᴴ * Z + Zᴴ * V))

omit [DecidableEq m] in
/-- **The derivative formula**, along an arbitrary straight line through
an isometry.  Arbitrary direction `Z`: no constraint on the velocity. -/
theorem hasDerivAt_cubicStiefel {V : Matrix m n ℂ} (hV : IsIsometry V)
    (Z : Matrix m n ℂ) :
    HasDerivAt (fun t : ℝ => cubicStiefel (V + t • Z)) (dCubicStiefel V Z) 0 := by
  have hVV : Vᴴ * V = 1 := hV.conjTranspose_mul_self
  have hline : HasDerivAt (fun t : ℝ => V + t • Z) Z 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Z).const_add V
    simp only [one_smul, id_eq] at h
    exact h
  have hstar : HasDerivAt (fun t : ℝ => (V + t • Z)ᴴ) Zᴴ 0 :=
    HasDerivAt.matrixConjTranspose hline
  have h0 : (fun t : ℝ => V + t • Z) 0 = V := by simp
  have hprod : HasDerivAt (fun t : ℝ => (V + t • Z) * (V + t • Z)ᴴ)
      (V * Zᴴ + Z * Vᴴ) 0 := by
    have := HasDerivAt.matrixMul hline hstar
    simpa [h0] using this
  have hcube : HasDerivAt (fun t : ℝ => (V + t • Z) * (V + t • Z)ᴴ * (V + t • Z))
      ((V * Vᴴ) * Z + (V * Zᴴ + Z * Vᴴ) * V) 0 := by
    have := HasDerivAt.matrixMul hprod hline
    simpa [h0] using this
  have halg : (3 / 2 : ℂ) • Z
      - (2 : ℂ)⁻¹ • ((V * Vᴴ) * Z + (V * Zᴴ + Z * Vᴴ) * V)
      = dCubicStiefel V Z := by
    have e1 : (V * Vᴴ) * Z = V * (Vᴴ * Z) := Matrix.mul_assoc V Vᴴ Z
    have e2 : (V * Zᴴ + Z * Vᴴ) * V = V * (Zᴴ * V) + Z := by
      rw [Matrix.add_mul, Matrix.mul_assoc V Zᴴ V, Matrix.mul_assoc Z Vᴴ V, hVV,
        Matrix.mul_one]
    rw [dCubicStiefel, e1, e2, Matrix.mul_add]
    rw [show (V * (Vᴴ * Z) + (V * (Zᴴ * V) + Z))
        = (V * (Vᴴ * Z) + V * (Zᴴ * V)) + Z by abel]
    rw [smul_add, ← sub_sub, sub_right_comm, ← sub_smul]
    norm_num
  simp only [cubicStiefel]
  have := (hcube.const_smul ((2 : ℂ)⁻¹))
  have hfin := (hline.const_smul ((3 / 2 : ℂ))).sub this
  rw [halg] at hfin
  exact hfin

omit [DecidableEq m] in
/-- **The linearized isometry constraint holds for every ambient velocity.**
Multiplying by `V†` and taking the adjoint gives the constraint. -/
theorem dCubicStiefel_linearized {V : Matrix m n ℂ} (hV : IsIsometry V)
    (Z : Matrix m n ℂ) :
    Vᴴ * dCubicStiefel V Z + (dCubicStiefel V Z)ᴴ * V = 0 := by
  have hVV : Vᴴ * V = 1 := hV.conjTranspose_mul_self
  have hS : (Vᴴ * Z + Zᴴ * V)ᴴ = Vᴴ * Z + Zᴴ * V := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
    abel
  have hleft : Vᴴ * dCubicStiefel V Z
      = Vᴴ * Z - (2 : ℂ)⁻¹ • (Vᴴ * Z + Zᴴ * V) := by
    rw [dCubicStiefel, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hVV,
      Matrix.one_mul]
  have hright : (dCubicStiefel V Z)ᴴ * V
      = Zᴴ * V - (2 : ℂ)⁻¹ • (Vᴴ * Z + Zᴴ * V) := by
    rw [dCubicStiefel, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, hS, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc, hVV, Matrix.mul_one]
    norm_num
  rw [hleft, hright]
  have hcollect : ∀ S : Matrix n n ℂ,
      Vᴴ * Z - (2 : ℂ)⁻¹ • S + (Zᴴ * V - (2 : ℂ)⁻¹ • S)
        = (Vᴴ * Z + Zᴴ * V) - ((2 : ℂ)⁻¹ • S + (2 : ℂ)⁻¹ • S) := by
    intro S; abel
  rw [hcollect, ← add_smul,
    show ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹) = 1 by norm_num, one_smul, sub_self]

end Stiefel

section Sphere

variable {ε : Type*} [Fintype ε]

/-- The Hermitian inner product of two finite complex vectors, in the same
convention as `NLQCLean.frobInner`: conjugate-linear in the first argument. -/
def vecInner (z w : ε → ℂ) : ℂ := ∑ e, star (z e) * w e

/-- The squared Euclidean norm of a finite complex vector. -/
def sqNorm (z : ε → ℂ) : ℝ := ∑ e, Complex.normSq (z e)

theorem vecInner_self (z : ε → ℂ) : vecInner z z = ((sqNorm z : ℝ) : ℂ) := by
  rw [vecInner, sqNorm, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem sqNorm_of_isUnitVector {z : ε → ℂ} (hz : IsUnitVector z) : sqNorm z = 1 := hz

/-- **Cubic sphere extension** `Q_sph(z) = ((3 - ‖z‖²)/2) z`. -/
noncomputable def cubicSphere (z : ε → ℂ) : ε → ℂ :=
  fun e => (((3 - sqNorm z) / 2 : ℝ)) • z e

/-- `Q_sph` fixes every unit vector. -/
theorem cubicSphere_of_isUnitVector {z : ε → ℂ} (hz : IsUnitVector z) :
    cubicSphere z = z := by
  funext e
  rw [cubicSphere, sqNorm_of_isUnitVector hz]
  norm_num

/-- The derivative of `Q_sph` at a unit vector, in the direction `w`:
`DQ_sph,z[w] = w - z Re⟨z,w⟩`. -/
noncomputable def dCubicSphere (z w : ε → ℂ) : ε → ℂ :=
  fun e => w e - ((vecInner z w).re) • z e

omit [Fintype ε] in
/-- Coordinates of the straight line `t ↦ z + t w`. -/
theorem hasDerivAt_line_apply (z w : ε → ℂ) (e : ε) :
    HasDerivAt (fun t : ℝ => (z + t • w) e) (w e) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (w e)).const_add (z e)
  simp only [one_smul, id_eq] at h
  simpa [Pi.add_apply, Pi.smul_apply] using h

/-- The squared norm has the expected directional derivative `2 Re⟨z,w⟩`. -/
theorem hasDerivAt_sqNorm (z w : ε → ℂ) :
    HasDerivAt (fun t : ℝ => sqNorm (z + t • w)) (2 * (vecInner z w).re) 0 := by
  have hC := _root_.HasDerivAt.fun_sum (u := (Finset.univ : Finset ε))
    (A := fun (e : ε) (t : ℝ) => star ((z + t • w) e) * (z + t • w) e)
    (A' := fun e : ε =>
      star (w e) * (z + (0 : ℝ) • w) e + star ((z + (0 : ℝ) • w) e) * w e)
    (x := (0 : ℝ))
    (fun e _ => ((hasDerivAt_line_apply z w e).star.mul (hasDerivAt_line_apply z w e)))
  simp only [zero_smul, add_zero] at hC
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hC
  simp only [Function.comp_def, Complex.reCLM_apply] at hre
  have hfun : (fun t : ℝ => (∑ e, star ((z + t • w) e) * (z + t • w) e).re)
      = fun t : ℝ => sqNorm (z + t • w) := by
    funext t
    rw [← vecInner, vecInner_self, Complex.ofReal_re]
  have hval : (∑ e, (star (w e) * z e + star (z e) * w e)).re
      = 2 * (vecInner z w).re := by
    rw [Finset.sum_add_distrib, Complex.add_re, ← vecInner, ← vecInner]
    have : vecInner w z = star (vecInner z w) := by
      rw [vecInner, vecInner, star_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [star_mul', star_star]; ring
    rw [this, Complex.star_def, Complex.conj_re]
    ring
  rw [hfun, hval] at hre
  exact hre

/-- **The derivative formula for the sphere block**, along an arbitrary
straight line through a unit vector.  Arbitrary direction `w`. -/
theorem hasDerivAt_cubicSphere {z : ε → ℂ} (hz : IsUnitVector z) (w : ε → ℂ) :
    HasDerivAt (fun t : ℝ => cubicSphere (z + t • w)) (dCubicSphere z w) 0 := by
  rw [hasDerivAt_pi]
  intro e
  have hsq : HasDerivAt (fun t : ℝ => ((3 - sqNorm (z + t • w)) / 2 : ℝ))
      (-((vecInner z w).re)) 0 := by
    have h := ((hasDerivAt_sqNorm z w).const_sub (3 : ℝ)).div_const (2 : ℝ)
    have heq : -(2 * (vecInner z w).re) / 2 = -((vecInner z w).re) := by ring
    rw [heq] at h
    exact h
  have hz0 : (3 - sqNorm (z + (0 : ℝ) • w)) / 2 = 1 := by
    rw [zero_smul, add_zero, sqNorm_of_isUnitVector hz]
    norm_num
  have hprod := (hsq.smul (hasDerivAt_line_apply z w e))
  simp only [hz0] at hprod
  have : (fun t : ℝ => cubicSphere (z + t • w) e)
      = fun t : ℝ => ((3 - sqNorm (z + t • w)) / 2 : ℝ) • (z + t • w) e := rfl
  rw [this]
  convert hprod using 1
  have hd : dCubicSphere z w e = w e - ((vecInner z w).re) • z e := rfl
  rw [hd, zero_smul, add_zero, one_smul, neg_smul, sub_eq_add_neg]

/-- **The linearized sphere constraint holds for every ambient velocity.** -/
theorem dCubicSphere_linearized {z : ε → ℂ} (hz : IsUnitVector z) (w : ε → ℂ) :
    (vecInner z (dCubicSphere z w)).re = 0 := by
  have hself : vecInner z z = 1 := by
    rw [vecInner_self, sqNorm_of_isUnitVector hz, Complex.ofReal_one]
  have hexp : vecInner z (dCubicSphere z w)
      = vecInner z w - (((vecInner z w).re : ℝ) : ℂ) * vecInner z z := by
    simp only [vecInner, dCubicSphere, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_sub, Complex.real_smul]
    ring
  rw [hexp, hself, mul_one, Complex.sub_re, Complex.ofReal_re, sub_self]

end Sphere

section Smoothness

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem cubicSphere_eq_smul {ε : Type*} [Fintype ε] (z : ε → ℂ) :
    cubicSphere z = (((3 - sqNorm z) / 2 : ℝ)) • z := rfl

theorem contDiff_sqNorm {ε : Type*} [Fintype ε] :
    ContDiff ℝ ∞ (sqNorm : (ε → ℂ) → ℝ) := by
  have h : ∀ e : ε, ContDiff ℝ ∞ (fun z : ε → ℂ => Complex.normSq (z e)) := by
    intro e
    refine ContDiff.complexNormSq ?_
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ε => ℂ) e).contDiff
      (n := ∞)
  exact ContDiff.sum fun e _ => h e

theorem contDiff_cubicSphere {ε : Type*} [Fintype ε] :
    ContDiff ℝ ∞ (cubicSphere : (ε → ℂ) → (ε → ℂ)) := by
  have hs : ContDiff ℝ ∞ (fun z : ε → ℂ => ((3 - sqNorm z) / 2 : ℝ)) :=
    (contDiff_const.sub contDiff_sqNorm).div_const 2
  have heq : (cubicSphere : (ε → ℂ) → (ε → ℂ)) =
      fun z => (((3 - sqNorm z) / 2 : ℝ)) • z := by
    funext z
    exact cubicSphere_eq_smul z
  rw [heq]
  exact hs.smul (contDiff_id (𝕜 := ℝ) (E := (ε → ℂ)) (n := ∞))

theorem contDiff_cubicStiefel {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    ContDiff ℝ ∞ (cubicStiefel : Matrix m n ℂ → Matrix m n ℂ) := by
  have hid : ContDiff ℝ ∞ (fun V : Matrix m n ℂ => V) := contDiff_id
  have hH : ContDiff ℝ ∞ (fun V : Matrix m n ℂ => Vᴴ) :=
    ContDiff.matrixConjTranspose hid
  have hVVV : ContDiff ℝ ∞ (fun V : Matrix m n ℂ => V * Vᴴ * V) :=
    ContDiff.matrixMul (ContDiff.matrixMul hid hH) hid
  have heq : (cubicStiefel : Matrix m n ℂ → Matrix m n ℂ) =
      fun V => (3 / 2 : ℂ) • V - (2 : ℂ)⁻¹ • (V * Vᴴ * V) := rfl
  rw [heq]
  exact (hid.const_smul ((3 / 2 : ℂ))).sub (hVVV.const_smul ((2 : ℂ)⁻¹))

end Smoothness

end NLQCLean
