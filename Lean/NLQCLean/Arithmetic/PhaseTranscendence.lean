import NLQCLean.Vendor.HermiteLindemann.Basic
import NLQCLean.Invariants.ControlledPhase
import Mathlib.RingTheory.Localization.Integral

/-!
# Transcendence of algebraic controlled-phase angles

The checked Hermite–Lindemann theorem excludes algebraicity of `exp(i θ)`
for every nonzero real algebraic angle. The converse arithmetic implication
from an algebraic cosine uses the explicit quadratic satisfied by the phase
and transitivity of algebraicity. The normalized two-qubit purity formula
then gives the same obstruction for `phasePurityValue`.
-/

namespace NLQCLean

open Polynomial

/-- A nonzero algebraic real angle gives a phase transcendental over the integers. -/
theorem transcendental_exp_angle_int {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) :
    Transcendental ℤ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hθc : IsAlgebraic ℚ (θ : ℂ) := by
    simpa only [Complex.coe_algebraMap] using hθ.algebraMap (A := ℂ)
  have hiθ : IsAlgebraic ℚ ((θ : ℂ) * Complex.I) :=
    hθc.mul (Complex.isIntegral_I ℚ).isAlgebraic
  apply HermiteLindemann.transcendental_exp
  · exact mul_ne_zero (by exact_mod_cast hθ0) Complex.I_ne_zero
  · exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hiθ

/-- The same phase is transcendental over the rationals. -/
theorem transcendental_exp_angle {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) :
    Transcendental ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  intro hphase
  exact transcendental_exp_angle_int hθ0 hθ
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hphase)

/-- Integer-polynomial algebraicity of the angle is an equivalent input. -/
theorem transcendental_exp_angle_of_isAlgebraic_int {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℤ θ) :
    Transcendental ℚ (Complex.exp ((θ : ℂ) * Complex.I)) :=
  transcendental_exp_angle hθ0 ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp hθ)

/-- The phase satisfies the explicit monic quadratic with cosine coefficient. -/
theorem exp_angle_quadratic (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ 2 -
      2 * (Real.cos θ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + 1 = 0 := by
  have hsum : Complex.exp ((θ : ℂ) * Complex.I) +
      (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = 2 * (Real.cos θ : ℂ) := by
    rw [← Complex.exp_neg,
      show -((θ : ℂ) * Complex.I) = -(θ : ℂ) * Complex.I by ring,
      ← Complex.two_cos, ← Complex.ofReal_cos]
  have hmul := congrArg (fun z : ℂ => z * Complex.exp ((θ : ℂ) * Complex.I)) hsum
  rw [add_mul, inv_mul_cancel₀ (Complex.exp_ne_zero _)] at hmul
  linear_combination hmul

/-- Algebraicity of the cosine implies algebraicity of the phase, by the
quadratic equation and transitivity through the algebraic closure in `ℂ`. -/
theorem isAlgebraic_exp_angle_of_cos {θ : ℝ} (hcos : IsAlgebraic ℚ (Real.cos θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hcosc : IsAlgebraic ℚ (Real.cos θ : ℂ) := by
    simpa only [Complex.coe_algebraMap] using hcos.algebraMap (A := ℂ)
  let c : Subalgebra.algebraicClosure ℚ ℂ := ⟨(Real.cos θ : ℂ), hcosc⟩
  let p : Polynomial (Subalgebra.algebraicClosure ℚ ℂ) := X ^ 2 - C (2 * c) * X + 1
  have hp : p ≠ 0 := by
    intro hp0
    have hcoeff := congrArg (fun q : Polynomial (Subalgebra.algebraicClosure ℚ ℂ) =>
      q.coeff 2) hp0
    simp [p, Polynomial.coeff_one] at hcoeff
  have hroot : aeval (Complex.exp ((θ : ℂ) * Complex.I)) p = 0 := by
    have htwo : ((2 : Subalgebra.algebraicClosure ℚ ℂ) : ℂ) = 2 := rfl
    simpa [p, Subalgebra.algebraMap_eq, c, htwo] using exp_angle_quadratic θ
  have hphase : IsAlgebraic (Subalgebra.algebraicClosure ℚ ℂ)
      (Complex.exp ((θ : ℂ) * Complex.I)) := ⟨p, hp, hroot⟩
  exact hphase.restrictScalars ℚ

/-- The cosine-to-phase implication also holds for integer polynomials. -/
theorem isAlgebraic_exp_angle_int_of_cos {θ : ℝ} (hcos : IsAlgebraic ℤ (Real.cos θ)) :
    IsAlgebraic ℤ (Complex.exp ((θ : ℂ) * Complex.I)) :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr
    (isAlgebraic_exp_angle_of_cos ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp hcos))

/-- Every nonzero real algebraic angle has transcendental cosine. -/
theorem transcendental_cos_of_algebraic {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) : Transcendental ℚ (Real.cos θ) := by
  intro hcos
  exact transcendental_exp_angle hθ0 hθ (isAlgebraic_exp_angle_of_cos hcos)

/-- The cosine is also transcendental over the integers. -/
theorem transcendental_cos_int_of_algebraic {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) : Transcendental ℤ (Real.cos θ) := by
  intro hcos
  exact transcendental_cos_of_algebraic hθ0 hθ
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp hcos)

/-- Recovering the cosine from normalized controlled-phase purity preserves
algebraicity over the rationals. -/
theorem isAlgebraic_cos_of_phasePurityValue {θ : ℝ}
    (hpurity : IsAlgebraic ℚ (phasePurityValue θ)) : IsAlgebraic ℚ (Real.cos θ) := by
  have hcos : Real.cos θ = 4 * phasePurityValue θ - 3 := by
    unfold phasePurityValue
    ring
  rw [hcos]
  exact ((isAlgebraic_natCast (R := ℚ) (A := ℝ) 4).mul hpurity).sub
    (isAlgebraic_natCast (R := ℚ) (A := ℝ) 3)

/-- Algebraic controlled-phase purity forces an algebraic exponential phase. -/
theorem isAlgebraic_exp_angle_of_phasePurityValue {θ : ℝ}
    (hpurity : IsAlgebraic ℚ (phasePurityValue θ)) :
    IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) :=
  isAlgebraic_exp_angle_of_cos (isAlgebraic_cos_of_phasePurityValue hpurity)

/-- Nonzero real algebraic angles have transcendental normalized purity. -/
theorem transcendental_phasePurityValue {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) : Transcendental ℚ (phasePurityValue θ) := by
  intro hpurity
  exact transcendental_cos_of_algebraic hθ0 hθ
    (isAlgebraic_cos_of_phasePurityValue hpurity)

/-- The normalized purity is also transcendental over the integers. -/
theorem transcendental_phasePurityValue_int {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) : Transcendental ℤ (phasePurityValue θ) := by
  intro hpurity
  exact transcendental_phasePurityValue hθ0 hθ
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp hpurity)

/-- The actual normalized two-qubit matrix purity has the same transcendence. -/
theorem transcendental_purity_controlledPhase {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) :
    Transcendental ℚ (purity (1 / 16) (controlledPhase θ)) := by
  rw [purity_controlledPhase]
  exact transcendental_phasePurityValue hθ0 hθ

theorem transcendental_exp_I : Transcendental ℚ (Complex.exp Complex.I) := by
  simpa using transcendental_exp_angle (θ := 1) one_ne_zero isAlgebraic_one

theorem transcendental_exp_I_int : Transcendental ℤ (Complex.exp Complex.I) := by
  simpa using transcendental_exp_angle_int (θ := 1) one_ne_zero isAlgebraic_one

theorem transcendental_cos_one : Transcendental ℚ (Real.cos 1) :=
  transcendental_cos_of_algebraic one_ne_zero isAlgebraic_one

theorem transcendental_cos_one_int : Transcendental ℤ (Real.cos 1) :=
  transcendental_cos_int_of_algebraic one_ne_zero isAlgebraic_one

theorem transcendental_phasePurityValue_one : Transcendental ℚ (phasePurityValue 1) :=
  transcendental_phasePurityValue one_ne_zero isAlgebraic_one

theorem transcendental_purity_controlledPhase_one :
    Transcendental ℚ (purity (1 / 16) (controlledPhase 1)) :=
  transcendental_purity_controlledPhase one_ne_zero isAlgebraic_one

end NLQCLean
