import NLQCLean.Invariants.PurityEstimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# The full-angle two-qubit controlled phase

The phased corner is `(1,1)`. The existing algebraic `phaseFamily` uses
`(0,0)` and its square root selects the upper semicircle; the two bridges
below record the necessary permutation and conjugation explicitly.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- A phase in the bottom-right computational basis corner. -/
def qubitCornerPhase (z : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun p => if p = (1, 1) then z else 1)

/-- The controlled phase `diag(1,1,1,exp(i theta))`, for every real angle. -/
noncomputable def controlledPhase (θ : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  qubitCornerPhase (Complex.exp ((θ : ℂ) * Complex.I))

theorem normSq_exp_angle (θ : ℝ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  simpa [pow_two] using Real.cos_sq_add_sin_sq θ

/-- The full-angle phase is unitary without a semicircle restriction. -/
theorem qubitCornerPhase_unitary {z : ℂ} (hz : Complex.normSq z = 1) :
    (qubitCornerPhase z)ᴴ * qubitCornerPhase z = 1 ∧
      qubitCornerPhase z * (qubitCornerPhase z)ᴴ = 1 := by
  have hzs : star z * z = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, hz]
    norm_num
  constructor <;> ext p q <;>
    simp only [qubitCornerPhase, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all [mul_comm]

theorem controlledPhase_unitary (θ : ℝ) :
    (controlledPhase θ)ᴴ * controlledPhase θ = 1 ∧
      controlledPhase θ * (controlledPhase θ)ᴴ = 1 :=
  qubitCornerPhase_unitary (normSq_exp_angle θ)

/-- Direct evaluation also applies to arbitrary complex corner entries. -/
theorem purity_qubitCornerPhase (z : ℂ) :
    purity (1 / 16) (qubitCornerPhase z) =
      (7 + 4 * z.re + 4 * Complex.normSq z + Complex.normSq z ^ 2) / 16 := by
  simp [purity, realign, qubitCornerPhase, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The manuscript's full-angle purity formula, with normalization `2^-4`. -/
theorem purity_controlledPhase (θ : ℝ) :
    purity (1 / 16) (controlledPhase θ) = (3 + Real.cos θ) / 4 := by
  rw [controlledPhase, purity_qubitCornerPhase, normSq_exp_angle]
  simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- The square root in `phaseZ` always equals `abs(sin theta)`. -/
theorem phaseZ_cos_eq (θ : ℝ) :
    phaseZ (Real.cos θ) =
      (Real.cos θ : ℂ) + (|Real.sin θ| : ℝ) * Complex.I := by
  rw [phaseZ, ← Real.abs_sin_eq_sqrt_one_sub_cos_sq]

/-- Upper-semicircle identification with the exponential phase. -/
theorem phaseZ_cos_upper {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    phaseZ (Real.cos θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [phaseZ_cos_eq, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ),
    Complex.exp_mul_I]
  simp

/-- On the lower semicircle the exponential is the conjugate of `phaseZ`. -/
theorem phaseZ_cos_lower {θ : ℝ} (hθπ : Real.pi ≤ θ) (hθ2π : θ ≤ 2 * Real.pi) :
    star (phaseZ (Real.cos θ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
  have hs : Real.sin θ ≤ 0 := by
    have h := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ θ - Real.pi by linarith) (show θ - Real.pi ≤ Real.pi by linarith)
    simpa [Real.sin_sub] using h
  rw [phaseZ_cos_eq, abs_of_nonpos hs, Complex.exp_mul_I]
  apply Complex.ext <;> simp

/-- Flip both qubit basis labels to exchange the two phased corners. -/
def qubitCornerFlip : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.swap 0 1)

/-- The basis permutation converts the existing first corner to the last. -/
theorem phaseFamily_cornerFlip (t : ℝ) :
    (phaseFamily 2 t).submatrix qubitCornerFlip qubitCornerFlip = qubitCornerPhase (phaseZ t) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [phaseFamily, cornerProj, basisProj, qubitCornerPhase, qubitCornerFlip,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

theorem controlledPhase_eq_phaseFamily_upper {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    controlledPhase θ =
      (phaseFamily 2 (Real.cos θ)).submatrix qubitCornerFlip qubitCornerFlip := by
  rw [phaseFamily_cornerFlip, phaseZ_cos_upper hθ0 hθπ]
  rfl

theorem controlledPhase_eq_phaseFamily_lower {θ : ℝ}
    (hθπ : Real.pi ≤ θ) (hθ2π : θ ≤ 2 * Real.pi) :
    controlledPhase θ =
      ((phaseFamily 2 (Real.cos θ)).submatrix qubitCornerFlip qubitCornerFlip).map star := by
  rw [phaseFamily_cornerFlip, controlledPhase, ← phaseZ_cos_lower hθπ hθ2π]
  ext p q
  by_cases hpq : p = q <;> by_cases hp : p = (1, 1) <;>
    simp_all [qubitCornerPhase]

/-- The scalar invariant as a function of the angle. -/
noncomputable def phasePurityValue (θ : ℝ) : ℝ := (3 + Real.cos θ) / 4

theorem hasDerivAt_phasePurityValue (θ : ℝ) :
    HasDerivAt phasePurityValue (-Real.sin θ / 4) θ := by
  change HasDerivAt (fun x : ℝ => (3 + Real.cos x) / 4) (-Real.sin θ / 4) θ
  exact ((Real.hasDerivAt_cos θ).const_add 3).div_const 4

/-- A lower derivative bound controls the inverse map on a convex real set. -/
theorem inverse_lipschitz_of_deriv_lower {f : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hf : Differentiable ℝ f) {m : ℝ} (hm : 0 < m)
    (hderiv : ∀ z ∈ S, m ≤ deriv f z) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |x - y| ≤ m⁻¹ * |f x - f y| := by
  have hbound := hS.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn (fun z hz => hderiv z (interior_subset hz))
  rw [inv_mul_eq_div, le_div_iff₀ hm]
  rcases le_total x y with hxy | hyx
  · have h := hbound x hx y hy hxy
    have hn : 0 ≤ f y - f x := (mul_nonneg hm.le (sub_nonneg.mpr hxy)).trans h
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (by linarith : f x - f y ≤ 0)]
    nlinarith
  · have h := hbound y hy x hx hyx
    have hn : 0 ≤ f x - f y := (mul_nonneg hm.le (sub_nonneg.mpr hyx)).trans h
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg hn]
    nlinarith

/-- Every compact interval strictly inside the upper semicircle has inverse
Lipschitz control, with its constant chosen after the interval. -/
theorem exists_phasePurity_inverse_lipschitz_upper {a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ m⁻¹ * |phasePurityValue x - phasePurityValue y| := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hab) Real.continuous_sin.continuousOn
  have hcpos : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hc.1) (hc.2.trans_lt hb)
  refine ⟨Real.sin c / 4, by positivity, ?_⟩
  intro x hx y hy
  have hf : Differentiable ℝ (fun θ => -phasePurityValue θ) :=
    fun θ => (hasDerivAt_phasePurityValue θ).neg.differentiableAt
  have hderiv : ∀ θ ∈ Set.Icc a b, Real.sin c / 4 ≤ deriv (fun θ => -phasePurityValue θ) θ := by
    intro θ hθ
    change Real.sin c / 4 ≤ deriv (-phasePurityValue) θ
    rw [(hasDerivAt_phasePurityValue θ).neg.deriv]
    have h := hmin hθ
    change Real.sin c ≤ Real.sin θ at h
    linarith
  have h := inverse_lipschitz_of_deriv_lower (convex_Icc a b) hf
    (by positivity : 0 < Real.sin c / 4) hderiv hx hy
  simpa only [neg_sub_neg, abs_sub_comm] using h

/-- Every compact interval strictly inside the lower semicircle has inverse
Lipschitz control; the sign of sine is handled separately. -/
theorem exists_phasePurity_inverse_lipschitz_lower {a b : ℝ}
    (hab : a ≤ b) (ha : Real.pi < a) (hb : b < 2 * Real.pi) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ m⁻¹ * |phasePurityValue x - phasePurityValue y| := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hab) Real.continuous_sin.neg.continuousOn
  have hcpos : 0 < -Real.sin c := by
    have h := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < c - Real.pi by linarith [hc.1])
      (show c - Real.pi < Real.pi by linarith [hc.2])
    simpa [Real.sin_sub] using h
  refine ⟨(-Real.sin c) / 4, by positivity, ?_⟩
  intro x hx y hy
  have hf : Differentiable ℝ phasePurityValue :=
    fun θ => (hasDerivAt_phasePurityValue θ).differentiableAt
  apply inverse_lipschitz_of_deriv_lower (convex_Icc a b) hf (by positivity) _ hx hy
  intro θ hθ
  rw [(hasDerivAt_phasePurityValue θ).deriv]
  have h := hmin hθ
  change -Real.sin c ≤ -Real.sin θ at h
  linarith

end NLQCLean
