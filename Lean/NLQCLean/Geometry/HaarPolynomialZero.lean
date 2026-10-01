import NLQCLean.Geometry.PolynomialZeroMeasure
import NLQCLean.Geometry.CriticalNormalImages
import NLQCLean.Geometry.UnitaryCayleyNormal
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Intrinsic polynomial zero sets on the unitary group

Scalar phase averaging first removes the exceptional set of a translated
Cayley chart. This uses Haar invariance, not ambient matrix volume.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- A rational unit phase with an injective real parameter. -/
noncomputable def scalarCayleyPhase (t : ℝ) : ℂ :=
  (1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I)

theorem scalarCayleyPhase_den_ne_zero (t : ℝ) :
    (1 - (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

theorem normSq_scalarCayleyPhase (t : ℝ) : Complex.normSq (scalarCayleyPhase t) = 1 := by
  unfold scalarCayleyPhase
  rw [Complex.normSq_div]
  have hn : Complex.normSq (1 + (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  have hd : Complex.normSq (1 - (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  rw [hn, hd, div_self (by positivity)]

theorem scalarCayleyPhase_injective : Function.Injective scalarCayleyPhase := by
  intro s t h
  have hc := (div_eq_div_iff (scalarCayleyPhase_den_ne_zero s)
    (scalarCayleyPhase_den_ne_zero t)).mp h
  have hi := congrArg Complex.im hc
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im] at hi
  linarith

theorem continuous_scalarCayleyPhase : Continuous scalarCayleyPhase := by
  unfold scalarCayleyPhase
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).div
    (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const))
    scalarCayleyPhase_den_ne_zero

/-- The scalar phase acts by a unitary matrix. -/
noncomputable def scalarCayleyUnitary (n : Type*) [Fintype n] [DecidableEq n]
    (t : ℝ) : Matrix.unitaryGroup n ℂ := by
  refine ⟨Matrix.diagonal (fun _ => scalarCayleyPhase t), Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  have hphase : star (scalarCayleyPhase t) * scalarCayleyPhase t = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, normSq_scalarCayleyPhase]
    norm_num
  change (Matrix.diagonal (fun _ : n => scalarCayleyPhase t))ᴴ *
    Matrix.diagonal (fun _ : n => scalarCayleyPhase t) = 1
  ext i j
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Pi.star_apply, hphase, Matrix.diagonal_apply, Matrix.one_apply]

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem scalarCayleyUnitary_coe (t : ℝ) :
    (scalarCayleyUnitary n t : Matrix n n ℂ) =
      Matrix.diagonal (fun _ => scalarCayleyPhase t) := rfl

/-- The determinant polynomial in a scalar phase has constant term one. -/
noncomputable def shiftedDetPolynomial (M : Matrix n n ℂ) : Polynomial ℂ :=
  Matrix.det ((1 : Matrix n n (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
    M.map (Polynomial.C : ℂ →+* Polynomial ℂ))

theorem shiftedDetPolynomial_eval (M : Matrix n n ℂ) (z : ℂ) :
    (shiftedDetPolynomial M).eval z = Matrix.det (1 + z • M) := by
  unfold shiftedDetPolynomial
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval z
    (((1 : Matrix n n (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
      M.map (Polynomial.C : ℂ →+* Polynomial ℂ)) i j) = (1 + z • M) i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Matrix.one_apply, apply_ite, Polynomial.eval_one,
    Polynomial.eval_zero]

theorem shiftedDetPolynomial_ne_zero (M : Matrix n n ℂ) : shiftedDetPolynomial M ≠ 0 := by
  intro h
  have he := congrArg (fun p : Polynomial ℂ => p.eval 0) h
  rw [shiftedDetPolynomial_eval] at he
  simp at he

/-- Only finitely many real scalar phases make `I + phase(t) M` singular. -/
theorem finite_scalarCayleyPhase_singular (M : Matrix n n ℂ) :
    Set.Finite {t : ℝ | Matrix.det (1 + scalarCayleyPhase t • M) = 0} := by
  have hroot := Polynomial.finite_setOfPred_isRoot (shiftedDetPolynomial_ne_zero M)
  have hfin := hroot.preimage (fun _ _ _ _ h => scalarCayleyPhase_injective h)
  simpa only [Set.preimage_ofPred_eq, Polynomial.IsRoot, shiftedDetPolynomial_eval] using hfin

/-- Almost every unitary is in the inverse domain of the Cayley chart.
Finite scalar-phase fibers and Haar invariance supply the global nullity. -/
theorem ae_unitary_det_one_add_ne_zero :
    ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      Matrix.det (1 + (U : Matrix n n ℂ)) ≠ 0 := by
  have hfib : ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n, ∀ᵐ t : ℝ,
      Matrix.det (1 + scalarCayleyPhase t • (U : Matrix n n ℂ)) ≠ 0 := by
    apply Filter.Eventually.of_forall
    intro U
    have hz := (finite_scalarCayleyPhase_singular (U : Matrix n n ℂ)).measure_zero volume
    simpa only [ae_iff, not_not] using hz
  have hc : Continuous (fun z : ℝ × Matrix.unitaryGroup n ℂ =>
      Matrix.det (1 + scalarCayleyPhase z.1 • (z.2 : Matrix n n ℂ))) :=
    (continuous_const.add
      ((continuous_scalarCayleyPhase.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))).matrix_det
  have hm : MeasurableSet {z : ℝ × Matrix.unitaryGroup n ℂ |
      Matrix.det (1 + scalarCayleyPhase z.1 • (z.2 : Matrix n n ℂ)) ≠ 0} :=
    (isClosed_singleton.preimage hc).isOpen_compl.measurableSet
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hm).mpr hfib).exists
  have hrot : ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      Matrix.det (1 + ((scalarCayleyUnitary n t * U : Matrix.unitaryGroup n ℂ) :
        Matrix n n ℂ)) ≠ 0 := by
    change ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      Matrix.det (1 + Matrix.diagonal (fun _ => scalarCayleyPhase t) *
        (U : Matrix n n ℂ)) ≠ 0
    simpa only [← Matrix.smul_eq_diagonal_mul] using ht
  have hback := (measurePreserving_mul_left (unitaryHaar n)
    (scalarCayleyUnitary n t)⁻¹).quasiMeasurePreserving.ae hrot
  simpa only [mul_inv_cancel_left] using hback

set_option maxHeartbeats 600000 in
/-- The translated Cayley chart at any fixed unitary has a Haar-null complement. -/
theorem ae_unitary_det_one_add_translate_ne_zero (W : Matrix.unitaryGroup n ℂ) :
    ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) ≠ 0 :=
  (measurePreserving_mul_left (unitaryHaar n) W⁻¹).quasiMeasurePreserving.ae
    (p := fun V : Matrix.unitaryGroup n ℂ => Matrix.det (1 + (V : Matrix n n ℂ)) ≠ 0)
    (ae_unitary_det_one_add_ne_zero (n := n))

/-- Polynomial substitution through rational coordinates admits an actual
polynomial numerator and a power of the common denominator. -/
theorem exists_polynomial_clearing_denominator {σ τ : Type*}
    (p : MvPolynomial σ ℝ) (q : MvPolynomial τ ℝ)
    (N : σ → MvPolynomial τ ℝ) :
    ∃ P : MvPolynomial τ ℝ, ∃ e : ℕ, ∀ x : τ → ℝ,
      MvPolynomial.eval x q ≠ 0 →
      MvPolynomial.eval x P = (MvPolynomial.eval x q) ^ e *
        MvPolynomial.eval (fun i => MvPolynomial.eval x (N i) / MvPolynomial.eval x q) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨MvPolynomial.C c, 0, fun x _ => by simp⟩
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨P₁, e₁, h₁⟩ := h₁
    obtain ⟨P₂, e₂, h₂⟩ := h₂
    refine ⟨P₁ * q ^ e₂ + P₂ * q ^ e₁, e₁ + e₂, ?_⟩
    intro x hx
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      h₁ x hx, h₂ x hx, pow_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, e, hp⟩ := hp
    refine ⟨P * N i, e + 1, ?_⟩
    intro x hx
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, hp x hx, pow_succ]
    field_simp [hx]

/-- Polynomial nullity in any finite Euclidean coordinate index type. -/
theorem mvPolynomial_zeroSet_euclidean_volume_eq_zero {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    volume {x : EuclideanSpace ℝ σ | MvPolynomial.eval (fun i => x i) p = 0} = 0 := by
  classical
  let e := Fintype.equivFin σ
  have hp' : MvPolynomial.rename e p ≠ 0 := by
    intro hz
    exact hp ((MvPolynomial.rename_eq_zero_iff_of_injective p e.injective).mp hz)
  have hpres := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have h := hpres.quasiMeasurePreserving.ae
    (ae_mvPolynomial_eval_ne_zero (MvPolynomial.rename e p) hp')
  have hpi : ∀ᵐ x : σ → ℝ, MvPolynomial.eval x p ≠ 0 := by
    filter_upwards [h] with x hx
    rw [MvPolynomial.eval_rename] at hx
    simpa only [Function.comp_def, MeasurableEquiv.piCongrLeft_apply_apply] using hx
  have hE := (PiLp.volume_preserving_ofLp σ).quasiMeasurePreserving.ae hpi
  simpa only [ae_iff, not_not] using hE

/-- Real and imaginary coefficient polynomials of a complex polynomial. -/
noncomputable def complexPartPolynomial {σ : Type*} (L : ℂ →ₗ[ℝ] ℝ)
    (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (L (p.coeff s))

theorem complexPartPolynomial_eval {σ : Type*} (L : ℂ →ₗ[ℝ] ℝ)
    (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (complexPartPolynomial L p) =
      L (MvPolynomial.eval (fun i => (x i : ℂ)) p) := by
  classical
  simp only [complexPartPolynomial, map_sum, MvPolynomial.eval_monomial]
  rw [MvPolynomial.eval_eq]
  simp only [map_sum, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro s _
  have hprod : (∏ i ∈ s.support, (x i : ℂ) ^ s i) =
      ((∏ i ∈ s.support, x i ^ s i : ℝ) : ℂ) := by simp
  rw [hprod, mul_comm (p.coeff s) _, ← Complex.real_smul, map_smul]
  simp only [smul_eq_mul, mul_comm]

/-- A real-linear complex functional has a concrete complex polynomial. -/
noncomputable def complexLinearPolynomial {σ : Type*} [Fintype σ]
    (L : EuclideanSpace ℝ σ →ₗ[ℝ] ℂ) : MvPolynomial σ ℂ :=
  ∑ i, MvPolynomial.C (L (EuclideanSpace.basisFun σ ℝ i)) * MvPolynomial.X i

theorem complexLinearPolynomial_eval {σ : Type*} [Fintype σ]
    (L : EuclideanSpace ℝ σ →ₗ[ℝ] ℂ) (x : EuclideanSpace ℝ σ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (complexLinearPolynomial L) = L x := by
  classical
  simp only [complexLinearPolynomial, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  have h := congrArg L ((EuclideanSpace.basisFun σ ℝ).sum_repr x)
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    Complex.real_smul, mul_comm] using h

/-- The inverse Cayley coordinate on the nonsingular chart domain. -/
noncomputable def inverseMatrixCayley (U : Matrix n n ℂ) : Matrix n n ℂ :=
  (U - 1) * (U + 1)⁻¹

theorem inverseMatrixCayley_mul_one_add (U : Matrix n n ℂ) (hU : IsUnit (U + 1)) :
    inverseMatrixCayley U * (U + 1) = U - 1 := by
  rw [inverseMatrixCayley, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.mul_one]

theorem one_sub_inverseMatrixCayley (U : Matrix n n ℂ) (hU : IsUnit (U + 1)) :
    1 - inverseMatrixCayley U = (2 : ℂ) • (U + 1)⁻¹ := by
  rw [inverseMatrixCayley, two_smul]
  calc
    _ = (U + 1) * (U + 1)⁻¹ - (U - 1) * (U + 1)⁻¹ := by
      rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]
    _ = _ := by noncomm_ring

theorem isUnit_one_sub_inverseMatrixCayley (U : Matrix n n ℂ) (hU : IsUnit (U + 1)) :
    IsUnit (1 - inverseMatrixCayley U) := by
  rw [one_sub_inverseMatrixCayley U hU, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).pow _ |>.mul
    (Matrix.isUnit_nonsing_inv_det_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp hU))

/-- The inverse chart coordinate is skew-Hermitian, with no norm restriction. -/
theorem inverseMatrixCayley_skew (U : Matrix.unitaryGroup n ℂ)
    (hU : IsUnit ((U : Matrix n n ℂ) + 1)) :
    (inverseMatrixCayley (U : Matrix n n ℂ))ᴴ =
      -inverseMatrixCayley (U : Matrix n n ℂ) := by
  let A := inverseMatrixCayley (U : Matrix n n ℂ)
  let B := (U : Matrix n n ℂ) + 1
  have hAB : A * B = (U : Matrix n n ℂ) - 1 := inverseMatrixCayley_mul_one_add _ hU
  have hBstar : IsUnit Bᴴ := isUnit_star.mpr hU
  have hUU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  apply eq_neg_iff_add_eq_zero.mpr
  apply hBstar.mul_left_cancel
  apply hU.mul_right_cancel
  rw [Matrix.mul_zero, Matrix.zero_mul]
  calc
    Bᴴ * (Aᴴ + A) * B = (A * B)ᴴ * B + Bᴴ * (A * B) := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = ((U : Matrix n n ℂ) - 1)ᴴ * B + Bᴴ * ((U : Matrix n n ℂ) - 1) := by rw [hAB]
    _ = 0 := by
      dsimp only [B]
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_sub, hUU, Matrix.one_mul, Matrix.mul_one]
      noncomm_ring

/-- Every unitary in the nonsingular domain is covered by the Cayley chart. -/
theorem matrixCayley_inverseMatrixCayley (U : Matrix n n ℂ)
    (hU : IsUnit (U + 1)) : matrixCayley (inverseMatrixCayley U) = U := by
  have hi := isUnit_one_sub_inverseMatrixCayley U hU
  have hrelation : 1 + inverseMatrixCayley U = U * (1 - inverseMatrixCayley U) := by
    apply hU.mul_right_cancel
    rw [Matrix.add_mul, Matrix.one_mul, inverseMatrixCayley_mul_one_add U hU,
      Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
      inverseMatrixCayley_mul_one_add U hU]
    noncomm_ring
  rw [matrixCayley, hrelation, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hi), Matrix.mul_one]

/-- Concrete polynomials for the skew coordinate of the normal chart. -/
noncomputable def normalSkewPolynomial (n : Type*) [Fintype n] :
    Matrix n n (MvPolynomial ((n × n) × Fin 2) ℂ) := Matrix.of fun i j =>
  complexLinearPolynomial
    ({ toFun := fun x => normalSkewCoordinate n x i j
       map_add' := fun x y => congrArg (fun M : Matrix n n ℂ => M i j)
         ((normalSkewCoordinate n).map_add x y)
       map_smul' := fun c x => congrArg (fun M : Matrix n n ℂ => M i j)
         ((normalSkewCoordinate n).map_smul c x) } :
      EuclideanSpace ℝ ((n × n) × Fin 2) →ₗ[ℝ] ℂ)

theorem normalSkewPolynomial_eval (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix (normalSkewPolynomial n) =
      normalSkewCoordinate n x := by
  ext i j
  exact complexLinearPolynomial_eval _ x

/-- The complex Cayley denominator is a determinant polynomial. -/
noncomputable def cayleyDenominatorPolynomial (n : Type*) [Fintype n] [DecidableEq n] :
    MvPolynomial ((n × n) × Fin 2) ℂ :=
  Matrix.det (1 - normalSkewPolynomial n)

theorem cayleyDenominatorPolynomial_eval (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (cayleyDenominatorPolynomial n) =
      Matrix.det (1 - normalSkewCoordinate n x) := by
  rw [cayleyDenominatorPolynomial, RingHom.map_det, map_sub, map_one,
    normalSkewPolynomial_eval]

/-- Conjugate coefficients evaluate to conjugate values at real coordinates. -/
theorem eval_map_star_real {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.map (starRingEnd ℂ) p) =
      star (MvPolynomial.eval (fun i => (x i : ℂ)) p) := by
  have h := MvPolynomial.hom_eval₂ p (RingHom.id ℂ) (starRingEnd ℂ)
    (fun i => (x i : ℂ))
  simpa only [RingHom.comp_id, MvPolynomial.eval₂_id, Complex.star_def,
    Complex.conj_ofReal, ← MvPolynomial.eval₂_eq_eval_map] using h.symm

/-- The adjugate numerator for a Cayley chart translated by a fixed matrix. -/
noncomputable def rawCayleyNumeratorPolynomial (W : Matrix n n ℂ) :
    Matrix n n (MvPolynomial ((n × n) × Fin 2) ℂ) :=
  (MvPolynomial.C : ℂ →+* MvPolynomial ((n × n) × Fin 2) ℂ).mapMatrix W *
    (1 + normalSkewPolynomial n) * (1 - normalSkewPolynomial n).adjugate

theorem rawCayleyNumeratorPolynomial_eval (W : Matrix n n ℂ)
    (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix (rawCayleyNumeratorPolynomial W) =
      W * (1 + normalSkewCoordinate n x) * (1 - normalSkewCoordinate n x).adjugate := by
  have hW : (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix
      ((MvPolynomial.C : ℂ →+* MvPolynomial ((n × n) × Fin 2) ℂ).mapMatrix W) = W := by
    ext i j
    exact MvPolynomial.eval_C _
  rw [rawCayleyNumeratorPolynomial, map_mul, map_mul, hW, map_add, map_one,
    normalSkewPolynomial_eval, RingHom.map_adjugate, map_sub, map_one,
    normalSkewPolynomial_eval]

/-- The real positive denominator is squared complex modulus. -/
noncomputable def realCayleyDenominatorPolynomial (n : Type*) [Fintype n] [DecidableEq n] :
    MvPolynomial ((n × n) × Fin 2) ℝ :=
  complexPartPolynomial Complex.reCLM.toLinearMap
    (cayleyDenominatorPolynomial n *
      MvPolynomial.map (starRingEnd ℂ) (cayleyDenominatorPolynomial n))

theorem realCayleyDenominatorPolynomial_eval (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    MvPolynomial.eval (fun i => x i) (realCayleyDenominatorPolynomial n) =
      Complex.normSq (Matrix.det (1 - normalSkewCoordinate n x)) := by
  rw [realCayleyDenominatorPolynomial, complexPartPolynomial_eval,
    MvPolynomial.eval_mul, eval_map_star_real, cayleyDenominatorPolynomial_eval]
  change (Matrix.det (1 - normalSkewCoordinate n x) *
    star (Matrix.det (1 - normalSkewCoordinate n x))).re =
      Complex.normSq (Matrix.det (1 - normalSkewCoordinate n x))
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- Rationalized real matrix-entry numerators of the translated Cayley chart. -/
noncomputable def realCayleyNumeratorPolynomial (W : Matrix n n ℂ)
    (k : (n × n) × Fin 2) : MvPolynomial ((n × n) × Fin 2) ℝ :=
  complexPartPolynomial
    (if k.2 = 0 then Complex.reCLM.toLinearMap else Complex.imCLM.toLinearMap)
    (MvPolynomial.map (starRingEnd ℂ) (cayleyDenominatorPolynomial n) *
      rawCayleyNumeratorPolynomial W k.1.1 k.1.2)

theorem realCayleyNumeratorPolynomial_eval (W : Matrix n n ℂ)
    (x : EuclideanSpace ℝ ((n × n) × Fin 2)) (k : (n × n) × Fin 2) :
    MvPolynomial.eval (fun i => x i) (realCayleyNumeratorPolynomial W k) =
      matrixFrobeniusCoordinates n n
        (star (Matrix.det (1 - normalSkewCoordinate n x)) •
          (W * (1 + normalSkewCoordinate n x) * (1 - normalSkewCoordinate n x).adjugate)) k := by
  have hN := congrArg (fun M : Matrix n n ℂ => M k.1.1 k.1.2)
    (rawCayleyNumeratorPolynomial_eval W x)
  unfold realCayleyNumeratorPolynomial
  rw [complexPartPolynomial_eval, MvPolynomial.eval_mul, eval_map_star_real,
    cayleyDenominatorPolynomial_eval]
  change MvPolynomial.eval (fun i => (x i : ℂ))
    (rawCayleyNumeratorPolynomial W k.1.1 k.1.2) =
      (W * (1 + normalSkewCoordinate n x) * (1 - normalSkewCoordinate n x).adjugate)
        k.1.1 k.1.2 at hN
  rw [hN]
  rcases k with ⟨⟨i, j⟩, b⟩
  fin_cases b <;> rfl

set_option maxHeartbeats 800000 in
/-- The concrete real numerators and denominator represent every Cayley entry. -/
theorem translatedCayley_coordinates_eq_div (W : Matrix n n ℂ)
    (x : EuclideanSpace ℝ ((n × n) × Fin 2)) (k : (n × n) × Fin 2) :
    matrixFrobeniusCoordinates n n (W * matrixCayley (normalSkewCoordinate n x)) k =
      MvPolynomial.eval (fun i => x i) (realCayleyNumeratorPolynomial W k) /
        MvPolynomial.eval (fun i => x i) (realCayleyDenominatorPolynomial n) := by
  let A := normalSkewCoordinate n x
  let d := Matrix.det (1 - A)
  let N := star d • (W * (1 + A) * (1 - A).adjugate)
  have he : W * matrixCayley A = (Complex.normSq d)⁻¹ • N := by
    rw [matrixCayley, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.mul_smul,
      Matrix.mul_smul, ← Matrix.mul_assoc, Complex.inv_def]
    ext i j
    simp only [N, d, Matrix.smul_apply, Complex.real_smul, Complex.star_def]
    ring
  rw [realCayleyNumeratorPolynomial_eval, realCayleyDenominatorPolynomial_eval]
  have hc := congrArg (fun M => matrixFrobeniusCoordinates n n M k) he
  rw [map_smul] at hc
  change matrixFrobeniusCoordinates n n (W * matrixCayley A) k =
    (Complex.normSq d)⁻¹ * matrixFrobeniusCoordinates n n N k at hc
  simpa only [A, d, N, div_eq_mul_inv, mul_comm] using hc

/-- Smoothness of the full normal chart on its exact inverse domain. -/
theorem contDiffAt_normalCayleyEuclidean_of_isUnit
    (x : EuclideanSpace ℝ ((n × n) × Fin 2))
    (hx : IsUnit (1 - normalSkewCoordinate n x)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (normalCayleyEuclidean n) x := by
  let C := (matrixFrobeniusCoordinates n n).toContinuousLinearEquiv.toContinuousLinearMap
  have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => matrixCayley (normalSkewCoordinate n z)) x :=
    (contDiffAt_matrixCayley (normalSkewCoordinate n x) hx).comp x
      (normalSkewCoordinate n).contDiff.contDiffAt
  have hh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (1 : Matrix n n ℂ) + normalHermitianCoordinate n z) x :=
    contDiffAt_const.add (normalHermitianCoordinate n).contDiff.contDiffAt
  have hm := ((mulCLM (l := n) (m := n) (n := n) (𝕜 := ℂ)).contDiff.contDiffAt.comp x hc).clm_apply hh
  exact C.contDiff.contDiffAt.comp x hm

/-- A polynomial nonzero at the center of a translated Cayley chart has a
nonzero polynomial numerator on the whole normal-coordinate space. -/
theorem exists_nonzero_translatedCayley_polynomial
    (p : MvPolynomial ((n × n) × Fin 2) ℝ) (W : Matrix n n ℂ)
    (hW : MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n W k) p ≠ 0) :
    ∃ P : MvPolynomial ((n × n) × Fin 2) ℝ, P ≠ 0 ∧
      ∀ x : EuclideanSpace ℝ ((n × n) × Fin 2),
        IsUnit (1 - normalSkewCoordinate n x) →
        MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n
          (W * matrixCayley (normalSkewCoordinate n x)) k) p = 0 →
        MvPolynomial.eval (fun i => x i) P = 0 := by
  obtain ⟨P, e, hP⟩ := exists_polynomial_clearing_denominator p
    (realCayleyDenominatorPolynomial n) (realCayleyNumeratorPolynomial W)
  have hden (x : EuclideanSpace ℝ ((n × n) × Fin 2))
      (hx : IsUnit (1 - normalSkewCoordinate n x)) :
      MvPolynomial.eval (fun i => x i) (realCayleyDenominatorPolynomial n) ≠ 0 := by
    rw [realCayleyDenominatorPolynomial_eval]
    exact mt Complex.normSq_eq_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hx).ne_zero
  have hzero : MvPolynomial.eval (fun i => (0 : EuclideanSpace ℝ ((n × n) × Fin 2)) i)
      (realCayleyDenominatorPolynomial n) = 1 := by
    rw [realCayleyDenominatorPolynomial_eval]
    simp
  have hcoord (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
      (fun k => MvPolynomial.eval (fun i => x i) (realCayleyNumeratorPolynomial W k) /
        MvPolynomial.eval (fun i => x i) (realCayleyDenominatorPolynomial n)) =
      (fun k => matrixFrobeniusCoordinates n n
        (W * matrixCayley (normalSkewCoordinate n x)) k) := by
    funext k
    exact (translatedCayley_coordinates_eq_div W x k).symm
  have hP0 := hP (fun i => (0 : EuclideanSpace ℝ ((n × n) × Fin 2)) i)
    (by rw [hzero]; exact one_ne_zero)
  rw [hcoord 0, hzero, one_pow, one_mul] at hP0
  have hbase : MvPolynomial.eval (fun i => (0 : EuclideanSpace ℝ ((n × n) × Fin 2)) i) P ≠ 0 := by
    rw [hP0]
    simpa [matrixCayley] using hW
  refine ⟨P, fun h => hbase (by simp [h]), ?_⟩
  intro x hx hz
  have he := hP (fun i => x i) (hden x hx)
  rw [hcoord x, hz, mul_zero] at he
  exact he

/-- Intrinsic Haar nullity of a polynomial restriction with one unitary
nonvanishing witness. No ambient-volume assertion about the group is used. -/
theorem unitaryHaar_polynomial_zeroSet_eq_zero
    (p : MvPolynomial ((n × n) × Fin 2) ℝ) (W : Matrix.unitaryGroup n ℂ)
    (hW : MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n
      (W : Matrix n n ℂ) k) p ≠ 0) :
    unitaryHaar n {U : Matrix.unitaryGroup n ℂ |
      MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n (U : Matrix n n ℂ) k) p = 0} = 0 := by
  classical
  obtain ⟨P, hP, hzero⟩ := exists_nonzero_translatedCayley_polynomial p (W : Matrix n n ℂ) hW
  let S : Set (Matrix.unitaryGroup n ℂ) := {U |
    MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n (U : Matrix n n ℂ) k) p = 0 ∧
      Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) ≠ 0}
  let T : Set (EuclideanSpace ℝ ((n × n) × Fin 2)) := {x |
    MvPolynomial.eval (fun i => x i) P = 0 ∧ IsUnit (1 - normalSkewCoordinate n x)}
  let f : EuclideanSpace ℝ ((n × n) × Fin 2) → EuclideanSpace ℝ ((n × n) × Fin 2) :=
    fun x => unitaryLeftEuclidean W (normalCayleyEuclidean n x)
  have hT : volume T = 0 := measure_mono_null (fun _ hx => hx.1)
    (mvPolynomial_zeroSet_euclidean_volume_eq_zero P hP)
  have hdiff : DifferentiableOn ℝ f T := by
    intro x hx
    have hd := (unitaryLeftEuclidean W).toContinuousLinearEquiv.differentiableAt.comp x
      ((contDiffAt_normalCayleyEuclidean_of_isUnit x hx.2).differentiableAt (by simp))
    exact hd.differentiableWithinAt
  have himage : volume (f '' T) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hT
  have hcoords : Continuous (fun U : Matrix.unitaryGroup n ℂ =>
      fun k => matrixFrobeniusCoordinates n n (U : Matrix n n ℂ) k) :=
    (PiLp.continuous_ofLp 2 (fun _ : ((n × n) × Fin 2) => ℝ)).comp
      ((matrixFrobeniusCoordinates n n).continuous.comp continuous_subtype_val)
  have hc : Continuous (fun U : Matrix.unitaryGroup n ℂ =>
      MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n (U : Matrix n n ℂ) k) p) :=
    p.continuous_eval.comp hcoords
  have hdetc : Continuous (fun U : Matrix.unitaryGroup n ℂ =>
      Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ))) :=
    (continuous_const.add (continuous_subtype_val.comp (continuous_const.mul continuous_id))).matrix_det
  have hS : MeasurableSet S :=
    (isClosed_singleton.preimage hc).measurableSet.inter
      (isClosed_singleton.preimage hdetc).isOpen_compl.measurableSet
  have hnull : unitaryHaar n S = 0 := by
    apply unitaryHaar_eq_zero_of_rightNormalImage_subset_null (s := 1 / 4)
      (by norm_num) (by norm_num) hS himage
    rintro y ⟨U, hU, Q, hQ, _, rfl⟩
    let V : Matrix.unitaryGroup n ℂ := W⁻¹ * U
    have hV : IsUnit ((V : Matrix n n ℂ) + 1) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      exact isUnit_iff_ne_zero.mpr (by simpa only [V, add_comm] using hU.2)
    let A : SkewFrobenius n :=
      ⟨inverseMatrixCayley (V : Matrix n n ℂ), inverseMatrixCayley_skew V hV⟩
    let x := adjointSumEuclidean n (WithLp.toLp 2 ((⟨Q, hQ⟩ : HermitianFrobenius n), A))
    have hxA : normalSkewCoordinate n x = (A : Matrix n n ℂ) := by
      change (((adjointSumEuclidean n).symm ((adjointSumEuclidean n)
        (WithLp.toLp 2 ((⟨Q, hQ⟩ : HermitianFrobenius n), A)))).snd : Matrix n n ℂ) = _
      simp only [LinearIsometryEquiv.symm_apply_apply, WithLp.toLp_snd]
    have hxQ : normalHermitianCoordinate n x = Q := by
      change (((adjointSumEuclidean n).symm ((adjointSumEuclidean n)
        (WithLp.toLp 2 ((⟨Q, hQ⟩ : HermitianFrobenius n), A)))).fst : Matrix n n ℂ) = _
      simp only [LinearIsometryEquiv.symm_apply_apply, WithLp.toLp_fst]
    have hxinv : IsUnit (1 - normalSkewCoordinate n x) := by
      rw [hxA]
      exact isUnit_one_sub_inverseMatrixCayley _ hV
    have hxU : (W : Matrix n n ℂ) * matrixCayley (normalSkewCoordinate n x) =
        (U : Matrix n n ℂ) := by
      rw [hxA, matrixCayley_inverseMatrixCayley _ hV]
      change ((W * (W⁻¹ * U) : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) = _
      rw [mul_inv_cancel_left]
    refine ⟨x, ⟨hzero x hxinv (by rw [hxU]; exact hU.1), hxinv⟩, ?_⟩
    dsimp only [f, normalCayleyEuclidean]
    rw [unitaryLeftEuclidean_coordinates, hxQ, ← Matrix.mul_assoc, hxU]
  have hexcept : unitaryHaar n {U : Matrix.unitaryGroup n ℂ |
      Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) = 0} = 0 := by
    simpa only [ae_iff, not_not] using ae_unitary_det_one_add_translate_ne_zero W
  apply le_antisymm _ zero_le
  calc
    _ ≤ unitaryHaar n (S ∪ {U : Matrix.unitaryGroup n ℂ |
        Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) = 0}) := by
      apply measure_mono
      intro U hU
      by_cases hdet : Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) = 0
      · exact Or.inr hdet
      · exact Or.inl ⟨hU, hdet⟩
    _ ≤ unitaryHaar n S + unitaryHaar n {U : Matrix.unitaryGroup n ℂ |
        Matrix.det (1 + ((W⁻¹ * U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) = 0} := measure_union_le _ _
    _ = 0 := by rw [hnull, hexcept, zero_add]

end NLQCLean
