import NLQCLean.Geometry.HaarPolynomialZero
import NLQCLean.Approx.GeneralizedBellBasis
import NLQCLean.Models.SwapChoi

/-!
# Haar-generic full Schmidt rank

Each exceptional set is the zero set of a squared-modulus determinant
polynomial restricted to the unitary group. SWAP and the concrete generalized
Bell basis supply the nonvanishing witnesses.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Concrete coefficient polynomials for a real-linear matrix map. -/
noncomputable def linearMatrixCoordinatePolynomial
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ) :
    Matrix m m (MvPolynomial ((n × n) × Fin 2) ℂ) := Matrix.of fun i j =>
  complexLinearPolynomial
    ({ toFun := fun x => L ((matrixFrobeniusCoordinates n n).symm x) i j
       map_add' := by intro x y; simp only [map_add]; rfl
       map_smul' := by intro c x; simp only [map_smul]; rfl } :
      EuclideanSpace ℝ ((n × n) × Fin 2) →ₗ[ℝ] ℂ)

omit [DecidableEq n] in
theorem linearMatrixCoordinatePolynomial_eval
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ)
    (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix (linearMatrixCoordinatePolynomial L) =
      L ((matrixFrobeniusCoordinates n n).symm x) := by
  ext i j
  exact complexLinearPolynomial_eval _ x

/-- The squared determinant modulus is a real polynomial. -/
noncomputable def linearDetNormSqPolynomial
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ) : MvPolynomial ((n × n) × Fin 2) ℝ :=
  let p := (linearMatrixCoordinatePolynomial L).det
  complexPartPolynomial Complex.reCLM.toLinearMap
    (p * MvPolynomial.map (starRingEnd ℂ) p)

omit [DecidableEq n] in
theorem linearDetNormSqPolynomial_eval
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ)
    (x : EuclideanSpace ℝ ((n × n) × Fin 2)) :
    MvPolynomial.eval (fun i => x i) (linearDetNormSqPolynomial L) =
      Complex.normSq (L ((matrixFrobeniusCoordinates n n).symm x)).det := by
  unfold linearDetNormSqPolynomial
  rw [complexPartPolynomial_eval, MvPolynomial.eval_mul, eval_map_star_real,
    RingHom.map_det, linearMatrixCoordinatePolynomial_eval]
  change ((L ((matrixFrobeniusCoordinates n n).symm x)).det *
    star (L ((matrixFrobeniusCoordinates n n).symm x)).det).re = _
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- One unitary determinant witness suffices for generic nonsingularity. -/
theorem ae_unitary_det_linear_ne_zero
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ) (W : Matrix.unitaryGroup n ℂ)
    (hW : (L (W : Matrix n n ℂ)).det ≠ 0) :
    ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n, (L (U : Matrix n n ℂ)).det ≠ 0 := by
  have hp : MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n
      (W : Matrix n n ℂ) k) (linearDetNormSqPolynomial L) ≠ 0 := by
    rw [linearDetNormSqPolynomial_eval, LinearIsometryEquiv.symm_apply_apply]
    exact mt Complex.normSq_eq_zero.mp hW
  have hz := unitaryHaar_polynomial_zeroSet_eq_zero (linearDetNormSqPolynomial L) W hp
  have hae : ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n
        (U : Matrix n n ℂ) k) (linearDetNormSqPolynomial L) ≠ 0 := by
    simpa only [ae_iff, not_not] using hz
  filter_upwards [hae] with U hU
  rw [linearDetNormSqPolynomial_eval, LinearIsometryEquiv.symm_apply_apply] at hU
  exact fun h => hU (Complex.normSq_eq_zero.mpr h)

/-- A linear matrix invariant with one nonsingular unitary witness is full rank almost everywhere. -/
theorem ae_unitary_rank_linear_full
    (L : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ) (W : Matrix.unitaryGroup n ℂ)
    (hW : (L (W : Matrix n n ℂ)).det ≠ 0) :
    ∀ᵐ (U : Matrix.unitaryGroup n ℂ) ∂unitaryHaar n,
      (L (U : Matrix n n ℂ)).rank = Fintype.card m := by
  filter_upwards [ae_unitary_det_linear_ne_zero L W hW] with U hU
  exact Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hU))

/-- The operator-Schmidt rank is full for Haar-almost every bipartite unitary. -/
theorem ae_unitary_operatorSchmidtRank_full (d : ℕ) :
    ∀ᵐ (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      (labChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)).rank = d ^ 2 := by
  let W : Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    ⟨swapUnitary (Fin d), Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_swapUnitary (Fin d))⟩
  let L := (realignLM (ι := Fin d)).restrictScalars ℝ
  have hW : (L (W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)).det ≠ 0 := by
    change (labChoiMatrix (swapUnitary (Fin d))).det ≠ 0
    rw [labChoiMatrix_swapUnitary]
    exact (Matrix.UnitaryGroup.det_isUnit W).ne_zero
  have h := ae_unitary_rank_linear_full L W hW
  filter_upwards [h] with U hU
  have he : realign (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) =
      labChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    ext i j
    rfl
  simpa only [L, LinearMap.restrictScalars_apply, realignLM_apply, he,
    Fintype.card_prod, Fintype.card_fin, pow_two] using hU

/-- Extraction and conjugation of one laboratory target column is real-linear. -/
noncomputable def pvmConjugateColumnLinear (d : ℕ) (i : Fin d × Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ where
  toFun M := pvmConjugateColumnMatrix M i
  map_add' M N := by ext a b; simp [pvmConjugateColumnMatrix]
  map_smul' c M := by ext a b; simp [pvmConjugateColumnMatrix]

@[simp] theorem pvmConjugateColumnLinear_apply (d : ℕ) (i : Fin d × Fin d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    pvmConjugateColumnLinear d i M = pvmConjugateColumnMatrix M i := rfl

/-- All columns of a Haar-random ordered orthonormal basis have full laboratory Schmidt rank. -/
theorem ae_pvmColumnSchmidtRank_full (d : ℕ) [NeZero d] :
    ∀ᵐ (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∀ i, (pvmConjugateColumnMatrix (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) i).rank = d := by
  apply ae_all_iff.mpr
  intro i
  let W := generalizedBellUnitary d
  let B := pvmConjugateColumnMatrix (W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) i
  have hdet : B.det ≠ 0 := by
    have hgram := pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d i
    have hdiag : (Matrix.diagonal (fun _ : Fin d => ((Fintype.card (Fin d) : ℝ)⁻¹ : ℂ))).det ≠ 0 := by
      rw [Matrix.det_diagonal]
      apply Finset.prod_ne_zero_iff.mpr
      intro _ _
      norm_cast
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (by simpa only [Fintype.card_fin] using (NeZero.ne d)))
    have hmul : B.det * Bᴴ.det ≠ 0 := by
      rw [← Matrix.det_mul]
      change (pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i *
        (pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i)ᴴ).det ≠ 0
      rw [hgram]
      exact hdiag
    exact (mul_ne_zero_iff.mp hmul).1
  simpa only [pvmConjugateColumnLinear_apply, Fintype.card_fin] using
    ae_unitary_rank_linear_full (pvmConjugateColumnLinear d i) W hdet

end NLQCLean
