import NLQCLean.Approx.WitnessDifferentialBounds
import NLQCLean.Approx.ChoiProjection

/-!
# Frobenius tensor-insertion bounds

For a unit resource vector `η` and an isometry `V`,

  `‖(X ⊗ V) J_η‖_F ≤ √(dim b) ‖X‖_F` and `‖(V ⊗ X) J_η‖_F ≤ √(dim a) ‖X‖_F`,

where `J_η = insertResource a b η`. This is the Frobenius form of
`‖(Ẋ ⊗ V) J_η‖_F² = dim · Tr[ẊᴴẊ (I ⊗ ρ)] ≤ dim ‖Ẋ‖_F²`; a coarse operator-to-Frobenius
conversion would lose the factor needed downstream.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

theorem norm_one_matrix (n : Type*) [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n) := by
  have hs : ‖(1 : Matrix n n ℂ)‖ ^ 2 = (Fintype.card n : ℝ) := by
    have h := frobInner_self_of_isometry (isIsometry_one (n := n) (𝕜 := ℂ))
    rw [frobInner_self_eq_norm_sq] at h
    exact_mod_cast h
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

section Insertion

variable {a b rA rB l : Type*} [Fintype a] [Fintype b] [Fintype rA] [Fintype rB] [Fintype l]
  [DecidableEq a] [DecidableEq b] [DecidableEq rA] [DecidableEq rB] [DecidableEq l]

/-- Reorder the rows of a `(l × rB) × b` matrix as `l × (b × rB)`. -/
def insertionRowEquiv (l b rB : Type*) : l × (b × rB) ≃ (l × rB) × b where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun q := (q.1.1, (q.2, q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype l] [DecidableEq l] in
omit [DecidableEq rA] in
theorem kronecker_one_mul_insertResource (X : Matrix l (a × rA) ℂ) (η : rA × rB → ℂ) :
    (X ⊗ₖ (1 : Matrix (b × rB) (b × rB) ℂ)) * insertResource a b η =
      ((Matrix.of fun (p : l × rB) (i : a) =>
          (X * ((1 : Matrix a a ℂ) ⊗ₖ resourceMatrix η)) p.1 (i, p.2)) ⊗ₖ
        (1 : Matrix b b ℂ)).submatrix (insertionRowEquiv l b rB) (Equiv.refl (a × b)) := by
  ext ⟨l0, j', pb'⟩ ⟨i, j⟩
  simp only [Matrix.submatrix_apply, insertionRowEquiv, Equiv.coe_fn_mk, Equiv.refl_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single (j', pb')]
  · rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, insertResource_apply]
    simp only [Matrix.one_apply_eq, mul_one, resourceMatrix_apply, Matrix.one_apply]
    by_cases h1 : u.1 = i <;> by_cases h2 : j' = j <;> simp [h1, h2]
  · intro t2 _ ht2
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg (Ne.symm ht2), mul_zero, zero_mul]
  · simp

omit [DecidableEq a] [DecidableEq rB] [DecidableEq l] in
theorem norm_of_insertionReindex (Y : Matrix l (a × rB) ℂ) :
    ‖(Matrix.of fun (p : l × rB) (i : a) => Y p.1 (i, p.2))‖ = ‖Y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobNorm_sq, frobNorm_sq]
  simp only [Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Frobenius tensor insertion with an isometric right factor. -/
theorem frobNorm_kronecker_isometry_right_mul_insertResource_le (X : Matrix l (a × rA) ℂ)
    {lB : Type*} [Fintype lB] [DecidableEq lB] {V : Matrix lB (b × rB) ℂ} (hV : IsIsometry V)
    {η : rA × rB → ℂ} (hη : IsUnitVector η) :
    ‖(X ⊗ₖ V) * insertResource a b η‖ ≤ Real.sqrt (Fintype.card b) * ‖X‖ := by
  have hfact : X ⊗ₖ V = ((1 : Matrix l l ℂ) ⊗ₖ V) * (X ⊗ₖ (1 : Matrix (b × rB) (b × rB) ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hfact, Matrix.mul_assoc, (isIsometry_one.kronecker hV).frobNorm_mul_eq,
    kronecker_one_mul_insertResource, norm_submatrix_equiv, frobNorm_kronecker,
    norm_of_insertionReindex, norm_one_matrix, mul_comm]
  have hR : ‖resourceMatrix η‖ = 1 := (isUnitVector_iff_norm_resourceMatrix η).mp hη
  have hY : ‖X * ((1 : Matrix a a ℂ) ⊗ₖ resourceMatrix η)‖ ≤ ‖X‖ :=
    (frobNorm_mul_le' _ _).trans (by
      have h1 := (opNorm_one_kronecker_le (resourceMatrix η) (n := a)).trans
        ((opNorm_le_frobNorm _).trans hR.le)
      simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg X))
  exact mul_le_mul_of_nonneg_left hY (Real.sqrt_nonneg _)

/-- Reorder the rows of an `a × (rA × lB)` matrix as `(a × rA) × lB`. -/
def insertionLeftRowEquiv (a rA lB : Type*) : (a × rA) × lB ≃ a × (rA × lB) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun q := ((q.1, q.2.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq rB] in
theorem one_kronecker_mul_insertResource {lB : Type*} [Fintype lB] [DecidableEq lB]
    (X : Matrix lB (b × rB) ℂ) (η : rA × rB → ℂ) :
    ((1 : Matrix (a × rA) (a × rA) ℂ) ⊗ₖ X) * insertResource a b η =
      ((1 : Matrix a a ℂ) ⊗ₖ (Matrix.of fun (p : rA × lB) (j : b) =>
          (X * ((1 : Matrix b b ℂ) ⊗ₖ resourceMatrix (fun q : rB × rA => η (q.2, q.1)))) p.2
            (j, p.1))).submatrix (insertionLeftRowEquiv a rA lB) (Equiv.refl (a × b)) := by
  ext ⟨⟨i', pa'⟩, m⟩ ⟨i, j⟩
  simp only [Matrix.submatrix_apply, insertionLeftRowEquiv, Equiv.coe_fn_mk, Equiv.refl_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (i', pa'),
    Finset.mul_sum]
  · refine Finset.sum_congr rfl fun t2 _ => ?_
    rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, insertResource_apply]
    simp only [Matrix.one_apply_eq, one_mul, resourceMatrix_apply, Matrix.one_apply]
    by_cases h1 : i' = i <;> by_cases h2 : t2.1 = j <;> simp [h1, h2, mul_comm, mul_left_comm]
  · intro u _ hu
    refine Finset.sum_eq_zero fun t2 _ => ?_
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg (Ne.symm hu), zero_mul, zero_mul]
  · simp

omit [DecidableEq b] [DecidableEq rA] in
theorem norm_of_insertionLeftReindex {lB : Type*} [Fintype lB] [DecidableEq lB] (Y : Matrix lB (b × rA) ℂ) :
    ‖(Matrix.of fun (p : rA × lB) (j : b) => Y p.2 (j, p.1))‖ = ‖Y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobNorm_sq, frobNorm_sq]
  simp only [Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Frobenius tensor insertion with an isometric left factor. -/
theorem frobNorm_kronecker_isometry_left_mul_insertResource_le
    {lA lB : Type*} [Fintype lA] [DecidableEq lA] [Fintype lB] [DecidableEq lB]
    {V : Matrix lA (a × rA) ℂ} (hV : IsIsometry V) (X : Matrix lB (b × rB) ℂ)
    {η : rA × rB → ℂ} (hη : IsUnitVector η) :
    ‖(V ⊗ₖ X) * insertResource a b η‖ ≤ Real.sqrt (Fintype.card a) * ‖X‖ := by
  have hfact : V ⊗ₖ X = (V ⊗ₖ (1 : Matrix lB lB ℂ)) * ((1 : Matrix (a × rA) (a × rA) ℂ) ⊗ₖ X) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hfact, Matrix.mul_assoc, (hV.kronecker isIsometry_one).frobNorm_mul_eq,
    one_kronecker_mul_insertResource, norm_submatrix_equiv, frobNorm_kronecker,
    norm_of_insertionLeftReindex, norm_one_matrix]
  have hη' : IsUnitVector (fun q : rB × rA => η (q.2, q.1)) :=
    (Fintype.sum_equiv (Equiv.prodComm rB rA) _ _ (fun _ => rfl)).trans hη
  have hR : ‖resourceMatrix (fun q : rB × rA => η (q.2, q.1))‖ = 1 :=
    (isUnitVector_iff_norm_resourceMatrix _).mp hη'
  have hY : ‖X * ((1 : Matrix b b ℂ) ⊗ₖ resourceMatrix (fun q : rB × rA => η (q.2, q.1)))‖ ≤
      ‖X‖ :=
    (frobNorm_mul_le' _ _).trans (by
      have h1 := (opNorm_one_kronecker_le (resourceMatrix (fun q : rB × rA => η (q.2, q.1)))
        (n := b)).trans ((opNorm_le_frobNorm _).trans hR.le)
      simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg X))
  exact mul_le_mul_of_nonneg_left hY (Real.sqrt_nonneg _)

omit [DecidableEq rA] [DecidableEq rB] in
theorem norm_insertResource (η : rA × rB → ℂ) :
    ‖insertResource a b η‖ = Real.sqrt (Fintype.card (a × b)) * ‖WithLp.toLp 2 η‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := frobInner_self_eq_norm_sq (insertResource a b η)
  rw [frobInner_eq_trace, insertResource_gram, vecInner_self, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul] at h
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← sqNorm_eq_euclidean_norm_sq]
  have h' := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at h'
  linarith

end Insertion

end NLQCLean
