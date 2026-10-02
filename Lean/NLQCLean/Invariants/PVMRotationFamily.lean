import NLQCLean.Invariants.PVMMeanPurity

/-!
# An explicit nonconstant family of ordered product-type PVM bases

Rotate the two basis columns |00⟩ and |11⟩ by real amplitudes
√(1−s), √s and keep every other product column. Each basis matrix is unitary
for 0≤s≤1, its mean reduced purity is 1−(4/D)s(1−s), and every value in
[1−1/D, 1] is attained with 0≤s≤1/2. The condition d≥2 makes the rotated labels distinct.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section GramValues

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gramPurity_diagonal_ofReal (v : ι → ℝ) :
    gramPurity (Matrix.diagonal fun k => (v k : ℂ)) = ∑ k, v k ^ 4 := by
  have hstar : star (fun k => (v k : ℂ)) = fun k => (v k : ℂ) := by
    funext k; simp [Complex.conj_ofReal]
  rw [gramPurity, Matrix.diagonal_conjTranspose, hstar, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (v k : ℂ) * v k * ((v k : ℂ) * v k) = ((v k ^ 4 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_re]

theorem gramPurity_single_one (a b : ι) : gramPurity (Matrix.single a b (1 : ℂ)) = 1 := by
  rw [gramPurity, Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_same, mul_one, Matrix.trace_single_eq_same, Complex.one_re]

end GramValues

section Rotation

variable {d : ℕ}

/-- The first diagonal label `0`. -/
def rotLabel0 (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The second diagonal label `1`. -/
def rotLabel1 (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

theorem rotLabel0_ne_rotLabel1 (hd : 2 ≤ d) : rotLabel0 hd ≠ rotLabel1 hd := by
  simp [rotLabel0, rotLabel1, Fin.ext_iff]

/-- The rotated basis labels `|00⟩` and `|11⟩`. -/
def rotO (hd : 2 ≤ d) : Fin d × Fin d := (rotLabel0 hd, rotLabel0 hd)

/-- See `rotO`. -/
def rotE (hd : 2 ≤ d) : Fin d × Fin d := (rotLabel1 hd, rotLabel1 hd)

theorem rotO_ne_rotE (hd : 2 ≤ d) : rotO hd ≠ rotE hd := by
  simp [rotO, rotE, rotLabel0_ne_rotLabel1 hd]

/-- The amplitude vector `a|00⟩+b|11⟩`. -/
noncomputable def rotVector (hd : 2 ≤ d) (a b : ℝ) : Fin d × Fin d → ℂ :=
  fun p => (if p = rotO hd then (a : ℂ) else 0) + (if p = rotE hd then (b : ℂ) else 0)

/-- Column `q` of the rotated ordered basis. -/
noncomputable def pvmRotationColumn (hd : 2 ≤ d) (s : ℝ) (q : Fin d × Fin d) :
    Fin d × Fin d → ℂ :=
  if q = rotO hd then rotVector hd (Real.sqrt (1 - s)) (Real.sqrt s)
  else if q = rotE hd then rotVector hd (-Real.sqrt s) (Real.sqrt (1 - s))
  else fun p => if p = q then 1 else 0

/-- The rotated ordered basis, as the matrix of its columns. -/
noncomputable def pvmRotationBasis (hd : 2 ≤ d) (s : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => pvmRotationColumn hd s q p

theorem pvmRotationColumn_O (hd : 2 ≤ d) (s : ℝ) :
    pvmRotationColumn hd s (rotO hd) = rotVector hd (Real.sqrt (1 - s)) (Real.sqrt s) :=
  ite_eq_left rfl

theorem pvmRotationColumn_E (hd : 2 ≤ d) (s : ℝ) :
    pvmRotationColumn hd s (rotE hd) = rotVector hd (-Real.sqrt s) (Real.sqrt (1 - s)) := by
  rw [pvmRotationColumn, ite_eq_right (Ne.symm (rotO_ne_rotE hd)), ite_eq_left rfl]

theorem pvmRotationColumn_other (hd : 2 ≤ d) (s : ℝ) {q : Fin d × Fin d}
    (hqO : q ≠ rotO hd) (hqE : q ≠ rotE hd) :
    pvmRotationColumn hd s q = fun p => if p = q then 1 else 0 := by
  rw [pvmRotationColumn, ite_eq_right hqO, ite_eq_right hqE]

theorem star_rotVector (hd : 2 ≤ d) (a b : ℝ) (p : Fin d × Fin d) :
    star (rotVector hd a b p) = rotVector hd a b p := by
  simp only [rotVector, star_add]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem star_pvmRotationColumn (hd : 2 ≤ d) (s : ℝ) (q p : Fin d × Fin d) :
    star (pvmRotationColumn hd s q p) = pvmRotationColumn hd s q p := by
  by_cases hqO : q = rotO hd
  · rw [hqO, pvmRotationColumn_O, star_rotVector]
  · by_cases hqE : q = rotE hd
    · rw [hqE, pvmRotationColumn_E, star_rotVector]
    · rw [pvmRotationColumn_other hd s hqO hqE]
      dsimp only
      split_ifs <;> simp

/-- Inner products of the two-dimensional amplitude vectors. -/
theorem sum_rotVector_mul (hd : 2 ≤ d) (a b a' b' : ℝ) :
    ∑ p, rotVector hd a b p * rotVector hd a' b' p = ((a * a' + b * b' : ℝ) : ℂ) := by
  have hOE := rotO_ne_rotE hd
  simp only [rotVector, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_eq_right hOE,
    ite_eq_right (Ne.symm hOE)]
  push_cast
  ring

theorem sum_rotVector_mul_single (hd : 2 ≤ d) (a b : ℝ) {q : Fin d × Fin d}
    (hqO : q ≠ rotO hd) (hqE : q ≠ rotE hd) :
    ∑ p, rotVector hd a b p * (if p = q then 1 else 0) = 0 := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, rotVector,
    ite_eq_right hqO, ite_eq_right hqE, add_zero]

theorem sum_single_mul_rotVector (hd : 2 ≤ d) (a b : ℝ) {q : Fin d × Fin d}
    (hqO : q ≠ rotO hd) (hqE : q ≠ rotE hd) :
    ∑ p, (if p = q then (1 : ℂ) else 0) * rotVector hd a b p = 0 := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, rotVector,
    ite_eq_right hqO, ite_eq_right hqE, add_zero]

theorem sum_single_mul_single (q q' : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, (if p = q then (1 : ℂ) else 0) * (if p = q' then 1 else 0) =
      if q = q' then 1 else 0 := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Orthonormality of the rotated columns. -/
theorem sum_pvmRotationColumn_mul (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (q q' : Fin d × Fin d) :
    ∑ p, pvmRotationColumn hd s q p * pvmRotationColumn hd s q' p =
      if q = q' then 1 else 0 := by
  have hOE := rotO_ne_rotE hd
  have hc : Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s := Real.mul_self_sqrt (by linarith)
  have hσ : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0
  by_cases hqO : q = rotO hd
  · subst hqO
    rw [pvmRotationColumn_O]
    by_cases hq'O : q' = rotO hd
    · subst hq'O
      rw [pvmRotationColumn_O, sum_rotVector_mul, ite_eq_left rfl, hc, hσ]; push_cast; ring
    · by_cases hq'E : q' = rotE hd
      · subst hq'E
        rw [pvmRotationColumn_E, sum_rotVector_mul, ite_eq_right hOE]; push_cast; ring
      · rw [pvmRotationColumn_other hd s hq'O hq'E, sum_rotVector_mul_single hd _ _ hq'O hq'E,
          ite_eq_right (Ne.symm hq'O)]
  · by_cases hqE : q = rotE hd
    · subst hqE
      rw [pvmRotationColumn_E]
      by_cases hq'O : q' = rotO hd
      · subst hq'O
        rw [pvmRotationColumn_O, sum_rotVector_mul, ite_eq_right (Ne.symm hOE)]; push_cast; ring
      · by_cases hq'E : q' = rotE hd
        · subst hq'E
          rw [pvmRotationColumn_E, sum_rotVector_mul, ite_eq_left rfl, neg_mul_neg, hc, hσ]
          push_cast; ring
        · rw [pvmRotationColumn_other hd s hq'O hq'E, sum_rotVector_mul_single hd _ _ hq'O hq'E,
            ite_eq_right (Ne.symm hq'E)]
    · rw [pvmRotationColumn_other hd s hqO hqE]
      by_cases hq'O : q' = rotO hd
      · subst hq'O
        rw [pvmRotationColumn_O, sum_single_mul_rotVector hd _ _ hqO hqE, ite_eq_right hqO]
      · by_cases hq'E : q' = rotE hd
        · subst hq'E
          rw [pvmRotationColumn_E, sum_single_mul_rotVector hd _ _ hqO hqE, ite_eq_right hqE]
        · rw [pvmRotationColumn_other hd s hq'O hq'E, sum_single_mul_single]

/-- The rotated basis matrix is an isometry, hence unitary, for `0 ≤ s ≤ 1`. -/
theorem isIsometry_pvmRotationBasis (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsIsometry (pvmRotationBasis hd s) := by
  unfold IsIsometry
  ext q q'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pvmRotationBasis, Matrix.of_apply,
    star_pvmRotationColumn, Matrix.one_apply]
  exact sum_pvmRotationColumn_mul hd hs0 hs1 q q'

theorem pvmRotationBasis_mem_unitaryGroup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pvmRotationBasis hd s ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_pvmRotationBasis hd hs0 hs1)

/-- The reshaped rotated column is diagonal. -/
theorem reshape_rotVector (hd : 2 ≤ d) (a b : ℝ) :
    (Matrix.of fun x y => rotVector hd a b (x, y) : Matrix (Fin d) (Fin d) ℂ) =
      Matrix.diagonal fun k => (((if k = rotLabel0 hd then a else 0) +
        (if k = rotLabel1 hd then b else 0) : ℝ) : ℂ) := by
  ext x y
  simp only [Matrix.of_apply, Matrix.diagonal_apply, rotVector, rotO, rotE, Prod.mk.injEq]
  by_cases hxy : x = y
  · subst hxy; split_ifs <;> simp_all
  · rw [ite_eq_right hxy]; split_ifs <;> simp_all

theorem reshape_single (q : Fin d × Fin d) :
    (Matrix.of fun x y => if ((x, y) : Fin d × Fin d) = q then (1 : ℂ) else 0 :
        Matrix (Fin d) (Fin d) ℂ) = Matrix.single q.1 q.2 (1 : ℂ) := by
  obtain ⟨q1, q2⟩ := q
  ext x y
  simp only [Matrix.of_apply, Matrix.single_apply, Prod.mk.injEq, @eq_comm _ x q1,
    @eq_comm _ y q2]

theorem sum_rotation_fourth (hd : 2 ≤ d) (a b : ℝ) :
    ∑ k : Fin d, ((if k = rotLabel0 hd then a else 0) + (if k = rotLabel1 hd then b else 0)) ^ 4 =
      a ^ 4 + b ^ 4 := by
  have h01 := rotLabel0_ne_rotLabel1 hd
  have hk : ∀ k : Fin d,
      ((if k = rotLabel0 hd then a else 0) + (if k = rotLabel1 hd then b else 0)) ^ 4 =
        (if k = rotLabel0 hd then a ^ 4 else 0) + (if k = rotLabel1 hd then b ^ 4 else 0) := by
    intro k
    by_cases h0 : k = rotLabel0 hd
    · subst h0; simp [h01]
    · by_cases h1 : k = rotLabel1 hd
      · subst h1; simp [Ne.symm h01]
      · simp [h0, h1]
  simp only [hk, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem gramPurity_pvmRotationBasis_column (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (q : Fin d × Fin d) :
    gramPurity (pvmColumnMatrix (pvmRotationBasis hd s) q) =
      1 + (if q = rotO hd then ((1 - s) ^ 2 + s ^ 2 - 1) else 0) +
        (if q = rotE hd then ((1 - s) ^ 2 + s ^ 2 - 1) else 0) := by
  have hOE := rotO_ne_rotE hd
  have hc : Real.sqrt (1 - s) ^ 4 = (1 - s) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
  have hσ : Real.sqrt s ^ 4 = s ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hs0]
  have hreshape : pvmColumnMatrix (pvmRotationBasis hd s) q =
      Matrix.of fun x y => pvmRotationColumn hd s q (x, y) := by
    ext x y; rfl
  rw [hreshape]
  by_cases hq : q = rotO hd
  · subst hq
    rw [pvmRotationColumn_O, reshape_rotVector, gramPurity_diagonal_ofReal, sum_rotation_fourth,
      hc, hσ, ite_eq_left rfl, ite_eq_right hOE]
    ring
  · by_cases hqE : q = rotE hd
    · subst hqE
      rw [pvmRotationColumn_E, reshape_rotVector, gramPurity_diagonal_ofReal, sum_rotation_fourth,
        neg_pow, hc, hσ, ite_eq_left rfl, ite_eq_right (Ne.symm hOE)]
      norm_num
      ring
    · rw [pvmRotationColumn_other hd s hq hqE, reshape_single, gramPurity_single_one, ite_eq_right hq,
        ite_eq_right hqE]
      ring

/-- The mean reduced purity of the rotated basis is `1−(4/D)s(1−s)`. -/
theorem pvmMeanPurity_pvmRotationBasis (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ (pvmRotationBasis hd s) =
      1 - 4 / (d : ℝ) ^ 2 * (s * (1 - s)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  rw [pvmMeanPurity]
  simp only [gramPurity_pvmRotationBasis_column hd hs0 hs1, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  field_simp
  ring

/-- Every value in `[1−1/D, 1]` is attained with `0 ≤ s ≤ 1/2`. -/
theorem exists_pvmRotationBasis_purity_eq (hd : 2 ≤ d) {v : ℝ}
    (hlo : 1 - 1 / (d : ℝ) ^ 2 ≤ v) (hhi : v ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧
      pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ (pvmRotationBasis hd s) = v := by
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  set w : ℝ := (1 - v) * (d : ℝ) ^ 2 / 4 with hw
  have hw1 : w ≤ 1 / 4 := by
    have h2 : (1 - v) * (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) ^ 2 * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hd0.le
    rw [one_div, inv_mul_cancel₀ hd0.ne'] at h2
    rw [hw]
    linarith
  set t : ℝ := 1 - 4 * w with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hst : Real.sqrt t ≤ 1 := by
    rw [Real.sqrt_le_one]
    have hv : 0 ≤ 1 - v := by linarith
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    rw [ht]; linarith
  refine ⟨(1 - Real.sqrt t) / 2, by linarith, by linarith [Real.sqrt_nonneg t], ?_⟩
  rw [pvmMeanPurity_pvmRotationBasis hd (by linarith) (by linarith [Real.sqrt_nonneg t])]
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have hprod : (1 - Real.sqrt t) / 2 * (1 - (1 - Real.sqrt t) / 2) = w := by
    have h : (1 - Real.sqrt t) / 2 * (1 - (1 - Real.sqrt t) / 2) =
        (1 - Real.sqrt t ^ 2) / 4 := by ring
    rw [h, hsq, ht]; ring
  rw [hprod, hw]
  field_simp
  ring

end Rotation

end NLQCLean
