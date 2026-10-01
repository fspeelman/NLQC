import NLQCLean.LinearAlgebra.TensorOperatorNorm
import NLQCLean.LinearAlgebra.SchmidtOverlap
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Pointwise spectral cutoff of a residual

For any complex matrix `R` and cutoff `c > 0` there are a unitary `U`
and a finite index set `S` of eigen-directions of `RᴴR` with

* `|S| c² ≤ ‖R‖_F²` (few large singular values), and
* `‖R (1 − P)‖_op ≤ c` for the orthogonal projection `P = U diag(1_S) Uᴴ`.

Multiplying by `P` on the right (or left) lands in a real subspace of dimension
`2 · (number of rows or columns) · |S|`. The cutoff is chosen at one point; no smooth choice
or parametrization is claimed.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section Diagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem opNorm_diagonal_le {w : n → ℂ} {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    opNorm (Matrix.diagonal w) ≤ C := by
  change ‖toCLM (Matrix.diagonal w)‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  rw [toCLM_apply]
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 2 ≠ 0)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mulVec_diagonal, norm_mul, mul_pow]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem opNorm_unitary_conj_le {U : Matrix n n ℂ} (hU : IsIsometry U) (hU' : IsIsometry Uᴴ)
    (M : Matrix n n ℂ) : opNorm (U * M * Uᴴ) ≤ opNorm M :=
  (opNorm_mul_le _ _).trans (by
    calc opNorm (U * M) * opNorm Uᴴ ≤ opNorm M * 1 :=
          mul_le_mul (opNorm_isometry_mul_le hU M) hU'.opNorm_le_one (opNorm_nonneg _)
            (opNorm_nonneg _)
      _ = opNorm M := mul_one _)

/-- The orthogonal projection onto the eigen-directions indexed by `S`. -/
noncomputable def cutoffProjection (U : Matrix n n ℂ) (S : Finset n) : Matrix n n ℂ :=
  U * Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * Uᴴ

theorem conjTranspose_cutoffProjection (U : Matrix n n ℂ) (S : Finset n) :
    (cutoffProjection U S)ᴴ = cutoffProjection U S := by
  simp only [cutoffProjection, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  congr 2
  ext i j
  simp only [Matrix.diagonal_apply, Pi.star_apply]
  split_ifs <;> simp

theorem one_sub_cutoffProjection {U : Matrix n n ℂ} (hU' : IsIsometry Uᴴ) (S : Finset n) :
    1 - cutoffProjection U S =
      U * Matrix.diagonal (fun i => if i ∈ S then (0 : ℂ) else 1) * Uᴴ := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [IsIsometry, Matrix.conjTranspose_conjTranspose] using hU'
  have hd : Matrix.diagonal (fun i => if i ∈ S then (0 : ℂ) else 1) =
      1 - Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij; by_cases hi : i ∈ S <;> simp [hi]
    · simp [hij]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU, cutoffProjection]

end Diagonal

/-- spectral cutoff at `c > 0`. -/
theorem exists_spectral_cutoff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (R : Matrix m n ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ (U : Matrix n n ℂ) (S : Finset n), IsIsometry U ∧ IsIsometry Uᴴ ∧
      (S.card : ℝ) * c ^ 2 ≤ ‖R‖ ^ 2 ∧ opNorm (R * (1 - cutoffProjection U S)) ≤ c := by
  let hH := Matrix.isHermitian_conjTranspose_mul_self R
  let Uu := hH.eigenvectorUnitary
  let U : Matrix n n ℂ := Uu
  let ev := hH.eigenvalues
  have hU : IsIsometry U := Unitary.coe_star_mul_self Uu
  have hU' : IsIsometry Uᴴ := by
    simpa only [IsIsometry, Matrix.conjTranspose_conjTranspose, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self Uu
  have hspec : Rᴴ * R = U * Matrix.diagonal (fun i => (ev i : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    simpa [U, ev, Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hev0 : ∀ i, 0 ≤ ev i := fun i => Matrix.eigenvalues_conjTranspose_mul_self_nonneg R i
  let S : Finset n := Finset.univ.filter (fun i => c ^ 2 < ev i)
  refine ⟨U, S, hU, hU', ?_, ?_⟩
  · have htrace : ∑ i, ev i = ‖R‖ ^ 2 := by
      have h := congrArg Complex.re hH.trace_eq_sum_eigenvalues
      have hn := norm_sq_eq_re_trace_mul_conjTranspose Rᴴ
      rw [Matrix.frobenius_norm_conjTranspose, Matrix.conjTranspose_conjTranspose] at hn
      rw [hn, h]
      simp [ev, Complex.re_sum]
    calc (S.card : ℝ) * c ^ 2 = ∑ _i ∈ S, c ^ 2 := by simp [Finset.sum_const]
      _ ≤ ∑ i ∈ S, ev i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑ i, ev i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => hev0 i
      _ = ‖R‖ ^ 2 := htrace
  · set Q := 1 - cutoffProjection U S with hQ
    have hQe : Q = U * Matrix.diagonal (fun i => if i ∈ S then (0 : ℂ) else 1) * Uᴴ :=
      one_sub_cutoffProjection hU' S
    have hQh : Qᴴ = Q := by
      rw [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_cutoffProjection]
    have hgram : (R * Q)ᴴ * (R * Q) =
        U * Matrix.diagonal (fun i => if i ∈ S then (0 : ℂ) else (ev i : ℂ)) * Uᴴ := by
      have hUtU : Uᴴ * U = 1 := hU
      rw [Matrix.conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R Q, hspec, hQe]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUtU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUtU,
        Matrix.one_mul]
      simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      congr 2
      ext i j
      simp only [Matrix.diagonal_apply]
      split_ifs <;> simp_all
    have hbound : opNorm ((R * Q)ᴴ * (R * Q)) ≤ c ^ 2 := by
      rw [hgram]
      refine (opNorm_unitary_conj_le hU hU' _).trans (opNorm_diagonal_le (by positivity) ?_)
      intro i
      by_cases hi : i ∈ S
      · simp [hi]; positivity
      · simp only [hi, if_false, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hev0 i)]
        simpa [S] using hi
    rw [opNorm_adjoint_mul_self] at hbound
    exact (pow_le_pow_iff_left₀ (opNorm_nonneg _) hc.le (by decide : 2 ≠ 0)).mp hbound

section Range

variable {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n]

/-- Real-linear right multiplication. -/
def mulRightReal (B : Matrix n n ℂ) : Matrix k n ℂ →ₗ[ℝ] Matrix k n ℂ where
  toFun M := M * B
  map_add' M N := Matrix.add_mul M N B
  map_smul' c M := Matrix.smul_mul c M B

/-- Real-linear left multiplication. -/
def mulLeftReal (B : Matrix n n ℂ) : Matrix n k ℂ →ₗ[ℝ] Matrix n k ℂ where
  toFun M := B * M
  map_add' M N := Matrix.mul_add B M N
  map_smul' c M := (Matrix.mul_smul B c M)

theorem finrank_range_mulRight_cutoffProjection_le (U : Matrix n n ℂ) (S : Finset n) :
    Module.finrank ℝ (LinearMap.range
      (mulRightReal (k := k) (cutoffProjection U S))) ≤ 2 * Fintype.card k * S.card := by
  classical
  let Φ : Matrix k S ℂ →ₗ[ℝ] Matrix k n ℂ :=
    { toFun := fun Y => (Matrix.of fun i j => if h : j ∈ S then Y i ⟨j, h⟩ else 0) * Uᴴ
      map_add' := fun Y Z => by
        rw [← Matrix.add_mul]; congr 1; ext i j
        simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c Y => by
        rw [RingHom.id_apply, ← Matrix.smul_mul]; congr 1; ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp }
  have hle : LinearMap.range (mulRightReal (k := k) (cutoffProjection U S)) ≤ LinearMap.range Φ := by
    rintro _ ⟨M, rfl⟩
    refine ⟨Matrix.of fun i (j : S) => (M * U) i j, ?_⟩
    change (Matrix.of fun i j => if h : j ∈ S then (M * U) i j else 0) * Uᴴ =
      M * cutoffProjection U S
    rw [cutoffProjection, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_diagonal]
    split_ifs <;> simp
  have hdim : Module.finrank ℝ (Matrix k S ℂ) = 2 * Fintype.card k * S.card := by
    rw [finrank_real_of_complex]
    simp [Module.finrank_matrix, Fintype.card_coe]
    ring
  calc Module.finrank ℝ (LinearMap.range (mulRightReal (k := k) (cutoffProjection U S)))
      ≤ Module.finrank ℝ (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (Matrix k S ℂ) := LinearMap.finrank_range_le Φ
    _ = _ := hdim

theorem finrank_range_mulLeft_cutoffProjection_le (U : Matrix n n ℂ) (S : Finset n) :
    Module.finrank ℝ (LinearMap.range
      (mulLeftReal (k := k) (cutoffProjection U S))) ≤ 2 * Fintype.card k * S.card := by
  classical
  let Φ : Matrix S k ℂ →ₗ[ℝ] Matrix n k ℂ :=
    { toFun := fun Y => U * (Matrix.of fun i j => if h : i ∈ S then Y ⟨i, h⟩ j else 0)
      map_add' := fun Y Z => by
        rw [← Matrix.mul_add]; congr 1; ext i j
        simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c Y => by
        rw [RingHom.id_apply, ← Matrix.mul_smul]; congr 1; ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp }
  have hle : LinearMap.range (mulLeftReal (k := k) (cutoffProjection U S)) ≤ LinearMap.range Φ := by
    rintro _ ⟨M, rfl⟩
    refine ⟨Matrix.of fun (i : S) j => (Uᴴ * M) i j, ?_⟩
    change U * (Matrix.of fun i j => if h : i ∈ S then (Uᴴ * M) i j else 0) =
      cutoffProjection U S * M
    rw [cutoffProjection, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  have hdim : Module.finrank ℝ (Matrix S k ℂ) = 2 * Fintype.card k * S.card := by
    rw [finrank_real_of_complex]
    simp [Module.finrank_matrix, Fintype.card_coe]
    ring
  calc Module.finrank ℝ (LinearMap.range (mulLeftReal (k := k) (cutoffProjection U S)))
      ≤ Module.finrank ℝ (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (Matrix S k ℂ) := LinearMap.finrank_range_le Φ
    _ = _ := hdim

end Range

end NLQCLean
