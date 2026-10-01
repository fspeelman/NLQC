import NLQCLean.Geometry.CubicExtension
import NLQCLean.LinearAlgebra.FrobeniusInner

/-!
# The cubic derivatives are real orthogonal projections

The Stiefel and sphere cubic derivatives satisfy the
linearized constraints; here their discarded parts are proved orthogonal
to every allowed velocity, and their Euclidean contraction is proved.
The derivatives are also identified with the full ambient Fréchet derivative.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section General

/-- Orthogonality of the discarded part implies Frobenius contraction. -/
theorem frobNorm_le_of_projection_orthogonal {m n : Type*} [Fintype m] [Fintype n]
    (Z P : Matrix m n ℂ) (h : (frobInner (Z - P) P).re = 0) : ‖P‖ ≤ ‖Z‖ := by
  rw [frobInner_sub_left, Complex.sub_re, frobInner_self_eq_norm_sq, Complex.ofReal_re] at h
  have hc := congrArg Complex.re (frobInner_conj P Z)
  simp only [Complex.star_def, Complex.conj_re] at hc
  have hn := frobNorm_sub_sq Z P
  have hnonneg := sq_nonneg ‖Z - P‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

/-- Hermitian and skew-Hermitian matrices are orthogonal over the reals. -/
theorem frobInner_hermitian_skew_re_eq_zero {n : Type*} [Fintype n]
    (S K : Matrix n n ℂ) (hS : Sᴴ = S) (hK : Kᴴ = -K) :
    (frobInner S K).re = 0 := by
  rw [frobInner_eq_trace, hS]
  have hc : star (Matrix.trace (S * K)) = -Matrix.trace (S * K) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hK, hS,
      Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hr := congrArg Complex.re hc
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  linarith

end General

section Stiefel

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- The discarded part is orthogonal to every linearized isometry velocity. -/
theorem dCubicStiefel_orthogonal (V Z Y : Matrix m n ℂ)
    (hY : Vᴴ * Y + Yᴴ * V = 0) :
    (frobInner (Z - dCubicStiefel V Z) Y).re = 0 := by
  have hS : (Vᴴ * Z + Zᴴ * V)ᴴ = Vᴴ * Z + Zᴴ * V := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    abel
  have hK : (Vᴴ * Y)ᴴ = -(Vᴴ * Y) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact eq_neg_of_add_eq_zero_right hY
  have ho := frobInner_hermitian_skew_re_eq_zero (Vᴴ * Z + Zᴴ * V) (Vᴴ * Y) hS hK
  rw [dCubicStiefel, sub_sub_cancel, frobInner_smul_left, frobInner_mul_left]
  simp [Complex.mul_re, ho]

omit [DecidableEq m] [DecidableEq n] in
/-- The cubic derivative fixes each tangent velocity. -/
theorem dCubicStiefel_of_linearized (V Z : Matrix m n ℂ)
    (hZ : Vᴴ * Z + Zᴴ * V = 0) : dCubicStiefel V Z = Z := by
  simp [dCubicStiefel, hZ]

omit [DecidableEq m] in
/-- The cubic extension's derivative is the real Frobenius orthogonal projection. -/
theorem dCubicStiefel_projection {V : Matrix m n ℂ} (hV : IsIsometry V) (Z : Matrix m n ℂ) :
    Vᴴ * dCubicStiefel V Z + (dCubicStiefel V Z)ᴴ * V = 0 ∧
      (∀ Y, Vᴴ * Y + Yᴴ * V = 0 → (frobInner (Z - dCubicStiefel V Z) Y).re = 0) ∧
      ‖dCubicStiefel V Z‖ ≤ ‖Z‖ := by
  have ht := dCubicStiefel_linearized hV Z
  exact ⟨ht, dCubicStiefel_orthogonal V Z,
    frobNorm_le_of_projection_orthogonal Z _ (dCubicStiefel_orthogonal V Z _ ht)⟩

theorem fderiv_cubicStiefel_apply {V : Matrix m n ℂ} (hV : IsIsometry V) (Z : Matrix m n ℂ) :
    fderiv ℝ cubicStiefel V Z = dCubicStiefel V Z :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_cubicStiefel.differentiable (by simp)).differentiableAt
    (hasDerivAt_cubicStiefel hV Z)

theorem norm_fderiv_cubicStiefel_apply_le {V : Matrix m n ℂ} (hV : IsIsometry V)
    (Z : Matrix m n ℂ) : ‖fderiv ℝ cubicStiefel V Z‖ ≤ ‖Z‖ := by
  rw [fderiv_cubicStiefel_apply hV]
  exact (dCubicStiefel_projection hV Z).2.2

end Stiefel

section Sphere

variable {ε : Type*} [Fintype ε]

/-- The discarded sphere velocity is real-orthogonal to every tangent vector. -/
theorem dCubicSphere_orthogonal (z w y : ε → ℂ) (hy : (vecInner z y).re = 0) :
    (vecInner (w - dCubicSphere z w) y).re = 0 := by
  have heq : vecInner (w - dCubicSphere z w) y =
      ((vecInner z w).re : ℂ) * vecInner z y := by
    simp only [vecInner, dCubicSphere, Pi.sub_apply, sub_sub_cancel,
      Complex.real_smul, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hy]
  ring

theorem dCubicSphere_of_linearized (z w : ε → ℂ) (hw : (vecInner z w).re = 0) :
    dCubicSphere z w = w := by
  ext e
  simp [dCubicSphere, hw]

/-- The vector inner product is the Frobenius inner product of one-column
matrices; this keeps the Euclidean norm distinct from a Pi sup norm. -/
theorem vecInner_eq_frobInner_column (z w : ε → ℂ) :
    vecInner z w = frobInner (fun e (_ : Unit) => z e) (fun e (_ : Unit) => w e) := by
  simp [vecInner, frobInner]

theorem norm_column_eq_euclidean (z : ε → ℂ) :
    ‖Matrix.replicateCol Unit z‖ = ‖WithLp.toLp 2 z‖ :=
  Matrix.frobenius_norm_replicateCol (ι := Unit) z

/-- Orthogonal projection for the sphere, with its Euclidean norm. -/
theorem dCubicSphere_projection {z : ε → ℂ} (hz : IsUnitVector z) (w : ε → ℂ) :
    (vecInner z (dCubicSphere z w)).re = 0 ∧
      (∀ y, (vecInner z y).re = 0 → (vecInner (w - dCubicSphere z w) y).re = 0) ∧
      ‖WithLp.toLp 2 (dCubicSphere z w)‖ ≤ ‖WithLp.toLp 2 w‖ := by
  have ht := dCubicSphere_linearized hz w
  refine ⟨ht, dCubicSphere_orthogonal z w, ?_⟩
  rw [← norm_column_eq_euclidean, ← norm_column_eq_euclidean]
  apply frobNorm_le_of_projection_orthogonal
  exact (vecInner_eq_frobInner_column (w - dCubicSphere z w) (dCubicSphere z w)) ▸
    dCubicSphere_orthogonal z w _ ht

theorem fderiv_cubicSphere_apply {z : ε → ℂ} (hz : IsUnitVector z) (w : ε → ℂ) :
    fderiv ℝ cubicSphere z w = dCubicSphere z w :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_cubicSphere.differentiable (by simp)).differentiableAt
    (hasDerivAt_cubicSphere hz w)

/-- The sphere cubic expressed in Euclidean coordinates. -/
noncomputable def cubicSphereEuclidean (z : EuclideanSpace ℂ ε) : EuclideanSpace ℂ ε :=
  WithLp.toLp 2 (cubicSphere (WithLp.ofLp z))

theorem contDiff_cubicSphereEuclidean :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (cubicSphereEuclidean : EuclideanSpace ℂ ε → EuclideanSpace ℂ ε) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ε => ℂ)
  exact e.symm.contDiff.comp (contDiff_cubicSphere.comp e.contDiff)

theorem fderiv_cubicSphereEuclidean_apply {z : EuclideanSpace ℂ ε}
    (hz : IsUnitVector (WithLp.ofLp z)) (w : EuclideanSpace ℂ ε) :
    fderiv ℝ cubicSphereEuclidean z w =
      WithLp.toLp 2 (dCubicSphere (WithLp.ofLp z) (WithLp.ofLp w)) := by
  apply fderiv_apply_eq_of_hasDerivAt_line
    (contDiff_cubicSphereEuclidean.differentiable (by simp)).differentiableAt
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ε => ℂ)
  exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_cubicSphere hz (WithLp.ofLp w))

theorem norm_fderiv_cubicSphereEuclidean_le_one {z : EuclideanSpace ℂ ε}
    (hz : IsUnitVector (WithLp.ofLp z)) : ‖fderiv ℝ cubicSphereEuclidean z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  rw [fderiv_cubicSphereEuclidean_apply hz, one_mul]
  exact (dCubicSphere_projection hz (WithLp.ofLp w)).2.2

end Sphere

end NLQCLean
