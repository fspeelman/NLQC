import NLQCLean.Rigidity.PVMWitnessCalculus
import NLQCLean.Approx.PVMBlockNormalization
import NLQCLean.Approx.PVMCoordinateCount
import NLQCLean.Approx.WitnessVelocityBounds

/-!
# PVM witness velocity bounds

Vector velocities use their true Euclidean norms; the
label-dependent garbage family contributes its full squared-norm sum.
The estimates hold for all velocities before imposing tangent constraints.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- The compressed flag stores exactly one copy of every garbage entry. -/
theorem frobNorm_compressedFlag_sq {δ : Type*} [Fintype δ] [DecidableEq δ]
    {s : δ → ℕ} (g : ∀ i, Fin (s i) × Fin (s i) → ℂ) :
    ‖compressedFlag g‖ ^ 2 = ∑ i, ‖WithLp.toLp 2 (g i)‖ ^ 2 := by
  classical
  rw [frobNorm_sq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [compressedFlag, apply_dite, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Fintype.sum_sigma]

/-- A garbage velocity is bounded by its combined Euclidean norm. -/
theorem opNorm_compressedFlag_le {δ : Type*} [Fintype δ] [DecidableEq δ]
    {s : δ → ℕ} (g : ∀ i, Fin (s i) × Fin (s i) → ℂ) :
    opNorm (compressedFlag g) ≤ Real.sqrt (∑ i, ‖WithLp.toLp 2 (g i)‖ ^ 2) := by
  rw [← frobNorm_compressedFlag_sq, Real.sqrt_sq (norm_nonneg _)]
  exact opNorm_le_frobNorm _

namespace PVMReverseBlocks
variable {d K : ℕ} {s : PVMReverseShape d K}

theorem IsValid.opNorm_forwardVelocity_le {x : PVMReverseBlocks s} (hx : IsValid x) (v : PVMReverseBlocks s) :
    opNorm (forwardVelocity x v) ≤ ‖v.2.2.1‖ + ‖v.2.2.2.1‖ + ‖WithLp.toLp 2 v.1‖ := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  exact ((opNorm_isometry_mul_le hE _).trans
    (opNorm_encodedStateVelocity_le hx.1 v.1 hx.2.2.1 hx.2.2.2.1 v.2.2.1 v.2.2.2.1)).trans
      (add_le_add (add_le_add (opNorm_le_frobNorm _) (opNorm_le_frobNorm _)) le_rfl)

theorem IsValid.opNorm_reverseVelocity_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (v : PVMReverseBlocks s) :
    opNorm (reverseVelocity x v) ≤ ‖v.2.2.2.2.1‖ + ‖v.2.2.2.2.2‖ +
      Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) := by
  have h1 : opNorm (x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2) ≤ opNorm v.2.2.2.2.2 :=
    (opNorm_kronecker_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right hx.2.2.2.2.1.opNorm_le_one
        (opNorm_nonneg v.2.2.2.2.2))
  have h2 : opNorm (v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) ≤ opNorm v.2.2.2.2.1 :=
    (opNorm_kronecker_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left hx.2.2.2.2.2.opNorm_le_one
        (opNorm_nonneg v.2.2.2.2.1))
  rw [reverseVelocity]
  calc
    _ ≤ opNorm ((x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2 + v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) *
        compressedFlag x.2.1) +
        opNorm ((x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * compressedFlag v.2.1) := opNorm_add_le _ _
    _ ≤ opNorm (x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2 + v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) +
        opNorm (compressedFlag v.2.1) :=
      add_le_add (opNorm_mul_isometry_le _ (isIsometry_compressedFlag _ hx.2.1))
        (opNorm_isometry_mul_le (hx.2.2.2.2.1.kronecker hx.2.2.2.2.2) _)
    _ ≤ (opNorm (x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2) +
        opNorm (v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2)) +
        Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) :=
      add_le_add (opNorm_add_le _ _) (opNorm_compressedFlag_le _)
    _ ≤ _ := by linarith [opNorm_le_frobNorm v.2.2.2.2.1, opNorm_le_frobNorm v.2.2.2.2.2]

theorem garbageNorm_smul (c : ℝ) (g : (i : Fin d × Fin d) →
    Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    Real.sqrt (∑ i, ‖WithLp.toLp 2 ((c • g) i)‖ ^ 2) =
      |c| * Real.sqrt (∑ i, ‖WithLp.toLp 2 (g i)‖ ^ 2) := by
  have he (i : Fin d × Fin d) :
      ‖WithLp.toLp 2 ((c • g) i)‖ = |c| * ‖WithLp.toLp 2 (g i)‖ := by
    change ‖c • WithLp.toLp 2 (g i)‖ = _
    rw [norm_smul, Real.norm_eq_abs]
  simp only [he, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg c)]

/-- Exact Cauchy--Schwarz coefficient for the six normalized groups. -/
theorem IsValid.rescaled_speed_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (v : PVMReverseBlocks s) :
    opNorm (forwardVelocity x (rescaleBlocks v)) + opNorm (reverseVelocity x (rescaleBlocks v)) ≤
      Real.sqrt (1 + (d ^ 2 : ℝ) + 2 * (d * s.1.r : ℝ) + 2 * s.supportSize) * euclideanNorm v := by
  let weights : Fin 6 → ℝ := ![1, Real.sqrt (d ^ 2 : ℝ),
    Real.sqrt (d * s.1.r : ℝ), Real.sqrt (d * s.1.r : ℝ),
    Real.sqrt (s.supportSize : ℝ), Real.sqrt (s.supportSize : ℝ)]
  have hb : opNorm (forwardVelocity x (rescaleBlocks v)) +
      opNorm (reverseVelocity x (rescaleBlocks v)) ≤ ∑ i, weights i * blockNorms v i := by
    have h := add_le_add (hx.opNorm_forwardVelocity_le (rescaleBlocks v))
      (hx.opNorm_reverseVelocity_le (rescaleBlocks v))
    change _ ≤ (‖Real.sqrt (d * s.1.r : ℝ) • v.2.2.1‖ +
      ‖Real.sqrt (d * s.1.r : ℝ) • v.2.2.2.1‖ + ‖WithLp.toLp 2 v.1‖) +
      (‖Real.sqrt (s.supportSize : ℝ) • v.2.2.2.2.1‖ +
      ‖Real.sqrt (s.supportSize : ℝ) • v.2.2.2.2.2‖ +
      Real.sqrt (∑ i, ‖WithLp.toLp 2 ((Real.sqrt (d ^ 2 : ℝ) • v.2.1) i)‖ ^ 2)) at h
    rw [garbageNorm_smul] at h
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h.trans_eq (by
      simp only [blockNorms, weights, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul]
      ring)
  have hw : ∑ i, weights i ^ 2 =
      1 + (d ^ 2 : ℝ) + 2 * (d * s.1.r : ℝ) + 2 * s.supportSize := by
    simp [weights, Fin.sum_univ_succ, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg s.supportSize)]
    ring
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ weights (blockNorms v)
  rw [hw] at h
  exact hb.trans h

/-- The footprint floor gives a universal speed coefficient. -/
theorem IsValid.rescaled_speed_le_sqrt_ten {x : PVMReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (hfloor : d ^ 2 ≤ 4 * K) (v : PVMReverseBlocks s) :
    opNorm (forwardVelocity x (rescaleBlocks v)) + opNorm (reverseVelocity x (rescaleBlocks v)) ≤
      Real.sqrt (10 * d * K : ℝ) * euclideanNorm v := by
  have hr : s.1.r ≤ K := (s.1.dimensions_le_budget).1
  have hrR : (s.1.r : ℝ) ≤ K := by exact_mod_cast hr
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast s.one_le_budget
  have hSR : (s.supportSize : ℝ) ≤ K + (d : ℝ) ^ 2 := by exact_mod_cast s.supportSize_le
  have hfloorR : (d : ℝ) ^ 2 ≤ 4 * K := by exact_mod_cast hfloor
  have hc : 1 + (d ^ 2 : ℝ) + 2 * (d * s.1.r : ℝ) + 2 * s.supportSize ≤ 10 * d * K := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (d : ℝ)) (sub_nonneg.mpr hrR),
      mul_nonneg (sub_nonneg.mpr hdR) (by positivity : 0 ≤ (K : ℝ))]
  exact (hx.rescaled_speed_le v).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hc) (euclideanNorm_nonneg v))

end PVMReverseBlocks
end NLQCLean
