import NLQCLean.Approx.PVMReverseWitness
import NLQCLean.Approx.WitnessNormalization

/-!
# Normalization of the six PVM reverse-witness blocks

The dependent garbage family is one Euclidean block, formed by
an `l2` sum of its per-label Euclidean norms.  Rescaling restores the physical
normalizations: one factor of `sqrt (d^2)` for the whole garbage family,
column-count factors for the encoders, and `sqrt supportSize` for the two
reverse matrices.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

namespace PVMReverseBlocks

variable {d K : ℕ} {s : PVMReverseShape d K}

/-- The six Euclidean block norms.  The dependent garbage family is a single
block with the `l2` sum of all of its per-label vector norms. -/
noncomputable def blockNorms (x : PVMReverseBlocks s) : Fin 6 → ℝ :=
  ![‖WithLp.toLp 2 x.1‖,
    Real.sqrt (∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2),
    ‖x.2.2.1‖,
    ‖x.2.2.2.1‖,
    ‖x.2.2.2.2.1‖,
    ‖x.2.2.2.2.2‖]

/-- The Euclidean norm obtained by combining the six block norms in `l2`. -/
noncomputable def euclideanNorm (x : PVMReverseBlocks s) : ℝ :=
  Real.sqrt (∑ i, blockNorms x i ^ 2)

theorem euclideanNorm_nonneg (x : PVMReverseBlocks s) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- Restore the physical scale of all six blocks.  The resource vector is
already unit scale; the dependent garbage family has `d^2` unit vectors. -/
noncomputable def rescaleBlocks : PVMReverseBlocks s →ₗ[ℝ] PVMReverseBlocks s where
  toFun x :=
    (x.1,
      Real.sqrt (d ^ 2 : ℝ) • x.2.1,
      Real.sqrt (d * s.1.r : ℝ) • x.2.2.1,
      Real.sqrt (d * s.1.r : ℝ) • x.2.2.2.1,
      Real.sqrt (s.supportSize : ℝ) • x.2.2.2.2.1,
      Real.sqrt (s.supportSize : ℝ) • x.2.2.2.2.2)
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm c]

/-- Divide by the same scale factors used by `rescaleBlocks`. -/
noncomputable def normalizeBlocks : PVMReverseBlocks s →ₗ[ℝ] PVMReverseBlocks s where
  toFun x :=
    (x.1,
      (Real.sqrt (d ^ 2 : ℝ))⁻¹ • x.2.1,
      (Real.sqrt (d * s.1.r : ℝ))⁻¹ • x.2.2.1,
      (Real.sqrt (d * s.1.r : ℝ))⁻¹ • x.2.2.2.1,
      (Real.sqrt (s.supportSize : ℝ))⁻¹ • x.2.2.2.2.1,
      (Real.sqrt (s.supportSize : ℝ))⁻¹ • x.2.2.2.2.2)
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm c]

private theorem supportSize_pos (s : PVMReverseShape d K) (hd : 0 < d) :
    0 < s.supportSize := by
  let i : Fin d × Fin d := (⟨0, hd⟩, ⟨0, hd⟩)
  have hi : s.2.rank i ≤ ∑ j, s.2.rank j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  exact (s.2.rank_pos i).trans_le hi

theorem rescale_normalizeBlocks (hd : 0 < d) (x : PVMReverseBlocks s) :
    rescaleBlocks (normalizeBlocks x) = x := by
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by
    exact_mod_cast supportSize_pos s hd
  simp only [rescaleBlocks, normalizeBlocks, LinearMap.coe_mk, AddHom.coe_mk,
    smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hd2).ne',
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hdr).ne',
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hS).ne', one_smul]

theorem normalize_rescaleBlocks (hd : 0 < d) (x : PVMReverseBlocks s) :
    normalizeBlocks (rescaleBlocks x) = x := by
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by
    exact_mod_cast supportSize_pos s hd
  simp only [rescaleBlocks, normalizeBlocks, LinearMap.coe_mk, AddHom.coe_mk,
    smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hd2).ne',
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hdr).ne',
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hS).ne', one_smul]

/-- Each garbage vector, rather than only the combined garbage block, retains
its unit constraint after rescaling. -/
theorem isUnitVector_rescaled_garbage {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (i : Fin d × Fin d) :
    IsUnitVector (Real.sqrt (d ^ 2 : ℝ) • x.2.1 i) := by
  simpa only [rescaleBlocks, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply] using hx.2.1 i

private theorem mul_euclidean_norm_sq_of_rescaled_unitVector
    {i : Type*} [Fintype i] {n : ℝ} (hn : 0 < n) {z : i → ℂ}
    (hz : IsUnitVector (Real.sqrt n • z)) :
    n * ‖WithLp.toLp 2 z‖ ^ 2 = 1 := by
  have h := norm_euclidean_of_isUnitVector hz
  change ‖Real.sqrt n • WithLp.toLp 2 z‖ = 1 at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n)] at h
  nlinarith [Real.sq_sqrt hn.le]

/-- The `d^2` individually normalized garbage vectors contribute exactly one
to the squared norm of their normalized combined block. -/
theorem garbageNorm_eq_one_of_valid {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    Real.sqrt (∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2) = 1 := by
  have hd2 : 0 < (d ^ 2 : ℝ) := by exact_mod_cast pow_pos hd 2
  have hmul :
      (d ^ 2 : ℝ) * (∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2) = (d ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    calc
      ∑ i, (d ^ 2 : ℝ) * ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2 = ∑ _ : Fin d × Fin d, (1 : ℝ) :=
        Finset.sum_congr rfl fun i _ ↦
          mul_euclidean_norm_sq_of_rescaled_unitVector hd2
            (isUnitVector_rescaled_garbage hx i)
      _ = (d ^ 2 : ℝ) := by simp [pow_two]
  have hsum : ∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2 = 1 := by
    apply mul_left_cancel₀ hd2.ne'
    simpa using hmul
  rw [hsum, Real.sqrt_one]

theorem blockNorms_eq_one_of_valid {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (i : Fin 6) :
    blockNorms x i = 1 := by
  have hdr : 0 < (d * s.1.r : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)
  have hS : 0 < (s.supportSize : ℝ) := by
    exact_mod_cast supportSize_pos s hd
  have ha := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.1
  have hb := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.2.1
  have hta := norm_rescaled_isometry_eq_one hS (by simp [s.card_support]) hx.2.2.2.2.1
  have htb := norm_rescaled_isometry_eq_one hS (by simp [s.card_support]) hx.2.2.2.2.2
  fin_cases i
  · exact norm_euclidean_of_isUnitVector hx.1
  · exact garbageNorm_eq_one_of_valid hx hd
  · exact ha
  · exact hb
  · exact hta
  · exact htb

theorem euclideanNorm_eq_sqrt_six {x : PVMReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) :
    euclideanNorm x = Real.sqrt 6 := by
  simp [euclideanNorm, blockNorms_eq_one_of_valid hx hd]

end PVMReverseBlocks
end NLQCLean
