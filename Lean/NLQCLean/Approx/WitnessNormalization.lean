import NLQCLean.Rigidity.CoordinateWitnessDifferential
import NLQCLean.Models.CompactForward

/-!
# Inverse normalization and the exact six-block source radius

Divide each matrix by the square root of its column count. This is
invertible for every charged shape and d > 0. Each normalized valid block
has norm one, so every padded valid source point has Euclidean norm sqrt(6).
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem norm_rescaled_isometry_eq_one {m k : Type*}
    [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {n : ℝ} (hn : 0 < n) (hcard : (Fintype.card k : ℝ) = n) {W : Matrix m k ℂ}
    (hW : IsIsometry (Real.sqrt n • W)) : ‖W‖ = 1 := by
  have hs := hW.frobNorm_sq_eq_card
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n), mul_pow,
    Real.sq_sqrt hn.le, hcard] at hs
  have he : ‖W‖ ^ 2 = 1 := by nlinarith
  nlinarith [norm_nonneg W]

theorem norm_euclidean_of_isUnitVector {ι : Type*} [Fintype ι] {z : ι → ℂ}
    (hz : IsUnitVector z) : ‖WithLp.toLp 2 z‖ = 1 := by
  change sqNorm z = 1 at hz
  rw [sqNorm_eq_euclidean_norm_sq] at hz
  nlinarith [norm_nonneg (WithLp.toLp 2 z)]

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

/-- Inverse of the column-count rescaling on all six blocks. -/
noncomputable def normalizeBlocks : ReverseBlocks s →ₗ[ℝ] ReverseBlocks s where
  toFun x := (x.1, x.2.1, (Real.sqrt (d * s.r : ℝ))⁻¹ • x.2.2.1,
    (Real.sqrt (d * s.r : ℝ))⁻¹ • x.2.2.2.1, (Real.sqrt (d * K : ℝ))⁻¹ • x.2.2.2.2.1,
    (Real.sqrt (d * K : ℝ))⁻¹ • x.2.2.2.2.2)
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm c]

theorem rescale_normalizeBlocks (hd : 0 < d) (x : ReverseBlocks s) :
    rescaleBlocks (normalizeBlocks x) = x := by
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
  simp only [rescaleBlocks, normalizeBlocks, LinearMap.coe_mk, AddHom.coe_mk, smul_smul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hdr).ne', mul_inv_cancel₀ (Real.sqrt_pos.mpr hdK).ne', one_smul]

theorem normalize_rescaleBlocks (hd : 0 < d) (x : ReverseBlocks s) :
    normalizeBlocks (rescaleBlocks x) = x := by
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
  simp only [rescaleBlocks, normalizeBlocks, LinearMap.coe_mk, AddHom.coe_mk, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hdr).ne', inv_mul_cancel₀ (Real.sqrt_pos.mpr hdK).ne', one_smul]

theorem blockNorms_eq_one_of_valid {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (i : Fin 6) : blockNorms x i = 1 := by
  have hdr : 0 < (d * s.r : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.resource_pos)
  have hdK : 0 < (d * K : ℝ) := mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.one_le_budget)
  have ha := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.1
  have hb := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.2.1
  have hta := norm_rescaled_isometry_eq_one hdK (by simp) hx.2.2.2.2.1
  have htb := norm_rescaled_isometry_eq_one hdK (by simp) hx.2.2.2.2.2
  fin_cases i
  · exact norm_euclidean_of_isUnitVector hx.1
  · exact norm_euclidean_of_isUnitVector hx.2.1
  · exact ha
  · exact hb
  · exact hta
  · exact htb

theorem euclideanNorm_eq_sqrt_six {x : ReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) : euclideanNorm x = Real.sqrt 6 := by
  simp [euclideanNorm, blockNorms_eq_one_of_valid hx hd]

theorem norm_padded_valid_eq_sqrt_six (s : ReverseShape d K) (hd : 0 < d)
    {x : RealEuclidean (witnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x)))
    (hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) : ‖x‖ = Real.sqrt 6 := by
  rw [← encode_decodeCoordinates_of_padding s hd x hpad, norm_encodeCoordinates]
  exact euclideanNorm_eq_sqrt_six hx hd

/-- Every original valid witness has a padded normalized representative of
the exact required radius, with its raw overlap unchanged. -/
theorem exists_normalized_coordinate_witness (s : ReverseShape d K) (hd : 0 < d)
    {x : ReverseBlocks s} (hx : IsValid x) :
    ∃ y : RealEuclidean (witnessCoordinateBudget d K),
      rescaleBlocks (decodeCoordinates s hd y) = x ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd), y j = 0) ∧
      ‖y‖ = Real.sqrt 6 ∧ coordinateRawOverlap s hd y = overlapOutputCoordinates d (overlap x) := by
  let y := encodeCoordinates s hd (normalizeBlocks x)
  have hy : rescaleBlocks (decodeCoordinates s hd y) = x := by
    dsimp only [y]
    rw [decode_encodeCoordinates, rescale_normalizeBlocks hd]
  have hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd), y j = 0 :=
    fun _ hj => encodeCoordinates_zero_padding s hd _ hj
  refine ⟨y, hy, hpad, norm_padded_valid_eq_sqrt_six s hd (hy.symm ▸ hx) hpad, ?_⟩
  rw [coordinateRawOverlap, hy]

end ReverseBlocks
end NLQCLean
