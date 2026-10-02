import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.Quantitative

/-! # Universal unitary bounds combining the SWAP floor and precision -/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

private theorem scaled_max_le {c x y z : ℝ}
    (hx : c * x ≤ z) (hy : c * y ≤ z) : c * max x y ≤ z := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

/-- The SWAP floor supplies the constant term in the precision maximum,
with one constant for pure and common-map finite-mixed resources. -/
theorem exists_strongUniversalMaxResourceBound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedUniversalScore d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) := by
  obtain ⟨c, hc, hprecision⟩ := exists_strongUniversalResourceBound_of_imageVolumeBound hGeom
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), ?_⟩
  intro d K hd e he he2
  have hpure (h : PureUniversalScore d K e) :
      min c (1 / 2) * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K := by
    have hfloor : min c (1 / 2) * (d : ℝ) ^ 2 * 1 ≤ K := by
      have hmin := mul_le_mul_of_nonneg_right (min_le_right c (1 / 2))
        (sq_nonneg (d : ℝ))
      have hf := h.half_dimension_le (by omega : 0 < d) he2
      nlinarith
    have hrate : min c (1 / 2) * (d : ℝ) ^ 2 *
        Real.sqrt (Real.log (1 / e)) ≤ K := by
      calc
        _ ≤ c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (min_le_left c (1 / 2)) (sq_nonneg _))
            (Real.sqrt_nonneg _)
        _ ≤ K := (hprecision d K hd e he he2).1 h
    exact scaled_max_le hfloor hrate
  exact ⟨hpure, fun h => hpure ((mixedUniversalScore_iff_pure d K e).mp h)⟩

/-- The unitary maximum bound. -/
theorem exists_strongUniversalMaxResourceBound :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedUniversalScore d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) :=
  exists_strongUniversalMaxResourceBound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- The same maximum bound for normalized diamond universality. -/
theorem exists_strongUniversalMaxDiamondResourceBound :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) ^ 2 * max 1 (Real.sqrt (Real.log (1 / e))) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_strongUniversalMaxResourceBound
  refine ⟨c, hc, ?_⟩
  intro d K hd e he he2
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := h d K hd e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

end NLQCLean
