
import NLQCLean.Geometry.SemialgebraicImageVolume

/-!
# Uniform constants for LRT graph-selection volume bounds

Dimension-independent component and volume bases used by the canonical
polynomial image-volume argument.
-/

section

namespace NLQCLean

open MeasureTheory
open scoped ENNReal

def lrtSelectionComponentBase (κ : ℕ) : ℕ := componentFormatBase (2 * κ) (max (κ * 200) 2)

noncomputable def lrtSelectionVolumeBase (κ : ℕ) : ℝ := 4 * (lrtSelectionComponentBase κ : ℝ)

theorem lrtSelectionVolumeBase_ge_one (κ : ℕ) : 1 ≤ lrtSelectionVolumeBase κ := by
  have hβ : (1 : ℝ) ≤ lrtSelectionComponentBase κ := by
    exact_mod_cast componentFormatBase_pos (2 * κ) (max (κ * 200) 2)
  unfold lrtSelectionVolumeBase
  linarith

theorem lrt_selection_volume_constant_eq (κ a m : ℕ) (b : ℝ) :
    ENNReal.ofReal ((4 : ℝ) ^ a) * (lrtSelectionComponentBase κ ^ (a + m) : ℕ) *
      euclideanUnitBallVolume m * ENNReal.ofReal ((4 : ℝ) ^ m) * ENNReal.ofReal b =
    ENNReal.ofReal (lrtSelectionVolumeBase κ ^ (a + m)) * euclideanUnitBallVolume m *
      ENNReal.ofReal b := by
  have hbase : ENNReal.ofReal (lrtSelectionVolumeBase κ) =
      4 * (lrtSelectionComponentBase κ : ℝ≥0∞) := by
    unfold lrtSelectionVolumeBase
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hpow : ENNReal.ofReal (lrtSelectionVolumeBase κ ^ (a + m)) =
      (4 : ℝ≥0∞) ^ (a + m) * (lrtSelectionComponentBase κ : ℝ≥0∞) ^ (a + m) := by
    rw [ENNReal.ofReal_pow (zero_le_one.trans (lrtSelectionVolumeBase_ge_one κ)), hbase, mul_pow]
  have hβpow : ((lrtSelectionComponentBase κ ^ (a + m) : ℕ) : ℝ≥0∞) =
      (lrtSelectionComponentBase κ : ℝ≥0∞) ^ (a + m) := Nat.cast_pow _ _
  rw [hpow, hβpow, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num only [ENNReal.ofReal_ofNat]
  simp only [pow_add]
  ac_rfl

theorem euclideanUnitBallVolume_ne_top (m : ℕ) : euclideanUnitBallVolume m ≠ ∞ :=
  measure_ball_lt_top.ne

end NLQCLean
end
