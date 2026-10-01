import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Euclidean ball caps

For a vector `w` with `‖w‖ ≤ 1` in a real
finite-dimensional inner product space of dimension `n`, and `t, R > 0`,

  `vol {x ∈ B_R : t ≤ |⟪w, x⟫|} ≤ 2 exp(−n t²/(2R²)) vol B_R`.

Each half-cap is translated by `−t u` into the ball of radius `√(R² − t²)`; translation
invariance and scaling of Haar measure finish the estimate. No sphere measure is used.
-/

namespace NLQCLean

open MeasureTheory Metric Module

theorem sqrt_sub_sq_pow_le_exp {t R : ℝ} (ht : 0 ≤ t) (htR : t < R) (n : ℕ) :
    Real.sqrt (R ^ 2 - t ^ 2) ^ n ≤ Real.exp (-(n * t ^ 2 / (2 * R ^ 2))) * R ^ n := by
  have hR : 0 < R := ht.trans_lt htR
  set a := t ^ 2 / R ^ 2 with ha
  have hR2 : 0 < R ^ 2 := by positivity
  have hfac : Real.sqrt (R ^ 2 - t ^ 2) = Real.sqrt (1 - a) * R := by
    rw [show R ^ 2 - t ^ 2 = (1 - a) * R ^ 2 by rw [ha]; field_simp, Real.sqrt_mul' _ hR2.le,
      Real.sqrt_sq hR.le]
  have h1 : Real.sqrt (1 - a) ≤ Real.exp (-(a / 2)) := by
    rw [show Real.exp (-(a / 2)) = Real.sqrt (Real.exp (-a)) by
      rw [← Real.exp_half]; congr 1; ring]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp (-a)])
  rw [hfac, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc Real.sqrt (1 - a) ^ n ≤ Real.exp (-(a / 2)) ^ n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 n
    _ = Real.exp (-(n * t ^ 2 / (2 * R ^ 2))) := by
        rw [← Real.exp_nat_mul, ha]; congr 1; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- One-sided cap for a unit vector. -/
theorem volume_halfCap_le {u : E} (hu : ‖u‖ = 1) {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    volume ({x : E | t ≤ inner ℝ u x} ∩ ball 0 R) ≤
      ENNReal.ofReal (Real.exp (-(finrank ℝ E * t ^ 2 / (2 * R ^ 2)))) * volume (ball (0 : E) R) := by
  have hE : Nontrivial E := ⟨⟨u, 0, fun h => by simp [h] at hu⟩⟩
  rcases le_or_gt R t with htR | htR
  · have : {x : E | t ≤ inner ℝ u x} ∩ ball 0 R = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_ball, dist_zero_right,
        Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hx
      have := real_inner_le_norm u x
      rw [hu, one_mul] at this
      linarith
    rw [this, measure_empty]
    exact zero_le
  have hρ : 0 ≤ R ^ 2 - t ^ 2 := by nlinarith
  have hsub : {x : E | t ≤ inner ℝ u x} ∩ ball 0 R ⊆ ball (t • u) (Real.sqrt (R ^ 2 - t ^ 2)) := by
    rintro x ⟨hx1, hx2⟩
    simp only [Set.mem_ofPred_eq] at hx1
    rw [mem_ball, dist_zero_right] at hx2
    rw [mem_ball, dist_eq_norm, Real.lt_sqrt (norm_nonneg _)]
    have hexp : ‖x - t • u‖ ^ 2 = ‖x‖ ^ 2 - 2 * t * inner ℝ u x + t ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, real_inner_comm, norm_smul, hu, Real.norm_eq_abs,
        abs_of_pos ht]
      ring
    rw [hexp]
    have hx2' : ‖x‖ ^ 2 < R ^ 2 := by
      have := norm_nonneg x
      nlinarith
    nlinarith
  refine (measure_mono hsub).trans ?_
  rw [Measure.addHaar_ball volume _ (Real.sqrt_nonneg _), Measure.addHaar_ball volume _ hR.le,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (zero_le)
  exact sqrt_sub_sq_pow_le_exp ht.le htR _

/-- Cap lemma. -/
theorem volume_cap_le {w : E} (hw : ‖w‖ ≤ 1) {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    volume ({x : E | t ≤ |inner ℝ w x|} ∩ ball 0 R) ≤
      2 * ENNReal.ofReal (Real.exp (-(finrank ℝ E * t ^ 2 / (2 * R ^ 2)))) *
        volume (ball (0 : E) R) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · have : {x : E | t ≤ |inner ℝ (0 : E) x|} ∩ ball 0 R = ∅ := by
      ext x; simp [not_le.mpr ht]
    rw [this, measure_empty]
    exact zero_le
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set u : E := ‖w‖⁻¹ • w with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  have hsub : {x : E | t ≤ |inner ℝ w x|} ∩ ball 0 R ⊆
      ({x : E | t ≤ inner ℝ u x} ∩ ball 0 R) ∪ ({x : E | t ≤ inner ℝ (-u) x} ∩ ball 0 R) := by
    rintro x ⟨hx1, hx2⟩
    simp only [Set.mem_ofPred_eq] at hx1
    have hscale : inner ℝ w x = ‖w‖ * inner ℝ u x := by
      rw [hu_def, inner_smul_left, RCLike.conj_to_real, ← mul_assoc, mul_inv_cancel₀ hwpos.ne',
        one_mul]
    rw [hscale, abs_mul, abs_of_pos hwpos] at hx1
    have hux : t ≤ |inner ℝ u x| := by
      have : ‖w‖ * |inner ℝ u x| ≤ |inner ℝ u x| :=
        mul_le_of_le_one_left (abs_nonneg _) hw
      linarith
    rcases le_abs'.mp hux with h | h
    · right
      refine ⟨?_, hx2⟩
      simp only [Set.mem_ofPred_eq, inner_neg_left]
      linarith
    · exact Or.inl ⟨h, hx2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h1 := volume_halfCap_le hu ht hR
  have h2 := volume_halfCap_le (u := -u) (by rw [norm_neg, hu]) ht hR
  calc _ ≤ ENNReal.ofReal (Real.exp (-(finrank ℝ E * t ^ 2 / (2 * R ^ 2)))) *
          volume (ball (0 : E) R) +
        ENNReal.ofReal (Real.exp (-(finrank ℝ E * t ^ 2 / (2 * R ^ 2)))) *
          volume (ball (0 : E) R) := add_le_add h1 h2
    _ = _ := by rw [← two_mul, mul_assoc]

end NLQCLean
