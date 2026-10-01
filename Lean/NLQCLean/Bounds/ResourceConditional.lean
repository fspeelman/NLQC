import NLQCLean.Bounds.ResourceArithmetic
import NLQCLean.Bounds.SwapFloor
import NLQCLean.Bounds.HaarFractionConditional
import NLQCLean.Models.UniversalReachability

/-!
# Conditional universal footprint and qubit lower bounds

Universality retains target-dependent protocols and all finite
architectures. Exact support compression shows that these
finite-index predicates cover arbitrary original private/register types.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

/-- Universality at SWAP gives the unconditional source floor. -/
theorem PureUniversalScore.swap_floor {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (h : PureUniversalScore d K e) : (d : ℝ) ^ 2 * (1 - e) ≤ K := by
  let : NeZero d := ⟨hd.ne'⟩
  let U : Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    ⟨swapUnitary (Fin d), Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_swapUnitary (Fin d))⟩
  obtain ⟨s, P, hP, hscore⟩ := h U
  have hf := P.swap_footprint_floor hP hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hf

theorem PureUniversalScore.half_dimension_le {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (he : e ≤ 1 / 2) (h : PureUniversalScore d K e) : (d : ℝ) ^ 2 / 2 ≤ K := by
  have hf := h.swap_floor hd
  nlinarith [sq_nonneg (d : ℝ)]

theorem MixedUniversalScore.swap_floor {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (h : MixedUniversalScore d K e) : (d : ℝ) ^ 2 * (1 - e) ≤ K :=
  ((mixedUniversalScore_iff_pure d K e).mp h).swap_floor hd

/-- Resource bound: one positive constant works for pure and finite mixed universal implementations. -/
theorem exists_universal_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨C, hC, hHaar⟩ := exists_haar_fraction_constant hGeom
  have hC0 : 0 < C := by linarith
  refine ⟨Real.sqrt (3 / (32 * C)), by positivity, ?_⟩
  intro d K hd hK e he he'
  have hpure (hu : PureUniversalScore d K e) :
      Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have hhalf := hu.half_dimension_le (by omega : 0 < d) he'
    have hquarter : (d : ℝ) ^ 2 / 4 ≤ K := by nlinarith [sq_nonneg (d : ℝ)]
    have hm := (hHaar d K hd hK hquarter e he he').2.2.1
    rw [hu.reachable_eq_univ, unitaryHaar_univ] at hm
    have hone : 1 ≤ Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((unitaryCodimension d : ℝ) / 2) :=
      ENNReal.one_le_ofReal.mp (hm.trans (min_le_right _ _))
    exact resource_lower_of_one_le_haar_rhs hd hC0 he (by linarith) hone
  exact ⟨hpure, fun hm => hpure ((mixedUniversalScore_iff_pure d K e).mp hm)⟩

/-- Qubit bound: one nonnegative additive constant, with real base-two logarithms. -/
theorem exists_universal_qubit_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PureUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨c, hc, hresource⟩ := exists_universal_resource_constant hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, ?_⟩
  intro n K hn hK e he he'
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hL : 0 < Real.log (1 / e) := Real.log_pos ((one_lt_div₀ he).mpr (by linarith))
  obtain ⟨hp, hm⟩ := hresource (2 ^ n) K hd hK e he he'
  constructor
  · intro hu
    have h := hp hu
    push_cast at h
    exact qubit_lower_of_resource hc hL n h
  · intro hu
    have h := hm hu
    push_cast at h
    exact qubit_lower_of_resource hc hL n h

end NLQCLean
