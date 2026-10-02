import NLQCLean.Bounds.StrongHaarConditional
import NLQCLean.Bounds.SwapNeighborhoodHaar
import NLQCLean.Bounds.DiamondConditional

/-!
# Universal `d²` resource and qubit bounds

A universal pure or finite-mixed implementation at
error `0 < e ≤ 1/2` has `K ≥ D/2` by the SWAP floor, and all of `S_d` is reachable. Comparing
`μ_d(S_d) ≥ exp(−5N)` with the restricted bound `exp(C K²) e^(N/16)` gives
`(N/16) log(1/e) ≤ C K² + 5N ≤ (C + 20) K²`, hence

  `K ≥ d² √log(1/e) / (4 √(C + 20))`,

and at `d = 2ⁿ`, `log₂ K ≥ 2n + ½ log₂ log(1/e) − b`. Diamond universality implies score
universality. No near-SWAP or `K ≥ D/2` premise remains in these exports.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- The logarithmic step: patch mass against the restricted Haar bound. -/
theorem strong_resource_of_patch {C : ℝ} (hC : 0 ≤ C) {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 2 ≤ K) {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (h : Real.exp (-(5 * (d : ℝ) ^ 4)) ≤ Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16)) :
    1 / (4 * Real.sqrt (C + 20)) * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2K : (d : ℝ) ^ 2 ≤ 2 * K := by linarith
  have hNK : (d : ℝ) ^ 4 ≤ 4 * (K : ℝ) ^ 2 := by
    have h2 := pow_le_pow_left₀ (by positivity) h2K 2
    calc (d : ℝ) ^ 4 = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (K : ℝ)) ^ 2 := h2
      _ = 4 * (K : ℝ) ^ 2 := by ring
  set L := Real.log (1 / e) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div₀ he).mpr he1)
  have hlog : (d : ℝ) ^ 4 / 16 * L ≤ (C + 20) * (K : ℝ) ^ 2 := by
    rw [Real.rpow_def_of_pos he, ← Real.exp_add, Real.exp_le_exp] at h
    rw [hLdef, one_div, Real.log_inv]
    have h5 : 5 * (d : ℝ) ^ 4 ≤ 20 * (K : ℝ) ^ 2 := by linarith
    linarith
  have hC20 : 0 < C + 20 := by linarith
  set x := 1 / (4 * Real.sqrt (C + 20)) * (d : ℝ) ^ 2 * Real.sqrt L with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = (d : ℝ) ^ 4 * L / (16 * (C + 20)) := by
    rw [hxdef, mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hC20.le, Real.sq_sqrt hL0]
    ring
  have hxK : x ^ 2 ≤ (K : ℝ) ^ 2 := by
    rw [hx2, div_le_iff₀ (by positivity)]
    linarith
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) hK0 (by norm_num : (2 : ℕ) ≠ 0)
  linarith

/-- The universal `d²` resource bound from the polynomial image-volume property. -/
theorem exists_strongUniversalResourceBound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalResourceBound c := by
  obtain ⟨C, hC, hH⟩ := exists_strongRestrictedHaarBound_of_imageVolumeBound hGeom
  refine ⟨1 / (4 * Real.sqrt (C + 20)), by positivity, ?_⟩
  intro d K hd e he he2
  have hpure (hu : PureUniversalScore d K e) :
      1 / (4 * Real.sqrt (C + 20)) * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have hK := hu.half_dimension_le (by omega : 0 < d) he2
    have hm := (hH d K hd hK e he he2).1
    rw [hu.reachable_eq_univ, Set.inter_univ] at hm
    have hpatch := strongSwapPatchMassBound_five d hd
    have hle := (hpatch.trans hm).trans (min_le_right _ _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    exact strong_resource_of_patch (by linarith) hd hK he (by linarith) hle
  exact ⟨hpure, fun hm => hpure ((mixedUniversalScore_iff_pure d K e).mp hm)⟩

/-- The same for universal normalized diamond implementation. -/
theorem exists_strongUniversalDiamondResourceBound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} c := by
  obtain ⟨c, hc, h⟩ := exists_strongUniversalResourceBound_of_imageVolumeBound hGeom
  refine ⟨c, hc, ?_⟩
  intro d K hd e he he2
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hm⟩ := h d K hd e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

theorem strong_qubit_of_resource {c K e : ℝ} (hc : 0 < c) (he : 0 < e) (he2 : e ≤ 1 / 2) (n : ℕ)
    (h : c * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) :
    2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - max 0 (-Real.logb 2 c) ≤
      Real.logb 2 K := by
  have hL : 0 < Real.log (1 / e) := Real.log_pos ((one_lt_div₀ he).mpr (by linarith))
  have h' : c * (2 : ℝ) ^ (2 * n) * Real.sqrt (Real.log (1 / e)) ≤ K := by
    rw [pow_mul']
    push_cast at h
    exact h
  have hq := qubit_lower_of_resource hc hL (2 * n) h'
  push_cast at hq
  exact hq

/-- The qubit form at `d = 2ⁿ`. -/
theorem exists_strongUniversalQubitBound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalQubitBound b := by
  obtain ⟨c, hc, hres⟩ := exists_strongUniversalResourceBound_of_imageVolumeBound hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, ?_⟩
  intro n K hn _ e he he2
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  obtain ⟨hp, hm⟩ := hres (2 ^ n) K hd e he he2
  exact ⟨fun hu => strong_qubit_of_resource hc he he2 n (hp hu),
    fun hu => strong_qubit_of_resource hc he he2 n (hm hu)⟩

/-- The qubit form for universal normalized diamond implementation. -/
theorem exists_strongUniversalDiamondQubitBound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} b := by
  obtain ⟨b, hb, h⟩ := exists_strongUniversalQubitBound_of_imageVolumeBound hGeom
  refine ⟨b, hb, ?_⟩
  intro n K hn hK e he he2
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨hp, hm⟩ := h n K hn hK e he he2
  exact ⟨fun h' => hp h'.score, fun h' => hm h'.score⟩

end NLQCLean
