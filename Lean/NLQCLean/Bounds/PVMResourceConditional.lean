import NLQCLean.Bounds.PVMResourceArithmetic
import NLQCLean.Bounds.PVMTVHaarConditional
import NLQCLean.Approx.PVMRankFloor
import NLQCLean.Models.PVMUniversalReachability

/-!
# Conditional universal PVM footprint and qubit lower bounds

Universality quantifies every basis lift
and allows target-dependent protocols with arbitrary finite architectures;
support compression covers arbitrary original registers in the score-reachable sets.
The product-basis floor discharges K≥D/4, so it is not a hypothesis.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- Universality at the product basis gives the unconditional floor D/4≤K. -/
theorem PurePVMUniversalScore.quarter_floor {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 2) (h : PurePVMUniversalScore d K e) :
    (d : ℝ) ^ 2 / 4 ≤ K := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨s, P, hP, hscore⟩ := h 1
  have h1 : ((1 : Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = 1 := rfl
  rw [h1] at hscore
  have hf := P.quarter_card_le_of_identityPVM_score hP ⟨he0, by linarith⟩ he hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hf

theorem MixedPVMUniversalScore.quarter_floor {d K : ℕ} {e : ℝ} (hd : 0 < d)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 2) (h : MixedPVMUniversalScore d K e) :
    (d : ℝ) ^ 2 / 4 ≤ K :=
  ((mixedPVMUniversalScore_iff_pure d K e).mp h).quarter_floor hd he0 he

/-- PVM resource bound: one positive constant for score and joint-TV universality, pure and finite mixed.
No footprint floor or K≥1 hypothesis is assumed; the geometric property is explicit. -/
theorem exists_pvm_universal_resource_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalScore d K e → c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨C, hC, hHaar⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  have hC0 : 0 < C := by linarith
  refine ⟨Real.sqrt (3 / (32 * C)), by positivity, ?_⟩
  intro d K hd e he he'
  have hpure (hu : PurePVMUniversalScore d K e) :
      Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have hquarter := hu.quarter_floor (by omega) he.le he'
    have hK : 1 ≤ K := by
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hK1 : (1 : ℝ) ≤ K := by nlinarith
      exact_mod_cast hK1
    have hm := (hHaar d K hd hK hquarter e he he').2.2.1
    rw [hu.reachable_eq_univ, unitaryHaar_univ] at hm
    have hone : 1 ≤ Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((pvmCodimension d : ℝ) / 2) :=
      ENNReal.one_le_ofReal.mp (hm.trans (min_le_right _ _))
    exact pvm_resource_lower_of_one_le_haar_rhs hd hC0 he (by linarith) hone
  have hmixed (hu : MixedPVMUniversalScore d K e) :=
    hpure ((mixedPVMUniversalScore_iff_pure d K e).mp hu)
  exact ⟨hpure, hmixed, fun hu => hpure (hu.score (by omega)),
    fun hu => hmixed (hu.score (by omega))⟩

/-- PVM qubit bound: for d=2ⁿ, one nonnegative additive constant with real base-two logarithms. -/
theorem exists_pvm_universal_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨c, hc, hresource⟩ :=
    exists_pvm_universal_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, ?_⟩
  intro n K hn e he he'
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hL : 0 < Real.log (1 / e) := Real.log_pos ((one_lt_div₀ he).mpr (by linarith))
  obtain ⟨hp, hm, htp, htm⟩ := hresource (2 ^ n) K hd e he he'
  have hq {X : Prop} (hX : X → c * ((2 ^ n : ℕ) : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K)
      (hu : X) :
      (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - max 0 (-Real.logb 2 c) ≤
        Real.logb 2 (K : ℝ) := by
    have h := hX hu
    push_cast at h
    exact qubit_lower_of_resource hc hL n h
  exact ⟨hq hp, hq hm, hq htp, hq htm⟩

end NLQCLean
