import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arithmetic and first Borel–Cantelli helpers for almost-every targets

Nothing here mentions a quantum model or a geometric input. The forbidden
error sequence is `exp (-(A K² / d²))`; the Haar estimate is applied only for
`K ≥ d²`, the finite initial segment being absorbed by first Borel–Cantelli.
-/

namespace NLQCLean

open MeasureTheory Filter
open scoped ENNReal

/-- AF1: at the forbidden error, the Haar right side is at most `exp (-d² K²)`,
whenever `A ≥ (32/3)(C+1)` and the exponent is at least `3d⁴/32`. -/
theorem haar_rhs_at_forbiddenError_le {C A : ℝ} (hC : 0 ≤ C) (hA : 32 / 3 * (C + 1) ≤ A)
    {d K k : ℕ} (hd : 2 ≤ d) (hk : (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ (k : ℝ) / 2) :
    Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) ^ ((k : ℝ) / 2) ≤
      Real.exp (-((d : ℝ) ^ 2 * (K : ℝ) ^ 2)) := by
  rw [← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  have hdne : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact this.ne'
  have hA0 : 0 ≤ A := by linarith
  have ha0 : 0 ≤ A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hk ha0
  have h2 : A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2 * ((3 / 32 : ℝ) * (d : ℝ) ^ 4) =
      (3 / 32 * A) * ((d : ℝ) ^ 2 * (K : ℝ) ^ 2) := by
    field_simp
  have hDK : 0 ≤ (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by positivity
  have h3 : (C + 1) * ((d : ℝ) ^ 2 * (K : ℝ) ^ 2) ≤
      (3 / 32 * A) * ((d : ℝ) ^ 2 * (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hDK
  nlinarith

/-- For a positive integer budget, `exp (-d² K²) ≤ exp (-K)`. -/
theorem exp_neg_sq_mul_le_exp_neg {d K : ℕ} (hd : 1 ≤ d) :
    Real.exp (-((d : ℝ) ^ 2 * (K : ℝ) ^ 2)) ≤ Real.exp (-(K : ℝ)) := by
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hd)
  have hK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos K with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ K := by exact_mod_cast h
      nlinarith
  nlinarith [sq_nonneg (K : ℝ)]

/-- `exp (-t) ≤ 1/2` once `t ≥ 1`. -/
theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) : Real.exp (-t) ≤ 1 / 2 := by
  have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1 : ℝ)]

/-- Beyond `K ≥ d²` the forbidden-error exponent is at least one, for `A ≥ 1`. -/
theorem one_le_forbidden_exponent {A : ℝ} (hA : 1 ≤ A) {d K : ℕ} (hd : 1 ≤ d)
    (hK : d ^ 2 ≤ K) : 1 ≤ A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hd2]
  have hKR : (d : ℝ) ^ 2 ≤ K := by exact_mod_cast hK
  have hd1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hd)
  have hK1 : (1 : ℝ) ≤ K := hd1.trans hKR
  have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The side conditions of the full-group Haar estimate hold at the forbidden
error for every `K ≥ d²`, for `A ≥ 1`. -/
theorem forbiddenError_side_conditions {A : ℝ} (hA : 1 ≤ A) {d K : ℕ} (hd : 2 ≤ d)
    (hK : d ^ 2 ≤ K) :
    1 ≤ K ∧ (d : ℝ) ^ 2 / 4 ≤ K ∧ 0 < Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2)) ∧
      Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2)) ≤ 1 / 2 := by
  have hd4 : 4 ≤ d ^ 2 := by nlinarith
  have hKR : (d : ℝ) ^ 2 ≤ K := by exact_mod_cast hK
  refine ⟨by omega, by nlinarith [sq_nonneg (d : ℝ)], Real.exp_pos _, ?_⟩
  exact exp_neg_le_half (one_le_forbidden_exponent hA (by omega) hK)

/-- AF1 for a generic family of target sets: a Haar estimate of the existing
shape, on its own side conditions, bounds the forbidden sets by `exp (-K)`
for every `K ≥ d²`. -/
theorem measure_at_forbiddenError_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → ℝ → Set α} {C A : ℝ} (hC : 0 ≤ C) (hA : 32 / 3 * (C + 1) ≤ A)
    {d k : ℕ} (hd : 2 ≤ d) (hk : (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ (k : ℝ) / 2)
    (hbound : ∀ K : ℕ, 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      μ (s K e) ≤ min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((k : ℝ) / 2))))
    (K : ℕ) (hK : d ^ 2 ≤ K) :
    μ (s K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2)))) ≤
      ENNReal.ofReal (Real.exp (-(K : ℝ))) := by
  have hA1 : 1 ≤ A := by linarith
  obtain ⟨hK1, hq, hpos, hhalf⟩ := forbiddenError_side_conditions hA1 hd hK
  refine (hbound K hK1 hq _ hpos hhalf).trans ((min_le_right _ _).trans ?_)
  exact ENNReal.ofReal_le_ofReal ((haar_rhs_at_forbiddenError_le hC hA hd hk).trans
    (exp_neg_sq_mul_le_exp_neg (by omega)))

/-- The exponential tail is summable. -/
theorem summable_exp_neg_natCast : Summable (fun n : ℕ => Real.exp (-(n : ℝ))) := by
  have h := summable_geometric_of_lt_one (Real.exp_pos (-1 : ℝ)).le
    (Real.exp_lt_one_iff.mpr (by norm_num))
  refine h.congr fun n => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- AF1, first Borel–Cantelli only: exponentially small measures beyond a finite
initial segment make almost every point eventually avoid the sets. No
measurability and no independence are used. -/
theorem ae_exists_forall_notMem_of_le_exp_neg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : ℕ → Set α) (K₁ : ℕ)
    (hs : ∀ K : ℕ, K₁ ≤ K → μ (s K) ≤ ENNReal.ofReal (Real.exp (-(K : ℝ)))) :
    ∀ᵐ x ∂μ, ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → x ∉ s K := by
  have htail : (∑' n : ℕ, μ (s (n + K₁))) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, Real.exp (-(n : ℝ)))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) summable_exp_neg_natCast]
    refine ENNReal.tsum_le_tsum fun n => (hs (n + K₁) (Nat.le_add_left _ _)).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    push_cast
    linarith [(Nat.cast_nonneg K₁ : (0 : ℝ) ≤ K₁)]
  refine (ae_eventually_notMem htail).mono fun x hx => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hx
  refine ⟨N + K₁ + 1, by omega, fun K hK => ?_⟩
  have h := hN (K - K₁) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at h

/-- AF1 assembled for a generic family: almost every point eventually avoids the
forbidden error sequence. -/
theorem ae_forbiddenError_of_haar_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → ℝ → Set α} {C A : ℝ} (hC : 0 ≤ C) (hA : 32 / 3 * (C + 1) ≤ A)
    {d k : ℕ} (hd : 2 ≤ d) (hk : (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ (k : ℝ) / 2)
    (hbound : ∀ K : ℕ, 1 ≤ K → (d : ℝ) ^ 2 / 4 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      μ (s K e) ≤ min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
        e ^ ((k : ℝ) / 2)))) :
    ∀ᵐ x ∂μ, ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      x ∉ s K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))) :=
  ae_exists_forall_notMem_of_le_exp_neg μ _ (d ^ 2)
    (measure_at_forbiddenError_le hC hA hd hk hbound)

/-- AF2, deterministic: for a family increasing in budget and error, avoiding the
forbidden sequence from `K₀` on yields the resource bound at every budget and every
error below `e_{K₀}`, with `c = 1/√A`. -/
theorem resource_lower_of_forbiddenError {α : Type*} {R : ℕ → ℝ → Set α}
    (hmono : ∀ {K K' : ℕ} {e e' : ℝ}, K ≤ K' → e ≤ e' → R K e ⊆ R K' e')
    {A : ℝ} (hA : 0 < A) {d : ℕ} (hd : 0 < d) {x : α} {K₀ : ℕ}
    (hforb : ∀ K : ℕ, K₀ ≤ K → x ∉ R K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2))))
    {K : ℕ} {e : ℝ} (he₀ : e ≤ Real.exp (-(A * (K₀ : ℝ) ^ 2 / (d : ℝ) ^ 2)))
    (hx : x ∈ R K e) :
    1 / Real.sqrt A * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K := by
  rcases lt_or_ge K K₀ with hK | hK
  · exact absurd (hmono hK.le he₀ hx) (hforb K₀ le_rfl)
  · have hlt : Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2)) < e := by
      by_contra h
      exact hforb K hK (hmono le_rfl (not_lt.mp h) hx)
    have he : 0 < e := (Real.exp_pos _).trans hlt
    have hlog : Real.log (1 / e) < A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
      have h := Real.log_lt_log (Real.exp_pos _) hlt
      rw [Real.log_exp] at h
      rw [one_div, Real.log_inv]
      linarith
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hsq : Real.sqrt (Real.log (1 / e)) ≤ Real.sqrt A * K / d := by
      have heq : Real.sqrt A * K / d = Real.sqrt (A * (K : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul hA.le,
          Real.sqrt_sq (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
      rw [heq]
      exact Real.sqrt_le_sqrt hlog.le
    calc
      1 / Real.sqrt A * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤
          1 / Real.sqrt A * (d : ℝ) * (Real.sqrt A * K / d) := by gcongr
      _ = K := by field_simp

/-- AF2 threshold: enlarging `K₀` to at least `d²` puts `e_{K₀}` in `(0, 1/2]`. -/
theorem forbiddenError_threshold_mem {A : ℝ} (hA : 1 ≤ A) {d K₀ : ℕ} (hd : 1 ≤ d)
    (hK₀ : d ^ 2 ≤ K₀) :
    0 < Real.exp (-(A * (K₀ : ℝ) ^ 2 / (d : ℝ) ^ 2)) ∧
      Real.exp (-(A * (K₀ : ℝ) ^ 2 / (d : ℝ) ^ 2)) ≤ 1 / 2 :=
  ⟨Real.exp_pos _, exp_neg_le_half (one_le_forbidden_exponent hA hd hK₀)⟩

end NLQCLean
