/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.FormatParameters
import NLQCLean.Geometry.PolynomialZeroMeasure

/-!
# Local stability of convergent normalized polynomial descriptions

Away from the zero sets of nonzero limiting polynomials,
membership eventually agrees on a whole neighborhood. Zero coefficient
limits are eventually exactly zero because the norms lie in {0,1}.
-/

section

open Filter MeasureTheory
open scoped Topology

namespace NLQCLean

theorem PolynomialSign.eventually_same {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ u in 𝓝 t, ∀ s : PolynomialSign, s.Holds u ↔ s.Holds t := by
  rcases lt_or_gt_of_ne ht with h | h
  · filter_upwards [eventually_lt_nhds h] with u hu s
    cases s <;> simp only [Holds] <;> constructor <;> intro hs <;> linarith
  · filter_upwards [eventually_gt_nhds h] with u hu s
    cases s <;> simp only [Holds] <;> constructor <;> intro hs <;> linarith

theorem PolynomialCoefficients.eventually_eq_zero_of_normalized {n D : ℕ}
    {a : ℕ → PolynomialCoefficients n D} (ha : ∀ j, a j = 0 ∨ ‖a j‖ = 1)
    (hlim : Tendsto a atTop (𝓝 0)) : ∀ᶠ j in atTop, a j = 0 := by
  have hnorm : Tendsto (fun j => ‖a j‖) atTop (𝓝 (0 : ℝ)) := by simpa using hlim.norm
  filter_upwards [hnorm.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
  rcases ha j with h | h
  · exact h
  · linarith

theorem PolynomialCoefficients.exists_local_sign_stability {n D : ℕ}
    {a : ℕ → PolynomialCoefficients n D} {aLimit : PolynomialCoefficients n D}
    (ha : ∀ j, a j = 0 ∨ ‖a j‖ = 1) (hlim : Tendsto a atTop (𝓝 aLimit))
    (x : RealEuclidean n) (hx : aLimit = 0 ∨ aLimit.evaluate x ≠ 0) :
    ∃ V ∈ 𝓝 x, ∀ᶠ j in atTop, ∀ y ∈ V, ∀ s : PolynomialSign,
      s.Holds ((a j).evaluate y) ↔ s.Holds (aLimit.evaluate x) := by
  rcases hx with rfl | hx
  · refine ⟨Set.univ, univ_mem, ?_⟩
    filter_upwards [eventually_eq_zero_of_normalized ha hlim] with j hj
    intro y _ s
    simp [hj, evaluate]
  · have hcont : Tendsto (fun z : PolynomialCoefficients n D × RealEuclidean n =>
        z.1.evaluate z.2) (𝓝 (aLimit, x)) (𝓝 (aLimit.evaluate x)) :=
      (continuous_evaluate (n := n) (D := D)).tendsto (aLimit, x)
    have he : ∀ᶠ z : PolynomialCoefficients n D × RealEuclidean n in 𝓝 (aLimit, x),
        ∀ s : PolynomialSign, s.Holds (z.1.evaluate z.2) ↔ s.Holds (aLimit.evaluate x) :=
      hcont.eventually (PolynomialSign.eventually_same hx)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp he
    refine ⟨V, hV, ?_⟩
    filter_upwards [hlim.eventually hU] with j hj
    intro y hy
    exact @hUV (a j, y) ⟨hj, hy⟩

/-- Almost every point avoids every nonzero limiting coefficient polynomial.
Zero vectors are allowed and do not contribute exceptional zero sets. -/
theorem ae_format_coefficients_zero_or_eval_ne_zero {n D r b : ℕ}
    (a : PolynomialFormatCoefficients n D r b) :
    ∀ᵐ x : RealEuclidean n, ∀ i j, a i j = 0 ∨ (a i j).evaluate x ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hz : a i j = 0
  · exact Eventually.of_forall (fun _ => Or.inl hz)
  · have hp : (a i j).polynomial ≠ 0 := by simpa using hz
    have he : ∀ᵐ x : RealEuclidean n, (a i j).evaluate x ≠ 0 := by
      simpa only [ae_iff, not_not, PolynomialCoefficients.evaluate] using
        mvPolynomial_zeroSet_volume_eq_zero (a i j).polynomial hp
    exact he.mono (fun _ h => Or.inr h)

/-- Local, almost-everywhere membership stability of a fixed template. The
limit truth value is evaluated at x; every point in one neighborhood shares
that truth value for all sufficiently large sequence indices. -/
theorem PolynomialFormatTemplate.ae_local_source_stability {n D r b : ℕ}
    (T : PolynomialFormatTemplate r b) {a : ℕ → PolynomialFormatCoefficients n D r b}
    {aLimit : PolynomialFormatCoefficients n D r b}
    (ha : ∀ k, NormalizedFormatCoefficients (a k)) (hlim : Tendsto a atTop (𝓝 aLimit)) :
    ∀ᵐ x : RealEuclidean n, ∃ V ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ V,
      (y ∈ T.source (a k) ↔ x ∈ T.source aLimit) := by
  filter_upwards [ae_format_coefficients_zero_or_eval_ne_zero aLimit] with x hx
  have hslot (i : Fin r) (j : Fin b) :=
    PolynomialCoefficients.exists_local_sign_stability (fun k => ha k i j)
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i)) j) x (hx i j)
  choose V hV hstable using hslot
  refine ⟨⋂ i, ⋂ j, V i j, ?_, ?_⟩
  · exact Filter.iInter_mem.mpr (fun i => Filter.iInter_mem.mpr (hV i))
  · have hall : ∀ᶠ k in atTop, ∀ i j, ∀ y ∈ V i j, ∀ s : PolynomialSign,
        s.Holds ((a k i j).evaluate y) ↔ s.Holds ((aLimit i j).evaluate x) :=
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hstable i))
    filter_upwards [hall] with k hk
    intro y hy
    have hs (i : Fin r) (j : Fin b) (s : PolynomialSign) :=
      hk i j y (Set.mem_iInter.mp (Set.mem_iInter.mp hy i) j) s
    simp only [source, Set.mem_ofPred_eq, hs]

end NLQCLean
end
