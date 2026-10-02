/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Multiplicity form of the change-of-variables inequality

If a strictly differentiable self-map of a finite-dimensional real space has invertible
derivative on a measurable set `s`, and no fiber of `f` contains more than `N` points
of `s`, then the integral of the absolute Jacobian over `s` is at most `N` times the
measure of `f '' s`. The set `s` is covered by countably many open sets on which the
inverse function theorem makes `f` injective, and Mathlib's injective change of
variables applies on each piece.
-/

namespace NLQCLean

open MeasureTheory Set Filter
open scoped ENNReal Topology Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem ContinuousLinearMap.injective_of_det_ne_zero {A : E →L[ℝ] E} (hA : A.det ≠ 0) :
    Function.Injective A := by
  have hu : IsUnit (A : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA)
  exact ((Module.End.isUnit_iff _).mp hu).1

/-- An invertible continuous linear endomorphism as a continuous linear equivalence. -/
noncomputable def equivOfDetNeZero (A : E →L[ℝ] E) (hA : A.det ≠ 0) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E)
    (ContinuousLinearMap.injective_of_det_ne_zero hA)).toContinuousLinearEquiv

theorem coe_equivOfDetNeZero (A : E →L[ℝ] E) (hA : A.det ≠ 0) :
    (equivOfDetNeZero A hA : E →L[ℝ] E) = A := by
  ext x
  rfl

/-- Near a point with invertible strict derivative there is an open set on which `f` is
injective. -/
theorem exists_isOpen_injOn_of_hasStrictFDerivAt {f : E → E} {A : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.det ≠ 0) :
    ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ InjOn f O := by
  have hf' : HasStrictFDerivAt f (equivOfDetNeZero A hA : E →L[ℝ] E) x := by
    rwa [coe_equivOfDetNeZero]
  exact ⟨(hf'.toOpenPartialHomeomorph f).source, (hf'.toOpenPartialHomeomorph f).open_source,
    hf'.mem_toOpenPartialHomeomorph_source, (hf'.toOpenPartialHomeomorph f).injOn⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Banach indicatrix inequality.** -/
theorem lintegral_abs_det_le_mul_addHaar_image {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E} (hf' : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) (N : ℕ)
    (hN : ∀ (y : E) (T : Finset E), (∀ x ∈ T, x ∈ s ∧ f x = y) → T.card ≤ N) :
    ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ ≤ N * μ (f '' s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  have hloc : ∀ x ∈ s, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ InjOn f O := fun x hx =>
    exists_isOpen_injOn_of_hasStrictFDerivAt (hf' x hx) (hdet x hx)
  choose! O hOopen hxO hOinj using hloc
  obtain ⟨t, hts, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := s) (f := O) fun x hx => mem_nhdsWithin_of_mem_nhds ((hOopen x hx).mem_nhds (hxO x hx))
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hsne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := htc.exists_eq_range htne
  have hgs : ∀ n, g n ∈ s := fun n => hts (mem_range_self n)
  let P : ℕ → Set E := fun n => s ∩ disjointed (fun n => O (g n)) n
  have hPmeas : ∀ n, MeasurableSet (P n) := fun n =>
    hs.inter (MeasurableSet.disjointed (fun k => (hOopen _ (hgs k)).measurableSet) n)
  have hPdisj : Pairwise (Disjoint on P) := fun i j hij =>
    (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right
  have hPsub : ∀ n, P n ⊆ O (g n) := fun n => inter_subset_right.trans (disjointed_subset _ _)
  have hPinj : ∀ n, InjOn f (P n) := fun n => (hOinj _ (hgs n)).mono (hPsub n)
  have hPs : ∀ n, P n ⊆ s := fun n => inter_subset_left
  have hUnion : s = ⋃ n, P n := by
    show s = ⋃ n, s ∩ disjointed (fun n => O (g n)) n
    rw [← inter_iUnion, iUnion_disjointed]
    refine (inter_eq_left.mpr ?_).symm
    intro x hx
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨n, hy⟩
  have hPderiv : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPs n hx)).hasFDerivAt.hasFDerivWithinAt
  have hImeas : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPmeas n) (hPderiv n) (hPinj n)
  calc ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ
      = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| ∂μ := by
        conv_lhs => rw [hUnion]
        exact lintegral_iUnion hPmeas hPdisj _
    _ = ∑' n, μ (f '' P n) := by
        congr 1
        funext n
        exact lintegral_abs_det_fderiv_eq_addHaar_image μ (hPmeas n) (hPderiv n) (hPinj n)
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator 1 y ∂μ := by
        congr 1
        funext n
        rw [lintegral_indicator_one (hImeas n)]
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator 1 y ∂μ := by
        rw [lintegral_tsum fun n => (measurable_one.indicator (hImeas n)).aemeasurable]
    _ ≤ ∫⁻ y, (N : ℝ≥0∞) * (f '' s).indicator 1 y ∂μ := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ f '' s
        · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
          refine ENNReal.tsum_le_of_sum_range_le fun k => ?_
          let I := (Finset.range k).filter fun n => y ∈ f '' P n
          have hsum : ∑ n ∈ Finset.range k, (f '' P n).indicator (1 : E → ℝ≥0∞) y =
              (I.card : ℝ≥0∞) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            by_cases hn : y ∈ f '' P n <;> simp [hn]
          rw [hsum]
          have hpre : ∀ n ∈ I, ∃ x ∈ P n, f x = y := fun n hn =>
            (Finset.mem_filter.mp hn).2
          choose! x hxP hxy using hpre
          have hxinj : InjOn x I := by
            intro i hi j hj hij
            by_contra hne
            exact disjoint_left.mp (hPdisj hne) (hxP i hi) (hij ▸ hxP j hj)
          have hcard : (I.image x).card ≤ N := hN y _ fun z hz => by
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
            exact ⟨hPs n (hxP n hn), hxy n hn⟩
          rw [Finset.card_image_of_injOn hxinj] at hcard
          exact_mod_cast hcard
        · rw [indicator_of_notMem hy, mul_zero]
          refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun n => ?_)
          exact indicator_of_notMem (fun h => hy (image_mono (hPs n) h)) _
    _ = N * μ (f '' s) := by
        rw [lintegral_const_mul _ (measurable_one.indicator ?_), lintegral_indicator_one ?_]
        all_goals
          rw [hUnion, image_iUnion]
          exact MeasurableSet.iUnion hImeas

end NLQCLean
